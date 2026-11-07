/* Trusted FEval injection, NOT source checking or erased S/R type evidence.
   Real transport allocations back the immutable slice. No runtime limits change. */
#include <assert.h>
#include <stdlib.h>
static size_t live_allocations, allocations, releases;
static void *tracked_malloc(size_t size) {
  void *p = malloc(size);
  if (p) { live_allocations++; allocations++; }
  return p;
}
static void tracked_free(void *p) {
  if (p) { assert(live_allocations); live_allocations--; releases++; }
  free(p);
}
#define malloc tracked_malloc
#define free tracked_free
#include "fibril_binary_runtime.c"
#undef malloc
#undef free

static const unsigned char input[] = {126,0,255,195,40,128,254,127,97,98,99,100};
static const unsigned char saved[] = {0,255,195,40,128};
static size_t position, accepted, flushes, read_requests, write_requests, calls;
static int mode;
static FValue *initial_chunk, *current_state;
static const unsigned char *borrowed;

static FValue *one(FRuntime *r,FEnv *e) { (void)e; return byte_natural(r,1); }
static FValue *five(FRuntime *r,FEnv *e) { (void)e; return byte_natural(r,5); }
static FValue *eight(FRuntime *r,FEnv *e) { (void)e; return byte_natural(r,8); }
static FValue *capacity(FRuntime *r,FEnv *e) {
  (void)e; return byte_natural(r, mode == 5 && calls == 3 ? 2 : 1);
}
static FValue *limit(FRuntime *r,FEnv *e) {
  (void)e; return byte_natural(r, mode == 1 || mode == 4 ? 2 : 32);
}
static FValue *chunk_value(FRuntime *r,FEnv *e) { (void)r; (void)e; return initial_chunk; }
static FValue *state_value(FRuntime *r,FEnv *e) { (void)r; (void)e; return current_state; }
static FValue *pure_value(FRuntime *r,FValue *value) {
  FValue *io = new_value(r,V_PURE);
  if (io) io->as.io.first = ready(r,value);
  return io && io->as.io.first ? io : NULL;
}
static FValue *variant(FRuntime *r,size_t tag,FValue *payload) {
  FValue *v = new_value(r,V_VARIANT);
  if (v) { v->as.variant.tag = tag; v->as.variant.payload = ready(r,payload); }
  return v && v->as.variant.payload ? v : NULL;
}
static FValue *nominal(FRuntime *r,size_t tag,FValue *payload) {
  FValue *v = new_value(r,V_NOMINAL);
  if (v) v->as.nominal = ready(r,variant(r,tag,payload));
  return v && v->as.nominal ? v : NULL;
}
static FValue *unwrap(FRuntime *r,FValue *value,size_t tag) {
  assert(value && value->tag == V_NOMINAL);
  FValue *v = force(r,value->as.nominal);
  assert(v && v->tag == V_VARIANT && v->as.variant.tag == tag && v->as.variant.payload);
  return force(r,v->as.variant.payload);
}
static FValue *fragment_bytes(FRuntime *r,FValue *fragment) {
  FValue *bytes = unwrap(r,fragment,1); /* Fragment.View */
  assert(bytes && bytes->tag == V_BYTES && bytes->as.bytes.length == sizeof(saved));
  assert(bytes->as.bytes.data == borrowed);
  assert(!memcmp(bytes->as.bytes.data,saved,sizeof(saved)));
  return bytes;
}
static FValue *state_fragment(FRuntime *r,FValue *state,size_t phase) {
  FValue *fragment = unwrap(r,state,phase); /* Begin0/Middle1/End2 */
  (void)fragment_bytes(r,fragment);
  return fragment;
}
static FValue *after_read(FRuntime *r,FEnv *e) {
  FValue *read = force(r,e->value);
  assert(read && read->tag == V_VARIANT && read->as.variant.tag == 1);
  FValue *bytes = force(r,read->as.variant.payload);
  assert(bytes && bytes->tag == V_BYTES && bytes->as.bytes.length == 1);
  assert(bytes->as.bytes.data[0] == input[7 + calls]);
  FValue *state = force(r,e->tail->value);
  FValue *fragment = state_fragment(r,state,calls - 1);
  if (mode == 2 && calls == 3) return f_reject_bytes(r);
  if (calls < 3) return pure_value(r,variant(r,1,nominal(r,calls,fragment)));
  /* Done carries a DIFFERENT shape: Reply.Answer0, not Phase.End2. */
  return pure_value(r,variant(r,0,nominal(r,0,fragment)));
}
static FValue *read_next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,after_read); }
static FValue *read_action(FRuntime *r,FEnv *e) {
  read_requests++; return f_read_bytes(r,e,capacity);
}
static FValue *read_step(FRuntime *r,FEnv *e) { return f_bind(r,e,read_action,read_next); }
static FValue *after_flush(FRuntime *r,FEnv *e) {
  /* Explicit flush's Unit is consumed by this trusted fixture. Restore state. */
  assert(force(r,e->value)->tag == V_UNIT);
  return read_step(r,e->tail);
}
static FValue *flush_next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,after_flush); }
static FValue *flush_action(FRuntime *r,FEnv *e) { (void)e; return f_flush_bytes(r); }
static FValue *after_marker(FRuntime *r,FEnv *e) {
  assert(force(r,e->value)->tag == V_UNIT);
  return f_bind(r,e->tail,flush_action,flush_next);
}
static FValue *marker_next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,after_marker); }
static FValue *marker(FRuntime *r,FEnv *e) {
  (void)e; static const unsigned char mark[] = {'!'}; return f_bytes_literal(r,mark,1);
}
static FValue *write_marker(FRuntime *r,FEnv *e) {
  write_requests++; return f_write_bytes(r,e,marker);
}
static FValue *step_body(FRuntime *r,FEnv *e) {
  calls++;
  assert(calls <= 3);
  (void)state_fragment(r,force(r,e->value),calls - 1);
  return calls == 1 ? f_bind(r,e,write_marker,marker_next) : read_step(r,e);
}
static FValue *step(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,step_body); }
static FValue *loop(FRuntime *r,FEnv *e) { return f_iterate_binary(r,e,limit,step,state_value); }
static FValue *read_initial(FRuntime *r,FEnv *e) {
  read_requests++; return f_read_bytes(r,e,eight);
}
static FValue *write_view(FRuntime *r,FEnv *e) {
  write_requests++; return f_write_bytes(r,e,chunk_value);
}
static int host_read(void *opaque) {
  (void)opaque;
  if (mode == 5 && position == 11) return -2;
  assert(position < sizeof(input));
  return input[position++];
}
static int host_write(void *opaque,unsigned char byte) {
  (void)opaque;
  if (mode == 6 && accepted == 3) return -1;
  assert(accepted <= sizeof(saved));
  assert(byte == (accepted ? saved[accepted - 1] : '!'));
  accepted++; return 0;
}
static int host_flush(void *opaque) {
  (void)opaque; flushes++;
  return (mode == 7 && flushes == 2) || mode == 8 ? -1 : 0;
}
static void check_poison(FByteSession *session) {
  size_t p = position, a = accepted, f = flushes;
  size_t prefix = 999;
  assert(fibril_bytes_read(session,1).status == FB_POISONED);
  assert(fibril_bytes_write(session,saved,1,&prefix) == FB_POISONED && prefix == 0);
  assert(fibril_bytes_flush(session) == FB_POISONED);
  assert(position == p && accepted == a && flushes == f);
}
static FByteStatus body(FByteSession *session,void *opaque) {
  FBinaryContext *context = opaque; FRuntime *r = context->runtime;
  FThunk *first = interact_binary(context,session,evaluate(r,read_initial,NULL));
  assert(first);
  FValue *response = force(r,first);
  assert(response && response->tag == V_VARIANT && response->as.variant.tag == 1);
  initial_chunk = force(r,response->as.variant.payload);
  assert(initial_chunk && initial_chunk->tag == V_BYTES && initial_chunk->as.bytes.length == 8);
  assert(session->blocks && initial_chunk->as.bytes.data == session->blocks->data);
  assert(!memcmp(initial_chunk->as.bytes.data,input,8));
  borrowed = initial_chunk->as.bytes.data + 1; /* Session storage, not arena copy. */
  FValue *view = f_bytes_slice(r,NULL,one,five,chunk_value);
  current_state = nominal(r,0,nominal(r,1,view));
  FThunk *result = interact_binary(context,session,evaluate(r,loop,NULL));
  if (!result) {
    if (context->fault != FB_OK) { check_poison(session); return context->fault; }
    assert(mode == 2 && r->error); return FB_ADAPTER_VIOLATION;
  }
  FValue *outer = force(r,result);
  size_t exhausted = mode == 1 || mode == 4;
  assert(outer && outer->tag == V_VARIANT && outer->as.variant.tag == exhausted);
  FValue *payload = force(r,outer->as.variant.payload);
  FValue *fragment = exhausted ? state_fragment(r,payload,2) : unwrap(r,payload,0);
  initial_chunk = fragment_bytes(r,fragment); /* Transfer retained view to write. */
  FThunk *written = interact_binary(context,session,evaluate(r,write_view,NULL));
  if (!written) { assert(context->fault == FB_WRITE_FAILED); check_poison(session); return context->fault; }
  assert(force(r,written)->tag == V_UNIT);
  if (mode == 3 || mode == 4) {
    assert(!interact_binary(context,session,f_reject_bytes(r)));
    return FB_ADAPTER_VIOLATION;
  }
  return FB_OK;
}
int main(int argc,char **argv) {
  if (argc != 2) return 2;
  mode = atoi(argv[1]); assert(mode >= 0 && mode <= 8);
  FRuntime r = {0}; FBinaryContext context = {&r,loop,FB_OK,0,0};
  FByteStatus status = fibril_bytes_run_with(4096,8388608,
    (FByteAdapters){host_read,host_write,host_flush,NULL},body,&context);
  assert(r.depth == 0);
  assert(calls == (mode == 8 ? 1u : mode == 1 || mode == 4 ? 2u : 3u));
  assert(read_requests == (mode == 8 ? 1u : mode == 1 || mode == 4 ? 3u : 4u));
  assert(position == (mode == 8 ? 8u : mode == 1 || mode == 4 ? 10u : 11u));
  assert(write_requests == (mode == 2 || mode == 5 || mode == 8 ? 1u : 2u));
  assert(accepted == (mode == 2 || mode == 5 || mode == 8 ? 1u : mode == 6 ? 3u : 6u));
  assert(flushes == (mode == 0 || mode == 1 || mode == 7 ? 2u : 1u));
  assert(status == (mode <= 1 ? FB_OK : mode <= 4 ? FB_ADAPTER_VIOLATION :
    mode == 5 ? FB_READ_FAILED : mode == 6 ? FB_WRITE_FAILED : FB_FLUSH_FAILED));
  if (mode == 2 || mode == 3 || mode == 4) assert(r.error && strstr(r.error,"rejected input"));
  else assert(!r.error);
  if (mode == 5) assert(context.read_prefix == 1);
  if (mode == 6) assert(context.write_prefix == 2);
  /* Only arena metadata is inspected AFTER session payload teardown. */
  size_t arena_allocations = 0;
  for (FAllocation *a = r.allocations; a; a = a->next) arena_allocations++;
  assert(live_allocations == arena_allocations);
  while (r.allocations) {
    FAllocation *next = r.allocations->next;
    tracked_free(r.allocations); r.allocations = next;
  }
  assert(!live_allocations && allocations == releases);
  printf("VIEW_LIFETIME %d %zu %zu %zu %zu %zu %zu %zu %zu %zu\n", mode,
    calls, read_requests, position, write_requests, accepted, flushes,
    live_allocations, context.read_prefix, context.write_prefix);
  return 0;
}
