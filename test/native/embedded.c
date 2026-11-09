/* Trusted C fixtures: runtime/arena behavior, not evidence of source typing. */
#include "fibril_embedded.h"
#include <assert.h>
#include <stdint.h>
#include <string.h>

static FEmbeddedCell cells[8192];
static unsigned char bytes[65536];
typedef struct { unsigned char text[256]; size_t length, writes, flushes; int fail_write, fail_flush, reenter, mutate; FNativeHost *table; FEmbeddedArena *arena; } Sink;
static FValue *entry(FRuntime *, FEnv *);
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *pure(FRuntime *r, FEnv *e) { return f_pure(r,e,unit); }
static int write_bytes(void *context, const unsigned char *data, size_t length) {
  Sink *s=context; s->writes++;
  if (s->fail_write && s->writes==(size_t)s->fail_write) return 1;
  assert(length<=sizeof(s->text)-s->length);
  memcpy(s->text+s->length,data,length);s->length+=length;
  if (s->mutate) { s->table->write=NULL; s->table->flush=NULL; }
  if (s->reenter==1) {
    FNativeResult nested=fibril_native_embed_arena(pure,s->table,s->arena);
    assert(nested.status==F_NATIVE_INVALID_ARGUMENT && s->arena->busy);
  } else if (s->reenter==2) {
    FEmbeddedCell nested_cells[64];
    FEmbeddedArena nested_arena={.cells=nested_cells,.cell_capacity=64};
    Sink inner={0}; FNativeHost host={&inner,write_bytes,s->table->flush};
    FNativeResult nested=fibril_native_embed_arena(entry,&host,&nested_arena);
    assert(nested.status==F_NATIVE_OK && inner.length==6 && inner.flushes==1);
  }
  return 0;
}
static int flush(void *context) { Sink *s=context;s->flushes++;return s->fail_flush; }
static FValue *text(FRuntime *r, FEnv *e) { (void)e;static const unsigned char x[]="hello";return f_literal(r,x,5); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r,e,text); }
static FValue *joined(FRuntime *r, FEnv *e) { return f_append(r,e,text,text); }
static FValue *dynamic(FRuntime *r, FEnv *e) { return f_write(r,e,joined); }
static FValue *nul(FRuntime *r, FEnv *e) { (void)e;static const unsigned char x[]={0};return f_literal(r,x,1); }
static FValue *bad_write(FRuntime *r, FEnv *e) { return f_write(r,e,nul); }
static FValue *bad_next(FRuntime *r, FEnv *e) { return f_lambda(r,e,0,bad_write); }
static FValue *late_nul(FRuntime *r, FEnv *e) { return f_bind(r,e,entry,bad_next); }
static FValue *bad_final(FRuntime *r, FEnv *e) { return f_pure(r,e,text); }
static FValue *bad_final_next(FRuntime *r, FEnv *e) { return f_lambda(r,e,0,bad_final); }
static FValue *late_final(FRuntime *r, FEnv *e) { return f_bind(r,e,entry,bad_final_next); }
static FValue *read_request(FRuntime *r, FEnv *e) { (void)e;return f_read_line(r); }
static FValue *depth(FRuntime *r, FEnv *e) { (void)e;return f_global(r,depth); }
static FValue *variable(FRuntime *r, FEnv *e) { return f_variable(r,e,0); }
static FValue *region_body_value(FRuntime *r, FEnv *e) { return f_append(r,e,text,text); }
static FValue *region_body(FRuntime *r, FEnv *e) { return f_lambda(r,e,1,region_body_value); }
static FValue *region_text(FRuntime *r, FEnv *e) { return f_with_region(r,e,region_body); }
static FValue *region_entry(FRuntime *r, FEnv *e) { return f_write(r,e,region_text); }
static FValue *lazy_body(FRuntime *r, FEnv *e) { (void)e;return f_literal(r,(const unsigned char *)"lazy",4); }
static FValue *lazy_function(FRuntime *r, FEnv *e) { return f_lambda(r,e,1,lazy_body); }
static FValue *lazy_text(FRuntime *r, FEnv *e) { return f_apply(r,e,lazy_function,variable); }
static FValue *lazy_entry(FRuntime *r, FEnv *e) { return f_write(r,e,lazy_text); }
static FEmbeddedArena arena(void) {
  FEmbeddedArena a={.cells=cells,.cell_capacity=8192,.bytes=bytes,.byte_capacity=sizeof(bytes)};return a;
}
static void unchanged_failure(FEval code, FEmbeddedArena *a, FNativeStatus status, const char *message) {
  Sink s={0};FNativeHost h={&s,write_bytes,flush};FNativeResult r=fibril_native_embed_arena(code,&h,a);
  assert(r.status==status && r.message && (!message || strstr(r.message,message)));
  assert(!s.writes && !s.flushes && !a->busy);
}
int main(void) {
  FEmbeddedArena a=arena();Sink s={0};FNativeHost h={&s,write_bytes,flush};FNativeResult r;
  assert(fibril_native_embed_arena(entry,&h,NULL).status==F_NATIVE_INVALID_ARGUMENT);
  unchanged_failure(NULL,&a,F_NATIVE_INVALID_ARGUMENT,NULL);
  assert(fibril_native_embed_arena(entry,NULL,&a).status==F_NATIVE_INVALID_ARGUMENT);
  assert(!a.busy);
  FNativeHost invalid={0};assert(fibril_native_embed_arena(entry,&invalid,&a).status==F_NATIVE_INVALID_ARGUMENT);
  FEmbeddedArena bad=a;bad.cells=NULL;unchanged_failure(entry,&bad,F_NATIVE_INVALID_ARGUMENT,NULL);
  bad=a;bad.bytes=NULL;unchanged_failure(entry,&bad,F_NATIVE_INVALID_ARGUMENT,NULL);
  bad=a;bad.cell_capacity=SIZE_MAX;unchanged_failure(entry,&bad,F_NATIVE_INVALID_ARGUMENT,NULL);
  bad=a;bad.byte_capacity=SIZE_MAX;unchanged_failure(entry,&bad,F_NATIVE_INVALID_ARGUMENT,NULL);
  bad=a;bad.byte_capacity=FIBRIL_EMBEDDED_MAX_BYTES;unchanged_failure(entry,&bad,F_NATIVE_INVALID_ARGUMENT,NULL);
  FEmbeddedArena empty={0};unchanged_failure(entry,&empty,F_NATIVE_PROGRAM_ERROR,"cell arena exhausted");
  a.cell_capacity=1;unchanged_failure(entry,&a,F_NATIVE_PROGRAM_ERROR,"cell arena exhausted");
  a=arena();a.bytes=NULL;a.byte_capacity=0;
  r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_OK && s.length==6 && a.bytes_used==0);
  size_t minimum=a.cells_used;assert(minimum>1);
  a.cell_capacity=minimum-1;unchanged_failure(entry,&a,F_NATIVE_PROGRAM_ERROR,"cell arena exhausted");
  a.cell_capacity=minimum;s=(Sink){0};r=fibril_native_embed_arena(entry,&h,&a);
  assert(r.status==F_NATIVE_OK && a.cells_used==minimum && s.flushes==1);
  a=arena();a.byte_capacity=0;unchanged_failure(dynamic,&a,F_NATIVE_PROGRAM_ERROR,"byte arena exhausted");
  a=arena();s=(Sink){0};r=fibril_native_embed_arena(dynamic,&h,&a);
  assert(r.status==F_NATIVE_OK && a.bytes_used==10 && s.length==11);
  a.byte_capacity=9;bytes[9]=0xa5;unchanged_failure(dynamic,&a,F_NATIVE_PROGRAM_ERROR,"byte arena exhausted");assert(bytes[9]==0xa5);
  a.byte_capacity=10;s=(Sink){0};r=fibril_native_embed_arena(dynamic,&h,&a);assert(r.status==F_NATIVE_OK && a.bytes_used==10);
  a=arena();unchanged_failure(late_nul,&a,F_NATIVE_PROGRAM_ERROR,"NUL");
  unchanged_failure(late_final,&a,F_NATIVE_PROGRAM_ERROR,"unit");
  unchanged_failure(read_request,&a,F_NATIVE_PROGRAM_ERROR,"non-IO");
  unchanged_failure(depth,&a,F_NATIVE_PROGRAM_ERROR,"evaluation budget");
  s=(Sink){.fail_write=1};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_WRITE_ERROR && s.writes==1 && !s.flushes && !a.busy);
  s=(Sink){.fail_write=2};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_WRITE_ERROR && s.length==5 && !s.flushes);
  s=(Sink){.fail_flush=1};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_FLUSH_ERROR && s.flushes==1);
  s=(Sink){.reenter=1,.table=&h,.arena=&a};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_OK && s.length==6 && !a.busy);
  s=(Sink){.reenter=2,.table=&h};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_OK && s.length==6);
  s=(Sink){.mutate=1,.table=&h};r=fibril_native_embed_arena(entry,&h,&a);assert(r.status==F_NATIVE_OK && s.flushes==1);
  h.write=write_bytes;h.flush=flush;
  s=(Sink){0};r=fibril_native_embed_arena(region_entry,&h,&a);assert(r.status==F_NATIVE_OK && a.bytes_used==20 && s.length==11);
  s=(Sink){0};r=fibril_native_embed_arena(lazy_entry,&h,&a);assert(r.status==F_NATIVE_OK && s.length==5);
  for(size_t i=0;i<128;i++) {
    assert((uintptr_t)&cells[i].value % _Alignof(FValue)==0);
    assert((uintptr_t)&cells[i].thunk % _Alignof(FThunk)==0);
    assert((uintptr_t)&cells[i].env % _Alignof(FEnv)==0);
    assert((uintptr_t)&cells[i].action % _Alignof(FAction)==0);
  }
  for(int i=0;i<1000;i++) {
    s=(Sink){0};r=fibril_native_embed_arena(dynamic,&h,&a);
    assert(r.status==F_NATIVE_OK && a.bytes_used==10 && !memcmp(s.text,"hellohello\n",11) && !a.busy);
  }
  return 0;
}
