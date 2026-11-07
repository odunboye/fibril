/* Trusted FEval injection tests, NOT source typing/provenance evidence. */
#include "fibril_binary_runtime.c"
#include <assert.h>
static size_t calls, limit, bind_left, loop_left, reads, writes, flushes;
static int mode;
static FValue *shared_io;
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *bad(FRuntime *r, FEnv *e) { (void)e; fail(r,"demanded bad state"); return NULL; }
static FValue *initial(FRuntime *r, FEnv *e) { return mode == 2 ? bad(r,e) : unit(r,e); }
static FValue *count_value(FRuntime *r, FEnv *e) {
  (void)e;
  if (mode == 5) return f_unit(r);
  if (mode == 6) {
    FValue *cycle = new_value(r,V_NAT_SUCC);
    cycle->as.recursive.tail = ready(r,cycle); return cycle;
  }
  return byte_natural(r,limit);
}
static FValue *state(FRuntime *r, FEnv *e) { return f_variable(r,e,0); }
static FValue *response(FRuntime *r, FEnv *e) {
  if (mode == 7) return f_unit(r);
  if (mode == 8) return f_variant(r,e,2,state);
  if (mode == 9) return f_variant(r,e,0,NULL);
  return f_variant(r,e, mode == 0 || mode == 4 ? 0 : 1,
    mode == 3 || mode == 4 ? bad : state);
}
static FValue *body(FRuntime *,FEnv *);
static FValue *callback(FRuntime *r, FEnv *e) { return f_lambda(r,e,0,body); }
static FValue *loop(FRuntime *r, FEnv *e) { return f_iterate_binary(r,e,count_value,callback,initial); }
static FValue *body(FRuntime *r, FEnv *e) {
  calls++;
  if (mode == 10) {
    if (!shared_io) shared_io = f_pure(r,e,response);
    return shared_io;
  }
  if (mode == 11) return loop(r,e); /* nested frames, never pure recursion */
  if (mode == 12) { r->bytes = F_MAX_BYTES; return f_pure(r,e,response); }
  if (mode == 13) return evaluate(r,body,e); /* pure depth rejection */
  if (mode == 14 && loop_left--) return loop(r,e);
  return f_pure(r,e,response);
}
static FValue *unused(FRuntime *r, FEnv *e) { return f_pure(r,e,unit); }
static FValue *ignore(FRuntime *r, FEnv *e) { return f_lambda(r,e,0,unused); }
static FValue *entry(FRuntime *r, FEnv *e) {
  if (mode == 14 && bind_left--) return f_bind(r,e,entry,ignore);
  return loop(r,e);
}
static int no_read(void *p) { (void)p; reads++; return -1; }
static int no_write(void *p,unsigned char byte) { (void)p; (void)byte; writes++; return 0; }
static int no_flush(void *p) { (void)p; flushes++; return 0; }
static FByteStatus run(FByteSession *session,void *opaque) {
  FBinaryContext *context=opaque; FRuntime *r=context->runtime;
  FValue *io=evaluate(r,entry,NULL);
  FThunk *result=io?interact_binary(context,session,io):NULL;
  if (!result || r->error) return FB_ADAPTER_VIOLATION;
  FValue *value=force(r,result);
  assert(value && value->tag==V_VARIANT && value->as.variant.payload);
  assert(value->as.variant.tag==(mode==0 || mode==4 ? 0u : 1u));
  /* Do not force lazy Done or zero/exhausted state. */
  return FB_OK;
}
int main(int argc,char **argv) {
  if(argc!=2) return 2;
  mode=atoi(argv[1]); limit=mode==2?0:mode==0?1024:mode==1?1024:mode==10?20000:mode==3?2:1;
  if(mode==14) { bind_left=2048; loop_left=2049; }
  FRuntime r={0}; FBinaryContext context={&r,entry,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run_with(4096,8388608,
    (FByteAdapters){no_read,no_write,no_flush,NULL},run,&context);
  assert(!reads && !writes && r.depth==0);
  if(mode<=2 || mode==4) {
    assert(status==FB_OK && !r.error && flushes==1);
    assert(calls==(mode==2?0u:mode==1?1024u:1u));
  } else {
    assert(status!=FB_OK && r.error && !flushes);
    if(mode==3) assert(calls==1 && strstr(r.error,"bad state"));
    if(mode==5 || mode==6) assert(!calls);
    if(mode==6 || mode==10) assert(r.steps==F_MAX_STEPS);
    if(mode==7 || mode==8 || mode==9) assert(calls==1 && strstr(r.error,"Done/Continue"));
    if(mode==11 || mode==14) assert(strstr(r.error,"continuation budget"));
    if(mode==14) assert(calls==2048); /* shared limit, not 4096 per kind */
    if(mode==12) assert(strstr(r.error,"allocation budget"));
    if(mode==13) assert(strstr(r.error,"evaluation budget"));
  }
  while(r.allocations) { FAllocation *next=r.allocations->next; free(r.allocations); r.allocations=next; }
  return 0;
}
