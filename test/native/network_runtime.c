/* Trusted defensive runtime fixtures, deliberately bypass source checking. */
#include "fibril_network_runtime.c"
#include <assert.h>
#include <fcntl.h>
#include <string.h>

static int bad_result;
static FValue *listen_args(FRuntime *r, FEnv *e) {
  (void)e;
  return owned_pair(r, f_literal(r, (const unsigned char *)"127.0.0.1", 9),
    owned_pair(r, f_word(r, 0), owned_pair(r, f_word(r, 8), f_unit(r))));
}
static FValue *open_listener(FRuntime *r, FEnv *e) { return f_network(r, e, 1, listen_args); }
static FValue *final_value(FRuntime *r, FEnv *e) { (void)e; return bad_result ? f_word(r, 1) : f_unit(r); }
static FValue *finish(FRuntime *r, FEnv *e) { return f_pure(r, e, final_value); }
static FValue *continuation(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, finish); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_bind(r, e, open_listener, continuation); }
static void release(FRuntime *r) {
  while (r->allocations) { FAllocation *next = r->allocations->next; free(r->allocations); r->allocations = next; }
}
static void stale_and_wrong_kind(void) {
  FRuntime r = {0}; FNSession s; fn_init(&s); FNHandle l;
  assert(fn_listen(&s, "127.0.0.1", 0, 8, &l).status == FN_OK);
  FValue *handle = net_handle(&r, l, 1); FNHandle original = l;
  assert(fn_close(&s, &l, 1).status == FN_OK);
  FValue *effect = new_value(&r, V_NETWORK_EFFECT); effect->as.network.operation = 7;
  effect->as.network.arguments = ready(&r, owned_pair(&r, handle, f_unit(&r)));
  assert(!net_execute(&r, &s, effect) && strstr(r.error, "stale"));
  release(&r); r = (FRuntime){0};
  effect = new_value(&r, V_NETWORK_EFFECT); effect->as.network.operation = 7;
  effect->as.network.arguments = ready(&r, owned_pair(&r, net_handle(&r, original, 0), f_unit(&r)));
  assert(!net_execute(&r, &s, effect) && strstr(r.error, "kind"));
  release(&r); assert(fn_dispose(&s).status == FN_OK);
}
int main(void) {
  unsigned char before[1024];
  for (int i = 0; i < 1024; i++) before[i] = fcntl(i, F_GETFD) >= 0;
  for (int i = 0; i < 20; i++) {
    bad_result = i % 2;
    assert(fibril_native_network_run(entry) == bad_result);
    for (int fd = 0; fd < 1024; fd++) assert(before[fd] == (fcntl(fd, F_GETFD) >= 0));
  }
  stale_and_wrong_kind();
  puts("network runtime cleanup checks passed"); return 0;
}
