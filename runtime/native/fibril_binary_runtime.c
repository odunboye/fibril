/* Binary-only amalgamation. Compile this INSTEAD of fibril_runtime.c; do not
   additionally link fibril_bytes.c. Pure runtime and transport remain reusable
   standalone translation units for the legacy modes/tests. Trusted, not verified. */
#include "fibril_runtime.c"
#include "fibril_bytes.c"

typedef struct {
  FRuntime *runtime;
  FEval entry;
  FByteStatus fault;
  size_t read_prefix, write_prefix;
} FBinaryContext;

static int binary_capacity(FRuntime *r, FThunk *input, size_t *out) {
  FValue *value = force(r, input);
  size_t count = 0;
  while (value && value->tag == V_NAT_SUCC) {
    if (!byte_work(r)) return 0;
    if (count < SIZE_MAX) count++;
    value = force(r, value->as.recursive.tail);
  }
  if (!value || value->tag != V_NAT_ZERO) { fail(r, "native binary capacity expects Nat"); return 0; }
  *out = count; return 1;
}

static FThunk *interact_binary(FBinaryContext *context, FByteSession *session, FValue *io) {
  FRuntime *r = context->runtime;
  if (!enter(r)) return NULL;
  FThunk *result = NULL;
  if (!io) fail(r, "missing native binary description");
  else if (io->tag == V_PURE) result = io->as.io.first;
  else if (io->tag == V_READ_BYTES) {
    size_t capacity;
    if (binary_capacity(r, io->as.io.first, &capacity)) {
      FByteRead read = fibril_bytes_read(session, capacity);
      if (read.status == FB_EOF) result = ready(r, read_result(r, 0, NULL));
      else if (read.status == FB_OK) {
        FValue *bytes = f_bytes_literal(r, read.data, read.length);
        if (bytes) result = ready(r, read_result(r, 1, bytes));
      } else {
        context->fault = read.status;
        context->read_prefix = read.length;
      }
    }
  } else if (io->tag == V_WRITE_BYTES) {
    FValue *bytes = force(r, io->as.io.first);
    if (!bytes || bytes->tag != V_BYTES) fail(r, "native binary write expects Bytes");
    else {
      FByteStatus status = fibril_bytes_write(session, bytes->as.bytes.data,
                                             bytes->as.bytes.length, &context->write_prefix);
      if (status == FB_OK) result = ready(r, f_unit(r));
      else context->fault = status;
    }
  } else if (io->tag == V_REJECT_BYTES) {
    fail(r, "Binary program rejected input");
  } else if (io->tag == V_FLUSH_BYTES) {
    FByteStatus status = fibril_bytes_flush(session);
    if (status == FB_OK) result = ready(r, f_unit(r));
    else context->fault = status;
  } else if (io->tag == V_BIND) {
    FValue *first = force(r, io->as.io.first);
    FThunk *value = first ? interact_binary(context, session, first) : NULL;
    FValue *next = value ? force(r, io->as.io.second) : NULL;
    FValue *following = next ? apply_thunk(r, next, value) : NULL;
    if (following) result = interact_binary(context, session, following);
  } else fail(r, "native binary runner rejects non-binary IO");
  r->depth--; return result;
}

static FByteStatus binary_body(FByteSession *session, void *opaque) {
  FBinaryContext *context = opaque;
  FRuntime *r = context->runtime;
  FValue *io = evaluate(r, context->entry, NULL);
  FThunk *final = io ? interact_binary(context, session, io) : NULL;
  FValue *unit = final ? force(r, final) : NULL;
  if (context->fault != FB_OK) return context->fault;
  if (!r->error && (!unit || unit->tag != V_UNIT)) fail(r, "native binary main did not return Unit");
  /* A pure evaluator failure must not look like callback success/final flush. */
  return r->error ? FB_ADAPTER_VIOLATION : FB_OK;
}

static const char *binary_error(FByteStatus status) {
  switch (status) {
    case FB_OK: return "success";
    case FB_EOF: return "unexpected EOF status";
    case FB_ADMISSION: return "Binary transport admission exceeded";
    case FB_ZERO_READ: return "Binary reads require a positive capacity";
    case FB_CHUNK_LIMIT: return "Binary chunk exceeds 65536 bytes";
    case FB_REQUEST_LIMIT: return "Binary request budget exhausted";
    case FB_BYTE_LIMIT: return "Binary capacity budget exhausted";
    case FB_READ_FAILED: return "Binary read failed";
    case FB_WRITE_FAILED: return "Binary write failed";
    case FB_FLUSH_FAILED: return "Binary flush failed";
    case FB_ADAPTER_VIOLATION: return "Binary adapter violated its response contract";
    case FB_ALLOCATION_FAILED: return "Binary transport allocation failed";
    case FB_POISONED: return "Binary transport has a prior physical failure";
  }
  return "unknown binary failure";
}

static int binary_finish(FRuntime *r, FBinaryContext *context, FByteStatus status) {
  int failed = status != FB_OK || r->error;
  if (r->error) fprintf(stderr, "fibril native binary: %s\n", r->error);
  else if (status == FB_READ_FAILED)
    fprintf(stderr, "fibril native binary: %s after %zu bytes\n", binary_error(status), context->read_prefix);
  else if (status == FB_WRITE_FAILED)
    fprintf(stderr, "fibril native binary: %s after accepting %zu bytes\n", binary_error(status), context->write_prefix);
  else if (status != FB_OK) fprintf(stderr, "fibril native binary: %s\n", binary_error(status));
  /* Session payloads are already freed. Do not inspect borrowed byte/string
     views here; only arena metadata is traversed to release the pure runtime. */
  while (r->allocations) { FAllocation *next = r->allocations->next; free(r->allocations); r->allocations = next; }
  return failed ? 1 : 0;
}

int fibril_native_binary_run(FEval entry, size_t requests, size_t capacity) {
  FRuntime runtime = {0};
  FBinaryContext context = {&runtime, entry, FB_OK, 0, 0};
  if (!entry) fail(&runtime, "missing native binary entry");
  FByteStatus status = runtime.error ? FB_ADAPTER_VIOLATION :
    fibril_bytes_run(requests, capacity, stdin, stdout, binary_body, &context);
  return binary_finish(&runtime, &context, status);
}
