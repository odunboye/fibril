/* Experimental synchronous embedding for checked binary IO programs. */
#ifndef FIBRIL_BINARY_EMBED_H
#define FIBRIL_BINARY_EMBED_H
#include "fibril_runtime.h"
#include "fibril_bytes.h"

typedef enum {
  F_BINARY_OK = 0,
  F_BINARY_INVALID_ARGUMENT,
  F_BINARY_PROGRAM_ERROR,
  F_BINARY_TRANSPORT_ERROR,
  /* Explicit checked primRejectBytes, distinct from evaluator/internal failure. */
  F_BINARY_REJECTED
} FBinaryStatus;
typedef struct {
  FBinaryStatus status;
  /* Meaningful for TRANSPORT_ERROR only; otherwise FB_OK. Runtime errors are
     not misreported as a host adapter violation. */
  FByteStatus transport_status;
  /* Static immutable diagnostic storage, NULL on success. */
  const char *message;
  /* Partial bytes for the failing operation, NOT cumulative transfer totals.
     Nonzero only for FB_READ_FAILED / FB_WRITE_FAILED respectively. Accepted
     output is not a durability or remote-acknowledgement guarantee. */
  size_t read_prefix, write_prefix;
} FBinaryResult;

/* Link fibril_binary_runtime.c alone (it includes the pure/transport runtimes).
   Entry and all three host callbacks are required, even for a pure program.
   No stdio, retries or process termination. Existing transport/evaluation budgets
   apply. IO is incremental: earlier effects can precede a program failure.
   Host callbacks/state are borrowed for the call; they must return normally. */
FBinaryResult fibril_native_binary_embed(FEval entry, size_t requests,
                                        size_t capacity, const FByteAdapters *host);
/* Supplied only by newly generated emit-c-binary output. Compile that output
   with FIBRIL_EMBED_ONLY to omit its standalone main. One program per image. */
FBinaryResult fibril_program_binary_embed(const FByteAdapters *host);
#endif
