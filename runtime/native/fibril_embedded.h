/* Portable C11 no-heap profile. Trusted host boundary, not a source FFI. */
#ifndef FIBRIL_EMBEDDED_H
#define FIBRIL_EMBEDDED_H
#ifndef FIBRIL_NO_HEAP
#error "Compile generated code and fibril_runtime.c with -DFIBRIL_NO_HEAP"
#endif
#include <limits.h>
#include "fibril_runtime_internal.h"
_Static_assert(SIZE_MAX >= 16777216UL, "Fibril embedded profile requires size_t to represent 16 MiB");
_Static_assert(CHAR_BIT == 8, "Fibril embedded profile requires 8-bit bytes");
#define FIBRIL_EMBEDDED_MAX_BYTES ((size_t)16777216)
/* Typed members avoid alignment/effective-type violations from casting a char
   buffer to runtime structs. Do not access members or manufacture runtime values. */
typedef union {
  max_align_t alignment;
  FValue value;
  FThunk thunk;
  FEnv env;
  FAction action;
} FEmbeddedCell;
typedef struct {
  FEmbeddedCell *cells;
  size_t cell_capacity;
  unsigned char *bytes;
  size_t byte_capacity;
  /* Invocation results/reserved state. Zero-initialize the entire descriptor.
     Never change it or its buffers while an invocation is active. */
  size_t cells_used, bytes_used;
  int busy;
} FEmbeddedArena;
/* Caller owns correctly sized, exclusive, declared FEmbeddedCell[]/unsigned char[]
   arrays through every callback. No casts from raw byte storage. Capacities include
   all storage and must sum to at most MAX_BYTES. Zero-sized pools may use NULL.
   All allocations persist until return; regions copy results but do not reclaim
   cells in this profile. Reusing a descriptor resets allocation state. */
FNativeResult fibril_native_embed_arena(FEval entry, const FNativeHost *host, FEmbeddedArena *arena);
/* Supplied by emit-c-embedded output; there is no standalone main or default IO. */
FNativeResult fibril_program_embed_arena(const FNativeHost *host, FEmbeddedArena *arena);
#endif
