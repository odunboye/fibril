/* Internal layout shared only to provide strictly typed caller-owned storage.
   Experimental ABI: rebuild generated code, runtime and host together. */
#ifndef FIBRIL_RUNTIME_INTERNAL_H
#define FIBRIL_RUNTIME_INTERNAL_H
#include "fibril_runtime.h"
/* Keep every payload suitably aligned for all C object types. */
typedef union FAllocation { union FAllocation *next; max_align_t alignment; } FAllocation;
typedef struct FThunk FThunk;
/* A sub-arena owns allocations made while it is current; the run-wide arena
   (FRuntime.allocations) is the root, and a NULL region means the root. */
typedef struct FRegion { FAllocation *allocations; size_t bytes; } FRegion;
typedef struct FAction { const unsigned char *bytes; size_t length; struct FAction *next; } FAction;
struct FEnv { FThunk *value; FEnv *tail; };
typedef enum { V_UNIT, V_ERASED, V_BOOL, V_STRING, V_BYTES, V_CLOSURE, V_NOMINAL, V_VARIANT,
               V_NAT_ZERO, V_NAT_SUCC, V_REC_END, V_REC_MORE, V_SEQ_NIL, V_SEQ_CONS,
               V_PURE, V_BIND, V_WRITE, V_READ, V_PAIR, V_INPUT_HANDLE,
               V_WITH_INPUT, V_READ_INPUT, V_READ_BYTES, V_WRITE_BYTES, V_FLUSH_BYTES, V_REJECT_BYTES, V_ITERATE_BINARY,
               V_WORD, V_NETWORK_EFFECT, V_NETWORK_STREAM, V_NETWORK_LISTENER } FTag;
typedef enum { F_NAT, F_NAT_RUNTIME, F_REC, F_SEQ } FFoldKind;
struct FValue {
  FTag tag;
  union {
    struct { const unsigned char *bytes; size_t length; } string;
    struct { const unsigned char *data; size_t length; } bytes;
    int boolean;
    uint64_t word;
    struct { uint64_t identity, generation; } socket;
    struct { size_t operation; FThunk *arguments; } network;
    FThunk *nominal;
    struct { size_t tag; FThunk *payload; } variant;
    struct { FThunk *head, *tail; } recursive;
    struct { FEval body; FEnv *env; int erased; } closure;
    struct { FThunk *first, *second; } io;
    struct { FThunk *count, *step, *initial; } iteration;
    struct { FThunk *first, *second; } pair;
    struct { size_t identity, generation; } handle;
  } as;
};
struct FThunk {
  FEval code;
  FEnv *env;
  FValue *value;
  int state, is_fold;
  FFoldKind fold_kind;
  FRegion *owner;
  FThunk *input;
  FEval base, step;
};

#endif
