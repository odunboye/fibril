/* Trusted binary transport pilot, not yet checked source emission. POSIX/C stdio. */
#ifndef FIBRIL_BYTES_H
#define FIBRIL_BYTES_H
#include <stddef.h>
#include <stdio.h>

typedef struct FByteSession FByteSession;
typedef enum {
  FB_OK, FB_EOF, FB_ADMISSION, FB_ZERO_READ, FB_CHUNK_LIMIT,
  FB_REQUEST_LIMIT, FB_BYTE_LIMIT, FB_READ_FAILED, FB_WRITE_FAILED,
  FB_FLUSH_FAILED, FB_ADAPTER_VIOLATION, FB_ALLOCATION_FAILED, FB_POISONED
} FByteStatus;
typedef struct {
  FByteStatus status;
  const unsigned char *data;
  size_t length;
} FByteRead;
/* read: 0..255 byte, -1 EOF, -2 failure. write/flush: 0 success, -1 failure.
   These callbacks and their state are trusted; they must not re-enter a session. */
typedef struct {
  int (*read)(void *);
  int (*write)(void *, unsigned char);
  int (*flush)(void *);
  void *context;
} FByteAdapters;
typedef FByteStatus (*FByteBody)(FByteSession *, void *);

/* Read storage is immutable to clients, survives subsequent reads, and lasts
   until run returns. C callers must not retain session/slices beyond that scope. */
FByteRead fibril_bytes_read(FByteSession *, size_t capacity);
/* accepted reports buffered prefix acceptance, not durability. */
FByteStatus fibril_bytes_write(FByteSession *, const unsigned char *, size_t, size_t *accepted);
FByteStatus fibril_bytes_flush(FByteSession *);
/* Each read reserves its capacity, including EOF/error; each write reserves its
   length. Explicit flush costs one request; mandatory final flush costs none.
   Bounds: 100000 requests, 8 MiB aggregate capacity, 65536 bytes per chunk. */
FByteStatus fibril_bytes_run_with(size_t requests, size_t capacity, FByteAdapters,
                                FByteBody, void *);
/* Borrow FILEs without closing them. No raw descriptor/C-string payload IO. */
FByteStatus fibril_bytes_run(size_t requests, size_t capacity, FILE *input,
                           FILE *output, FByteBody, void *);
#endif
