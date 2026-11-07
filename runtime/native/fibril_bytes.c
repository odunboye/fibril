#include "fibril_bytes.h"
#include <stdlib.h>

#define FB_MAX_CHUNK ((size_t)65536)
#define FB_MAX_CAPACITY ((size_t)8388608)
#define FB_MAX_REQUESTS ((size_t)100000)

typedef struct FByteBlock {
  struct FByteBlock *next;
  unsigned char data[];
} FByteBlock;
struct FByteSession {
  size_t requests, capacity;
  FByteStatus fault;
  FByteAdapters host;
  FByteBlock *blocks;
};

static FByteStatus poison(FByteSession *s, FByteStatus status) {
  if (s->fault == FB_OK) s->fault = status;
  return s->fault;
}
static FByteStatus reserve(FByteSession *s, size_t size) {
  if (s->fault != FB_OK) return FB_POISONED;
  if (size > FB_MAX_CHUNK) return FB_CHUNK_LIMIT;
  if (!s->requests) return FB_REQUEST_LIMIT;
  if (size > s->capacity) return FB_BYTE_LIMIT;
  s->requests--; s->capacity -= size;
  return FB_OK;
}
FByteRead fibril_bytes_read(FByteSession *s, size_t capacity) {
  FByteRead result = {FB_OK, NULL, 0};
  if (s->fault != FB_OK) { result.status = FB_POISONED; return result; }
  if (!capacity) { result.status = FB_ZERO_READ; return result; }
  result.status = reserve(s, capacity);
  if (result.status != FB_OK) return result;
  /* Capacity is admitted before allocation. Aggregate live payload allocation
     cannot bypass the capacity quota by repeatedly reading EOF. */
  FByteBlock *block = malloc(sizeof(*block) + capacity);
  if (!block) { result.status = poison(s, FB_ALLOCATION_FAILED); return result; }
  block->next = s->blocks; s->blocks = block;
  result.data = block->data;
  while (result.length < capacity) {
    int byte = s->host.read(s->host.context);
    if (byte == -1) {
      result.status = result.length ? FB_OK : FB_EOF;
      return result;
    }
    if (byte == -2) { result.status = poison(s, FB_READ_FAILED); return result; }
    if (byte < 0 || byte > 255) { result.status = poison(s, FB_ADAPTER_VIOLATION); return result; }
    block->data[result.length++] = (unsigned char)byte;
  }
  return result;
}
FByteStatus fibril_bytes_write(FByteSession *s, const unsigned char *data,
                               size_t length, size_t *accepted) {
  if (accepted) *accepted = 0;
  if (length && !data) return poison(s, FB_ADAPTER_VIOLATION);
  FByteStatus status = reserve(s, length);
  if (status != FB_OK) return status;
  size_t count = 0;
  while (count < length) {
    int response = s->host.write(s->host.context, data[count]);
    if (response) {
      if (accepted) *accepted = count;
      return poison(s, response == -1 ? FB_WRITE_FAILED : FB_ADAPTER_VIOLATION);
    }
    count++;
  }
  if (accepted) *accepted = count;
  return FB_OK;
}
static FByteStatus flush_host(FByteSession *s) {
  int response = s->host.flush(s->host.context);
  return response == 0 ? FB_OK : poison(s, response == -1 ? FB_FLUSH_FAILED : FB_ADAPTER_VIOLATION);
}
FByteStatus fibril_bytes_flush(FByteSession *s) {
  FByteStatus status = reserve(s, 0);
  return status == FB_OK ? flush_host(s) : status;
}
FByteStatus fibril_bytes_run_with(size_t requests, size_t capacity, FByteAdapters host,
                                 FByteBody body, void *context) {
  if (requests > FB_MAX_REQUESTS || capacity > FB_MAX_CAPACITY ||
      !host.read || !host.write || !host.flush || !body) return FB_ADMISSION;
  FByteSession session = {requests, capacity, FB_OK, host, NULL};
  FByteStatus result = body(&session, context);
  if (session.fault != FB_OK) result = session.fault;
  else if (result == FB_OK) result = flush_host(&session);
  while (session.blocks) {
    FByteBlock *block = session.blocks;
    session.blocks = block->next;
    free(block);
  }
  return result;
}

typedef struct { FILE *input, *output; } FByteFiles;
static int read_stdio(void *context) {
  FByteFiles *files = context;
  if (ferror(files->input)) return -2;
  int byte = fgetc(files->input);
  return byte == EOF ? (ferror(files->input) ? -2 : -1) : byte;
}
static int write_stdio(void *context, unsigned char byte) {
  FByteFiles *files = context;
  if (ferror(files->output)) return -1;
  return fputc(byte, files->output) == EOF ? -1 : 0;
}
static int flush_stdio(void *context) {
  FByteFiles *files = context;
  return fflush(files->output) == 0 ? 0 : -1;
}
FByteStatus fibril_bytes_run(size_t requests, size_t capacity, FILE *input,
                            FILE *output, FByteBody body, void *context) {
  if (!input || !output) return FB_ADMISSION;
  FByteFiles files = {input, output};
  FByteAdapters host = {read_stdio, write_stdio, flush_stdio, &files};
  return fibril_bytes_run_with(requests, capacity, host, body, context);
}
