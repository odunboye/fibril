/* POSIX TCP platform boundary. No HTTP, SQL, DNS, TLS or process-global state. */
#ifndef FIBRIL_NETWORK_H
#define FIBRIL_NETWORK_H
#include <stddef.h>
#include <stdint.h>
#define FN_MAX_SOCKETS 64
#define FN_MAX_TRANSFER ((size_t)1048576)
#define FN_MAX_TIMEOUT_MS UINT64_C(3600000)
typedef enum { FN_OK, FN_EOF, FN_TIMEOUT, FN_INVALID, FN_SYSTEM, FN_LIMIT } FNStatus;
typedef struct { FNStatus status; size_t transferred; int system_error; } FNResult;
typedef struct { uint64_t identity, generation; } FNHandle;
/* Session-private data. Do not manufacture handles or mutate active entries.
   A session is single-owner; separate sessions may run on separate threads. */
typedef struct { int fd, listener; uint64_t generation; } FNEntry;
typedef struct { FNEntry entries[FN_MAX_SOCKETS]; uint64_t generation; } FNSession;
void fn_init(FNSession *session);
/* Cleanup attempts every live descriptor once, including after an earlier error. */
FNResult fn_dispose(FNSession *session);
FNResult fn_connect(FNSession *, const char *numeric_address, uint64_t port, uint64_t timeout_ms, FNHandle *out);
FNResult fn_listen(FNSession *, const char *numeric_address, uint64_t port, uint64_t backlog, FNHandle *out);
/* Valid handle operations advance generation even on timeout/system errors.
   Close consumes the handle. No API retries close after EINTR. */
FNResult fn_accept(FNSession *, FNHandle *listener, uint64_t timeout_ms, FNHandle *out);
FNResult fn_read(FNSession *, FNHandle *, void *buffer, size_t capacity, uint64_t timeout_ms);
FNResult fn_write_all(FNSession *, FNHandle *, const void *buffer, size_t length, uint64_t timeout_ms);
FNResult fn_shutdown_write(FNSession *, FNHandle *);
FNResult fn_local_port(FNSession *, FNHandle *listener, uint16_t *port);
FNResult fn_close(FNSession *, FNHandle *, int listener);
#endif
