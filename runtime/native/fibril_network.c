/* Narrow POSIX implementation; protocol and application libraries live in Fibril. */
#define _POSIX_C_SOURCE 200809L
#include "fibril_network.h"
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static FNResult result(FNStatus status, size_t count, int error) {
  FNResult r = {status, count, error}; return r;
}
static FNResult syserror(void) { return result(FN_SYSTEM, 0, errno); }
void fn_init(FNSession *s) {
  *s = (FNSession){0};
  for (size_t i = 0; i < FN_MAX_SOCKETS; i++) s->entries[i].fd = -1;
}
FNResult fn_dispose(FNSession *s) {
  FNResult r = result(FN_OK, 0, 0);
  for (size_t i = 0; i < FN_MAX_SOCKETS; i++) if (s->entries[i].fd >= 0) {
    int fd = s->entries[i].fd; s->entries[i].fd = -1;
    if (close(fd) != 0 && r.status == FN_OK) r = syserror();
  }
  return r;
}
static int address(const char *text, uint64_t port, struct sockaddr_storage *out, socklen_t *length) {
  if (!text || port > 65535) return 0;
  memset(out, 0, sizeof(*out));
  struct sockaddr_in *v4 = (struct sockaddr_in *)(void *)out;
  if (inet_pton(AF_INET, text, &v4->sin_addr) == 1) {
    v4->sin_family = AF_INET; v4->sin_port = htons((uint16_t)port); *length = sizeof(*v4); return AF_INET;
  }
  memset(out, 0, sizeof(*out));
  struct sockaddr_in6 *v6 = (struct sockaddr_in6 *)(void *)out;
  if (inet_pton(AF_INET6, text, &v6->sin6_addr) == 1) {
    v6->sin6_family = AF_INET6; v6->sin6_port = htons((uint16_t)port); *length = sizeof(*v6); return AF_INET6;
  }
  return 0;
}
static int configure(int fd) {
  int flags = fcntl(fd, F_GETFL);
  if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0 || fcntl(fd, F_SETFD, FD_CLOEXEC) < 0) return 0;
#ifdef SO_NOSIGPIPE
  int yes = 1;
  if (setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &yes, sizeof(yes)) != 0) return 0;
#endif
#if !defined(SO_NOSIGPIPE) && !defined(MSG_NOSIGNAL)
#error "TCP writes require per-socket/per-call SIGPIPE suppression"
#endif
  return 1;
}
static FNResult register_fd(FNSession *s, int fd, int listener, FNHandle *out) {
  for (size_t i = 0; i < FN_MAX_SOCKETS; i++) if (s->entries[i].fd < 0) {
    if (s->generation == UINT64_MAX) break;
    s->entries[i] = (FNEntry){fd, listener, ++s->generation};
    *out = (FNHandle){i + 1, s->generation}; return result(FN_OK, 0, 0);
  }
  (void)close(fd); return result(FN_LIMIT, 0, 0);
}
static FNEntry *take(FNSession *s, FNHandle *handle, int listener) {
  if (!handle || !handle->identity || handle->identity > FN_MAX_SOCKETS || s->generation == UINT64_MAX) return NULL;
  FNEntry *e = &s->entries[handle->identity - 1];
  if (e->fd < 0 || e->listener != listener || e->generation != handle->generation) return NULL;
  handle->generation = e->generation = ++s->generation; return e;
}
static int now_ms(uint64_t *value) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) return 0;
  if (t.tv_sec < 0 || (uint64_t)t.tv_sec > (UINT64_MAX - 3600001) / 1000) { errno = EOVERFLOW; return 0; }
  *value = (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000; return 1;
}
static FNResult deadline(uint64_t timeout, uint64_t *end) {
  if (timeout > FN_MAX_TIMEOUT_MS) return result(FN_INVALID, 0, 0);
  if (!now_ms(end)) return syserror();
  *end += timeout; return result(FN_OK, 0, 0);
}
static FNResult wait_fd(int fd, short events, uint64_t end) {
  for (;;) {
    uint64_t now;
    if (!now_ms(&now)) return syserror();
    int remaining = now >= end ? 0 : (int)(end - now);
    struct pollfd p = {fd, events, 0};
    int n = poll(&p, 1, remaining);
    if (n < 0) { if (errno == EINTR) { if (now >= end) return result(FN_TIMEOUT, 0, 0); continue; } return syserror(); }
    if (!n) return result(FN_TIMEOUT, 0, 0);
    if (p.revents & POLLNVAL) return result(FN_INVALID, 0, 0);
    /* Let recv/send/accept/SO_ERROR explain HUP and ERR. Buffered data may remain. */
    return result(FN_OK, 0, 0);
  }
}
static int expired(uint64_t end) { uint64_t now; return !now_ms(&now) || now >= end; }
FNResult fn_connect(FNSession *s, const char *text, uint64_t port, uint64_t timeout, FNHandle *out) {
  struct sockaddr_storage addr; socklen_t length;
  if (!out || !port) return result(FN_INVALID, 0, 0);
  int family = address(text, port, &addr, &length);
  if (!family) return result(FN_INVALID, 0, 0);
  uint64_t end; FNResult r = deadline(timeout, &end); if (r.status != FN_OK) return r;
  int fd = socket(family, SOCK_STREAM, 0); if (fd < 0) return syserror();
  if (!configure(fd)) { r = syserror(); (void)close(fd); return r; }
  if (connect(fd, (struct sockaddr *)(void *)&addr, length) != 0) {
    if (errno != EINPROGRESS && errno != EINTR) { r = syserror(); (void)close(fd); return r; }
    r = wait_fd(fd, POLLOUT, end);
    if (r.status == FN_OK) {
      int error = 0; socklen_t n = sizeof(error);
      if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &error, &n) != 0) r = syserror();
      else if (error) r = result(FN_SYSTEM, 0, error);
    }
    if (r.status != FN_OK) { (void)close(fd); return r; }
  }
  return register_fd(s, fd, 0, out);
}
FNResult fn_listen(FNSession *s, const char *text, uint64_t port, uint64_t backlog, FNHandle *out) {
  struct sockaddr_storage addr; socklen_t length;
  int family = address(text, port, &addr, &length);
  if (!family || !out || !backlog || backlog > 4096) return result(FN_INVALID, 0, 0);
  int fd = socket(family, SOCK_STREAM, 0); if (fd < 0) return syserror();
  FNResult r;
  int yes = 1;
  if (!configure(fd) || setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes)) != 0 ||
      (family == AF_INET6 && setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY, &yes, sizeof(yes)) != 0) ||
      bind(fd, (struct sockaddr *)(void *)&addr, length) != 0 || listen(fd, (int)backlog) != 0) {
    r = syserror(); (void)close(fd); return r;
  }
  return register_fd(s, fd, 1, out);
}
FNResult fn_accept(FNSession *s, FNHandle *handle, uint64_t timeout, FNHandle *out) {
  FNEntry *e = take(s, handle, 1); if (!e || !out) return result(FN_INVALID, 0, 0);
  uint64_t end; FNResult r = deadline(timeout, &end); if (r.status != FN_OK) return r;
  for (;;) {
    r = wait_fd(e->fd, POLLIN, end); if (r.status != FN_OK) return r;
    int fd = accept(e->fd, NULL, NULL);
    if (fd >= 0) {
      if (!configure(fd)) { r = syserror(); (void)close(fd); return r; }
      return register_fd(s, fd, 0, out);
    }
    if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK && errno != ECONNABORTED) return syserror();
    if (expired(end)) return result(FN_TIMEOUT, 0, 0);
  }
}
FNResult fn_read(FNSession *s, FNHandle *handle, void *buffer, size_t capacity, uint64_t timeout) {
  FNEntry *e = take(s, handle, 0); if (!e) return result(FN_INVALID, 0, 0);
  if (!buffer || !capacity || capacity > FN_MAX_TRANSFER) return result(FN_INVALID, 0, 0);
  uint64_t end; FNResult r = deadline(timeout, &end); if (r.status != FN_OK) return r;
  for (;;) {
    r = wait_fd(e->fd, POLLIN, end); if (r.status != FN_OK) return r;
    ssize_t n = recv(e->fd, buffer, capacity, 0);
    if (n > 0) return result(FN_OK, (size_t)n, 0);
    if (!n) return result(FN_EOF, 0, 0);
    if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) return syserror();
    if (expired(end)) return result(FN_TIMEOUT, 0, 0);
  }
}
FNResult fn_write_all(FNSession *s, FNHandle *handle, const void *buffer, size_t length, uint64_t timeout) {
  FNEntry *e = take(s, handle, 0); if (!e) return result(FN_INVALID, 0, 0);
  if ((length && !buffer) || length > FN_MAX_TRANSFER) return result(FN_INVALID, 0, 0);
  uint64_t end; FNResult r = deadline(timeout, &end); if (r.status != FN_OK) return r;
  size_t sent = 0;
  while (sent < length) {
    r = wait_fd(e->fd, POLLOUT, end); if (r.status != FN_OK) { r.transferred = sent; return r; }
    int flags = 0;
#ifdef MSG_NOSIGNAL
    flags = MSG_NOSIGNAL;
#endif
    ssize_t n = send(e->fd, (const unsigned char *)buffer + sent, length - sent, flags);
    if (n > 0) sent += (size_t)n;
    else if (!n) return result(FN_SYSTEM, sent, EPIPE);
    else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) return result(FN_SYSTEM, sent, errno);
    if (sent < length && expired(end)) return result(FN_TIMEOUT, sent, 0);
  }
  return result(FN_OK, sent, 0);
}
FNResult fn_shutdown_write(FNSession *s, FNHandle *handle) {
  FNEntry *e = take(s, handle, 0); if (!e) return result(FN_INVALID, 0, 0);
  return shutdown(e->fd, SHUT_WR) == 0 ? result(FN_OK, 0, 0) : syserror();
}
FNResult fn_local_port(FNSession *s, FNHandle *handle, uint16_t *port) {
  FNEntry *e = take(s, handle, 1); if (!e || !port) return result(FN_INVALID, 0, 0);
  struct sockaddr_storage addr; socklen_t n = sizeof(addr);
  if (getsockname(e->fd, (struct sockaddr *)(void *)&addr, &n) != 0) return syserror();
  if (addr.ss_family == AF_INET) *port = ntohs(((struct sockaddr_in *)(void *)&addr)->sin_port);
  else if (addr.ss_family == AF_INET6) *port = ntohs(((struct sockaddr_in6 *)(void *)&addr)->sin6_port);
  else return result(FN_INVALID, 0, 0);
  return result(FN_OK, 0, 0);
}
FNResult fn_close(FNSession *s, FNHandle *handle, int listener) {
  FNEntry *e = take(s, handle, listener); if (!e) return result(FN_INVALID, 0, 0);
  int fd = e->fd; e->fd = -1; *handle = (FNHandle){0};
  return close(fd) == 0 ? result(FN_OK, 0, 0) : syserror();
}
