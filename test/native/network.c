#define _POSIX_C_SOURCE 200809L
#include "fibril_network.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static void ok(FNResult r) { assert(r.status == FN_OK); }
static void exercise(const char *address) {
  FNSession s; fn_init(&s);
  FNHandle listener, client, server;
  FNResult opened = fn_listen(&s, address, 0, 8, &listener);
  if (opened.status == FN_SYSTEM && strcmp(address, "::1") == 0 &&
      (opened.system_error == EAFNOSUPPORT || opened.system_error == EPROTONOSUPPORT || opened.system_error == EADDRNOTAVAIL)) { puts("IPv6 loopback unavailable"); return; }
  ok(opened);
  uint16_t port; ok(fn_local_port(&s, &listener, &port)); assert(port);
  FNHandle stale = listener;
  FNResult timeout = fn_accept(&s, &listener, 10, &server); assert(timeout.status == FN_TIMEOUT);
  assert(fn_local_port(&s, &stale, &port).status == FN_INVALID);
  ok(fn_connect(&s, address, port, 1000, &client));
  ok(fn_accept(&s, &listener, 1000, &server));
  assert(fcntl(s.entries[client.identity - 1].fd, F_GETFL) & O_NONBLOCK);
  assert(fcntl(s.entries[server.identity - 1].fd, F_GETFD) & FD_CLOEXEC);
  unsigned char buffer[256];
  stale = server;
  assert(fn_read(&s, &server, buffer, sizeof(buffer), 10).status == FN_TIMEOUT);
  assert(fn_read(&s, &stale, buffer, sizeof(buffer), 0).status == FN_INVALID);
  assert(fn_read(&s, &server, buffer, 0, 0).status == FN_INVALID);
  assert(fn_read(&s, &server, buffer, sizeof(buffer), FN_MAX_TIMEOUT_MS + 1).status == FN_INVALID);
  const unsigned char bytes[] = {0, 255, 13, 10, 128, 42};
  FNResult sent = fn_write_all(&s, &client, bytes, sizeof(bytes), 1000); ok(sent); assert(sent.transferred == sizeof(bytes));
  size_t got = 0;
  while (got < sizeof(bytes)) { FNResult read = fn_read(&s, &server, buffer + got, 2, 1000); ok(read); got += read.transferred; }
  assert(got == sizeof(bytes) && memcmp(buffer, bytes, got) == 0);
  ok(fn_write_all(&s, &server, buffer, got, 1000));
  size_t received = 0;
  while (received < got) { FNResult read = fn_read(&s, &client, buffer + received, got - received, 1000); ok(read); received += read.transferred; }
  assert(memcmp(buffer, bytes, received) == 0);
  ok(fn_write_all(&s, &client, NULL, 0, 0));
  ok(fn_shutdown_write(&s, &client));
  assert(fn_read(&s, &server, buffer, sizeof(buffer), 1000).status == FN_EOF);
  ok(fn_write_all(&s, &server, bytes, sizeof(bytes), 1000));
  ok(fn_read(&s, &client, buffer, sizeof(buffer), 1000));
  stale = server; int fd = s.entries[server.identity - 1].fd;
  ok(fn_close(&s, &server, 0)); assert(fcntl(fd, F_GETFD) < 0 && errno == EBADF);
  assert(fn_close(&s, &stale, 0).status == FN_INVALID);
  assert(fn_close(&s, &listener, 0).status == FN_INVALID);
  ok(fn_close(&s, &client, 0)); ok(fn_close(&s, &listener, 1)); ok(fn_dispose(&s)); ok(fn_dispose(&s));
}
static void errors_and_cleanup(void) {
  FNSession s; fn_init(&s); FNHandle h;
  assert(fn_connect(&s, "localhost", 1, 1, &h).status == FN_INVALID);
  assert(fn_connect(&s, "127.0.0.1", 0, 1, &h).status == FN_INVALID);
  assert(fn_listen(&s, "127.0.0.1", 65536, 8, &h).status == FN_INVALID);
  assert(fn_listen(&s, "127.0.0.1", 0, 0, &h).status == FN_INVALID);
  int descriptors[FN_MAX_SOCKETS];
  for (size_t i = 0; i < FN_MAX_SOCKETS; i++) { ok(fn_listen(&s, "127.0.0.1", 0, 8, &h)); descriptors[i] = s.entries[h.identity - 1].fd; }
  assert(fn_listen(&s, "127.0.0.1", 0, 8, &h).status == FN_LIMIT);
  ok(fn_dispose(&s));
  for (size_t i = 0; i < FN_MAX_SOCKETS; i++) assert(fcntl(descriptors[i], F_GETFD) < 0 && errno == EBADF);
  ok(fn_listen(&s, "127.0.0.1", 0, 8, &h)); uint16_t port; ok(fn_local_port(&s, &h, &port));
  ok(fn_close(&s, &h, 1)); assert(fn_connect(&s, "127.0.0.1", port, 1000, &h).status == FN_SYSTEM);
  ok(fn_dispose(&s));
}
static void partial_write_and_peer_reset(void) {
  FNSession s; fn_init(&s); FNHandle l, c, a; uint16_t port;
  ok(fn_listen(&s, "127.0.0.1", 0, 8, &l)); ok(fn_local_port(&s, &l, &port));
  ok(fn_connect(&s, "127.0.0.1", port, 1000, &c)); ok(fn_accept(&s, &l, 1000, &a));
  int size = 1024; assert(setsockopt(s.entries[c.identity - 1].fd, SOL_SOCKET, SO_SNDBUF, &size, sizeof(size)) == 0);
  assert(setsockopt(s.entries[a.identity - 1].fd, SOL_SOCKET, SO_RCVBUF, &size, sizeof(size)) == 0);
  unsigned char *bytes = malloc(FN_MAX_TRANSFER); assert(bytes); memset(bytes, 42, FN_MAX_TRANSFER);
  FNResult r = fn_write_all(&s, &c, bytes, FN_MAX_TRANSFER, 25);
  assert(r.status == FN_TIMEOUT && r.transferred > 0 && r.transferred < FN_MAX_TRANSFER);
  struct linger reset = {1, 0}; assert(setsockopt(s.entries[a.identity - 1].fd, SOL_SOCKET, SO_LINGER, &reset, sizeof(reset)) == 0);
  ok(fn_close(&s, &a, 0));
  r = fn_write_all(&s, &c, bytes, FN_MAX_TRANSFER, 1000); assert(r.status == FN_SYSTEM);
  /* A second write must also return an error, never terminate with SIGPIPE. */
  r = fn_write_all(&s, &c, bytes, 1, 1000); assert(r.status == FN_SYSTEM);
  free(bytes); ok(fn_dispose(&s));
}
int main(void) {
  exercise("127.0.0.1"); exercise("::1"); errors_and_cleanup(); partial_write_and_peer_reset();
  puts("network platform checks passed"); return 0;
}
