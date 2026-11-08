#define _POSIX_C_SOURCE 200809L
#include "fibril_queue.h"
#include <assert.h>
#include <sqlite3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static const unsigned char tenant[] = {'t', 0, '\''};
static const unsigned char key[] = {'k', 0, '\''};
static const unsigned char payload[] = {0, 255, '\r', '\n'};
static FQueueRequest request = {tenant, key, payload, sizeof(tenant), sizeof(key), sizeof(payload)};
static FQueue *open_queue(const char *path) {
  FQueue *q = NULL; FQueueResult r = fibril_queue_open(path, &q);
  assert(r.status == FQ_OK && q); return q;
}
static void lookup(FQueue *q, int present) {
  unsigned char out[8] = {0}; size_t length = 99; int64_t id = -1;
  FQueueResult r = fibril_queue_get(q, tenant, sizeof(tenant), key, sizeof(key), out, sizeof(out), &length, &id);
  if (present) assert(r.status == FQ_OK && length == sizeof(payload) && id > 0 && !memcmp(out, payload, length));
  else assert(r.status == FQ_NOT_FOUND && !length && !id);
}
static void basic(const char *path) {
  FQueue *q = open_queue(path);
  int64_t id = -1, original; int created = -1;
  assert(fibril_queue_enqueue(q, &request, &id, &created).status == FQ_OK && created == 1 && id > 0);
  original = id;
  assert(fibril_queue_enqueue(q, &request, &id, &created).status == FQ_OK && !created && id == original);
  FQueueRequest other = request; other.payload = (const unsigned char *)"else";
  assert(fibril_queue_enqueue(q, &other, &id, &created).status == FQ_CONFLICT && !id && !created);
  other = request; other.tenant = (const unsigned char *)"new";
  assert(fibril_queue_enqueue(q, &other, &id, &created).status == FQ_OK && created && id != original);
  other = request; other.key = (const unsigned char *)"k\0x";
  assert(fibril_queue_enqueue(q, &other, &id, &created).status == FQ_OK && created && id != original);
  lookup(q, 1);
  unsigned char out[4] = {42, 42, 42, 42}; size_t length = 0;
  assert(fibril_queue_get(q, tenant, sizeof(tenant), key, sizeof(key), out, 1, &length, &id).status == FQ_BUFFER_SMALL);
  assert(length == sizeof(payload) && id == original && out[0] == 42);
  assert(fibril_queue_get(q, tenant, sizeof(tenant), key, sizeof(key), NULL, 0, &length, &id).status == FQ_BUFFER_SMALL);
  assert(length == sizeof(payload));
  assert(fibril_queue_get(q, tenant, sizeof(tenant), (const unsigned char *)"absent", 6, out, sizeof(out), &length, &id).status == FQ_NOT_FOUND);
  assert(!length && !id);
  fibril_queue_close(q); q = open_queue(path); lookup(q, 1);
  assert(fibril_queue_enqueue(q, &request, &id, &created).status == FQ_OK && !created && id == original);
  fibril_queue_close(q);
}
static void invalid(const char *path) {
  FQueue *q = (FQueue *)1;
  assert(fibril_queue_open(NULL, &q).status == FQ_INVALID && !q);
  assert(fibril_queue_open(":memory:", &q).status == FQ_INVALID && !q);
  assert(fibril_queue_open("file:queue.db", &q).status == FQ_INVALID && !q);
  assert(fibril_queue_open(path, NULL).status == FQ_INVALID);
  q = open_queue(path); int64_t id = -1; int created = -1;
  assert(fibril_queue_enqueue(NULL, &request, &id, &created).status == FQ_INVALID && !id && !created);
  assert(fibril_queue_enqueue(q, NULL, &id, &created).status == FQ_INVALID);
  assert(fibril_queue_enqueue(q, &request, NULL, &created).status == FQ_INVALID);
  assert(fibril_queue_enqueue(q, &request, &id, NULL).status == FQ_INVALID);
  for (int i = 0; i < 6; i++) {
    FQueueRequest bad = request;
    if (i == 0) bad.tenant_length = 0;
    if (i == 1) bad.key_length = 129;
    if (i == 2) bad.payload_length = 65537;
    if (i == 3) bad.payload = NULL;
    if (i == 4) bad.key = NULL;
    if (i == 5) bad.payload_length = 0;
    id = -1; created = -1;
    assert(fibril_queue_enqueue(q, &bad, &id, &created).status == FQ_INVALID && !id && !created);
  }
  size_t length = 9;
  assert(fibril_queue_get(q, tenant, sizeof(tenant), key, sizeof(key), NULL, 1, &length, &id).status == FQ_INVALID && !length && !id);
  lookup(q, 0); fibril_queue_close(q); fibril_queue_close(NULL);
}
static void maximum(const char *path) {
  FQueue *q = open_queue(path);
  unsigned char identity[128], body[65536], copy[65536];
  memset(identity, 255, sizeof(identity));
  for (size_t i = 0; i < sizeof(body); i++) body[i] = (unsigned char)i;
  FQueueRequest req = {identity, identity, body, sizeof(identity), sizeof(identity), sizeof(body)};
  int64_t id; int created; size_t length;
  assert(fibril_queue_enqueue(q, &req, &id, &created).status == FQ_OK && created);
  assert(fibril_queue_get(q, identity, sizeof(identity), identity, sizeof(identity), copy, sizeof(copy), &length, &id).status == FQ_OK);
  assert(length == sizeof(body) && !memcmp(body, copy, length));
  fibril_queue_close(q);
}
static void locked(const char *path) {
  FQueue *q = open_queue(path); sqlite3 *db = NULL;
  assert(sqlite3_open(path, &db) == SQLITE_OK);
  assert(sqlite3_exec(db, "BEGIN IMMEDIATE", NULL, NULL, NULL) == SQLITE_OK);
  int64_t id = 99; int created = 99;
  FQueueResult r = fibril_queue_enqueue(q, &request, &id, &created);
  assert(r.status == FQ_BUSY && !id && !created && (r.sqlite_code & 255) == SQLITE_BUSY);
  lookup(q, 0);
  assert(sqlite3_exec(db, "ROLLBACK", NULL, NULL, NULL) == SQLITE_OK);
  assert(fibril_queue_enqueue(q, &request, &id, &created).status == FQ_OK && created);
  sqlite3_close(db); fibril_queue_close(q);
}
int main(int argc, char **argv) {
  assert(argc >= 3); const char *mode = argv[1], *path = argv[2];
  if (!strcmp(mode, "basic")) basic(path);
  else if (!strcmp(mode, "invalid")) invalid(path);
  else if (!strcmp(mode, "maximum")) maximum(path);
  else if (!strcmp(mode, "locked")) locked(path);
  else if (!strcmp(mode, "init")) fibril_queue_close(open_queue(path));
  else if (!strcmp(mode, "exists") || !strcmp(mode, "absent")) {
    FQueue *q = open_queue(path); lookup(q, !strcmp(mode, "exists")); fibril_queue_close(q);
  } else if (!strcmp(mode, "crash-uncommitted")) {
    sqlite3 *db = NULL; assert(sqlite3_open(path, &db) == SQLITE_OK);
    assert(sqlite3_exec(db, "BEGIN IMMEDIATE; INSERT INTO fibril_queue(tenant,key,payload) VALUES(X'740027',X'6B0027',X'00FF0D0A')", NULL, NULL, NULL) == SQLITE_OK);
    _exit(0); /* Explicitly no rollback/SQLite close: abandoned transaction. */
  } else if (!strcmp(mode, "crash-committed")) {
    FQueue *q = open_queue(path); int64_t id; int created;
    assert(fibril_queue_enqueue(q, &request, &id, &created).status == FQ_OK);
    _exit(0); /* Commit happened, but no application acknowledgement/close. */
  } else if (!strcmp(mode, "enqueue")) {
    /* Test-driver retry policy, NOT an automatic library retry. */
    for (int attempt = 0; attempt < 200; attempt++) {
      FQueue *q = NULL; FQueueResult r = fibril_queue_open(path, &q);
      int64_t id = 0; int created = 0;
      if (r.status == FQ_OK) r = fibril_queue_enqueue(q, &request, &id, &created);
      fibril_queue_close(q);
      if (r.status == FQ_OK) { printf("%lld %d\n", (long long)id, created); return 0; }
      assert(r.status == FQ_BUSY);
      struct timespec pause = {0, 1000000}; nanosleep(&pause, NULL);
    }
    return 1;
  } else if (!strcmp(mode, "open-status")) {
    assert(argc == 4); FQueue *q = (FQueue *)1;
    FQueueResult r = fibril_queue_open(path, &q);
    assert(r.status == (FQueueStatus)atoi(argv[3]) && !q);
  } else return 2;
  return 0;
}
