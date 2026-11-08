#include "fibril_worker.h"
#include <assert.h>
#include <sqlite3.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static const unsigned char tenant[] = {'t', 0, 'a'};
static size_t packet(unsigned char *bytes, size_t length) {
  memcpy(bytes, "FQ01", 4);
  for (size_t i = 0; i < 16; i++) bytes[4 + i] = (unsigned char)i;
  bytes[20] = (unsigned char)length;
  for (size_t i = 0; i < length; i++) bytes[21 + i] = (unsigned char)(i * 73);
  return 21 + length;
}
static size_t row_count(const char *path) {
  sqlite3 *db = NULL; sqlite3_stmt *s = NULL;
  assert(sqlite3_open(path, &db) == SQLITE_OK);
  assert(sqlite3_prepare_v2(db, "SELECT count(*) FROM fibril_queue", -1, &s, NULL) == SQLITE_OK);
  assert(sqlite3_step(s) == SQLITE_ROW);
  size_t count = (size_t)sqlite3_column_int64(s, 0);
  sqlite3_finalize(s); sqlite3_close(db); return count;
}
static void failed(FWorkerResult result, FWorkerStatus expected) {
  assert(result.status == expected && result.id == 0 && result.created == 0);
}
#ifndef FW_STUB_VALIDATOR
static void check_payload(FQueue *q, const unsigned char *request, size_t length) {
  unsigned char out[276]; size_t count; int64_t id;
  FQueueResult r = fibril_queue_get(q, tenant, sizeof(tenant), request + 4, 16,
                                  out, sizeof(out), &count, &id);
  assert(r.status == FQ_OK && count == length && id > 0);
  assert(!memcmp(out, request, count));
}

#endif
#ifdef FW_STUB_VALIDATOR
/* Deliberately broken trusted validators exercise host defenses, NOT typing. */
static int stub_mode;
FBinaryResult fibril_program_binary_embed(const FByteAdapters *host) {
  FBinaryResult result = {F_BINARY_OK, FB_OK, NULL, 0, 0};
  unsigned char bytes[300] = {0}; size_t length = 0;
  if (stub_mode == 0) return result; /* successful but empty output */
  if (stub_mode != 4) {
    int byte;
    while ((byte = host->read(host->context)) >= 0) {
      assert(length < sizeof(bytes)); bytes[length++] = (unsigned char)byte;
    }
  } else length = packet(bytes, 4); /* output valid, input not consumed */
  memcpy(bytes, "FV01", 4);
  if (stub_mode == 5) bytes[0] = 'X';
  if (stub_mode == 6) bytes[4] ^= 1;
  if (stub_mode == 7) bytes[20]++;
  if (stub_mode == 3) length = 300;
  for (size_t i = 0; i < length; i++) (void)host->write(host->context, bytes[i]);
  if (stub_mode == 1) result.status = F_BINARY_PROGRAM_ERROR;
  if (stub_mode == 2) result.status = F_BINARY_REJECTED;
  if (stub_mode == 8) { result.status = F_BINARY_TRANSPORT_ERROR; result.transport_status = FB_FLUSH_FAILED; }
  return result;
}
#endif

int main(int argc, char **argv) {
  assert(argc >= 3);
  const char *path = argv[2];
  FQueue *q = NULL;
  assert(fibril_queue_open(path, &q).status == FQ_OK);
  unsigned char request[300]; size_t length = packet(request, 4);
#ifdef FW_STUB_VALIDATOR
  stub_mode = atoi(argv[1]);
  FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
  failed(result, stub_mode == 2 ? FW_REJECTED : FW_INTERNAL);
  assert(row_count(path) == 0);
#else
  const char *mode = argv[1];
  if (!strcmp(mode, "basic") || !strcmp(mode, "maximum")) {
    if (!strcmp(mode, "maximum")) length = packet(request, 255);
    FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    assert(result.status == FW_OK && result.id > 0 && result.created == 1);
    int64_t id = result.id;
    result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    assert(result.status == FW_OK && result.id == id && result.created == 0);
    check_payload(q, request, length);
    request[length - 1] ^= 1;
    failed(fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length), FW_CONFLICT);
    request[length - 1] ^= 1;
    request[20]--;
    failed(fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length - 1), FW_CONFLICT);
    request[20]++;
    check_payload(q, request, length);
    result = fibril_worker_enqueue(q, (const unsigned char *)"other", 5, request, length);
    assert(result.status == FW_OK && result.id != id && result.created == 1);
    assert(row_count(path) == 2);
  } else if (!strcmp(mode, "reject")) {
    assert(argc == 4); int reason = atoi(argv[3]);
    if (reason == 0) request[0] = 'X';
    if (reason == 1) request[3] = '2';
    if (reason == 2) request[20] = 0;
    if (reason == 3) request[20] = 5; /* truncated body */
    if (reason == 4) request[20] = 3; /* trailing body */
    if (reason == 5) length = 20;
    if (reason == 6) length = 21;
    if (reason == 7) { length = packet(request, 256); request[20] = 255; }
    if (reason == 8) { length = packet(request, 257); request[20] = 255; }
    FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    failed(result, FW_REJECTED);
    assert(row_count(path) == 0);
  } else if (!strcmp(mode, "prefixes")) {
    for (size_t n = 0; n < length; n++)
      failed(fibril_worker_enqueue(q, tenant, sizeof(tenant), request, n), FW_REJECTED);
    assert(row_count(path) == 0);
  } else if (!strcmp(mode, "invalid")) {
    failed(fibril_worker_enqueue(NULL, tenant, sizeof(tenant), request, length), FW_INVALID_ARGUMENT);
    failed(fibril_worker_enqueue(q, NULL, sizeof(tenant), request, length), FW_INVALID_ARGUMENT);
    failed(fibril_worker_enqueue(q, tenant, 0, request, length), FW_INVALID_ARGUMENT);
    failed(fibril_worker_enqueue(q, tenant, 129, request, length), FW_INVALID_ARGUMENT);
    failed(fibril_worker_enqueue(q, tenant, sizeof(tenant), NULL, length), FW_INVALID_ARGUMENT);
    failed(fibril_worker_enqueue(q, tenant, sizeof(tenant), NULL, 0), FW_REJECTED);
    assert(row_count(path) == 0);
  } else if (!strcmp(mode, "locked")) {
    sqlite3 *db = NULL;
    assert(sqlite3_open(path, &db) == SQLITE_OK);
    assert(sqlite3_exec(db, "BEGIN IMMEDIATE", NULL, NULL, NULL) == SQLITE_OK);
    FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    failed(result, FW_BUSY); assert(row_count(path) == 0);
    assert(sqlite3_exec(db, "ROLLBACK", NULL, NULL, NULL) == SQLITE_OK);
    result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    assert(result.status == FW_OK && result.created == 1);
    sqlite3_close(db);
  } else if (!strcmp(mode, "crash")) {
    FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    assert(result.status == FW_OK && result.created == 1);
    _exit(0); /* no SQLite close/client acknowledgement after commit */
  } else if (!strcmp(mode, "replay")) {
    FWorkerResult result = fibril_worker_enqueue(q, tenant, sizeof(tenant), request, length);
    assert(result.status == FW_OK && result.created == 0 && row_count(path) == 1);
    check_payload(q, request, length);
  } else return 2;
#endif
  fibril_queue_close(q); return 0;
}
