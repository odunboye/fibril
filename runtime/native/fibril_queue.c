#define _POSIX_C_SOURCE 200809L
#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#endif
#include "fibril_queue.h"
#include <errno.h>
#include <fcntl.h>
#include <sqlite3.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

struct FQueue { sqlite3 *db; };
static const char schema[] =
  "CREATE TABLE fibril_queue ("
  "id INTEGER PRIMARY KEY AUTOINCREMENT,"
  "tenant BLOB NOT NULL CHECK(typeof(tenant)='blob' AND length(tenant) BETWEEN 1 AND 128),"
  "key BLOB NOT NULL CHECK(typeof(key)='blob' AND length(key) BETWEEN 1 AND 128),"
  "payload BLOB NOT NULL CHECK(typeof(payload)='blob' AND length(payload) BETWEEN 1 AND 65536),"
  "UNIQUE(tenant,key))";
static FQueueResult result(FQueueStatus status, int code) {
  FQueueResult r = {status, code}; return r;
}
static FQueueResult sql_result(int code) {
  if (code == SQLITE_OK) return result(FQ_OK, 0);
  int primary = code & 255;
  return result(primary == SQLITE_BUSY || primary == SQLITE_LOCKED ? FQ_BUSY : FQ_STORAGE, code);
}
static int execute(sqlite3 *db, const char *sql) { return sqlite3_exec(db, sql, NULL, NULL, NULL); }
static void rollback(sqlite3 *db) { (void)execute(db, "ROLLBACK"); }
static int identity_valid(const unsigned char *bytes, size_t length) {
  return bytes && length > 0 && length <= 128;
}
static int identity_bind(sqlite3_stmt *s, const unsigned char *tenant, size_t tn,
                         const unsigned char *key, size_t kn) {
  int code = sqlite3_bind_blob(s, 1, tenant, (int)tn, SQLITE_TRANSIENT);
  if (code == SQLITE_OK) code = sqlite3_bind_blob(s, 2, key, (int)kn, SQLITE_TRANSIENT);
  return code;
}
/* Refuse unrelated/version-mismatched schemas, rather than repairing them or
   allowing hidden triggers to alter enqueue semantics. Inspect before WAL and
   again under the initialization write lock. Database contents remain trusted. */
static int inspect_schema(sqlite3 *db, int *version, FQueueStatus *policy) {
  sqlite3_stmt *s = NULL;
  int code = sqlite3_prepare_v2(db, "PRAGMA user_version", -1, &s, NULL);
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_ROW) { *version = sqlite3_column_int(s, 0); code = SQLITE_OK; }
  }
  sqlite3_finalize(s); s = NULL;
  if (code != SQLITE_OK) return code;
  if (*version != 0 && *version != 1) { *policy = FQ_UNSUPPORTED; return SQLITE_OK; }
  code = sqlite3_prepare_v2(db,
    "SELECT count(*) FROM sqlite_schema WHERE name NOT GLOB 'sqlite_*'", -1, &s, NULL);
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_ROW) {
      if (sqlite3_column_int(s, 0) != (*version == 0 ? 0 : 1)) *policy = FQ_UNSUPPORTED;
      code = SQLITE_OK;
    }
  }
  sqlite3_finalize(s); s = NULL;
  if (code != SQLITE_OK || *policy != FQ_OK || *version == 0) return code;
  code = sqlite3_prepare_v2(db,
    "SELECT sql FROM sqlite_schema WHERE type='table' AND name='fibril_queue'", -1, &s, NULL);
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_ROW) {
      const unsigned char *text = sqlite3_column_text(s, 0);
      if (!text || strcmp((const char *)text, schema)) *policy = FQ_UNSUPPORTED;
      code = SQLITE_OK;
    } else if (code == SQLITE_DONE) { *policy = FQ_UNSUPPORTED; code = SQLITE_OK; }
  }
  sqlite3_finalize(s); return code;
}

void fibril_queue_close(FQueue *queue) {
  if (!queue) return;
  (void)sqlite3_close_v2(queue->db);
  free(queue);
}

FQueueResult fibril_queue_open(const char *path, FQueue **out) {
  if (out) *out = NULL;
  if (!out || !path || !*path || !strcmp(path, ":memory:") || !strncmp(path, "file:", 5))
    return result(FQ_INVALID, 0);
  if (sqlite3_libversion_number() < 3035000) return result(FQ_UNSUPPORTED, 0);
  /* No global umask change; refuse unsafe existing files rather than chmod them.
     The later SQLite open assumes no hostile path replacement in the trusted
     directory. This is not a race-proof filesystem sandbox. */
  int fd = open(path, O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC, 0600);
  if (fd < 0) return result(errno == ELOOP ? FQ_INVALID : FQ_STORAGE, 0);
  struct stat st;
  int safe = fstat(fd, &st) == 0 && S_ISREG(st.st_mode) && st.st_uid == geteuid() &&
             (st.st_mode & 077) == 0 && st.st_nlink == 1;
  int closed = close(fd);
  if (!safe) return result(FQ_INVALID, 0);
  if (closed) return result(FQ_STORAGE, 0);
  FQueue *queue = calloc(1, sizeof(*queue));
  if (!queue) return result(FQ_STORAGE, SQLITE_NOMEM);
  int code = sqlite3_open_v2(path, &queue->db, SQLITE_OPEN_READWRITE | SQLITE_OPEN_FULLMUTEX, NULL);
  if (code != SQLITE_OK) {
    FQueueResult failure = sql_result(code); fibril_queue_close(queue); return failure;
  }
  sqlite3_extended_result_codes(queue->db, 1);
  sqlite3_busy_timeout(queue->db, 0); /* host policy decides if/when to retry */
  int version = -1;
  FQueueStatus policy = FQ_OK;
  code = inspect_schema(queue->db, &version, &policy);
  if (code != SQLITE_OK || policy != FQ_OK) {
    FQueueResult failure = policy != FQ_OK ? result(policy, 0) : sql_result(code);
    fibril_queue_close(queue); return failure;
  }
  sqlite3_stmt *s = NULL;
  code = sqlite3_prepare_v2(queue->db, "PRAGMA journal_mode=WAL", -1, &s, NULL);
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_ROW) {
      const unsigned char *mode = sqlite3_column_text(s, 0);
      code = mode && !strcmp((const char *)mode, "wal") ? SQLITE_OK : SQLITE_ERROR;
    }
  }
  sqlite3_finalize(s); s = NULL;
  if (code == SQLITE_OK) code = execute(queue->db, "PRAGMA synchronous=FULL; PRAGMA trusted_schema=OFF;");
  if (code == SQLITE_OK) code = execute(queue->db, "BEGIN IMMEDIATE");
  if (code != SQLITE_OK) {
    FQueueResult failure = sql_result(code); fibril_queue_close(queue); return failure;
  }
  code = inspect_schema(queue->db, &version, &policy);
  if (code == SQLITE_OK && policy == FQ_OK && version == 0) {
    code = execute(queue->db, schema);
    if (code == SQLITE_OK) code = execute(queue->db, "PRAGMA user_version=1");
  }
  if (code == SQLITE_OK && policy == FQ_OK) code = execute(queue->db, "COMMIT");
  else rollback(queue->db);
  if (code != SQLITE_OK || policy != FQ_OK) {
    FQueueResult failure = policy != FQ_OK ? result(policy, 0) : sql_result(code);
    rollback(queue->db); fibril_queue_close(queue); return failure;
  }
  *out = queue; return result(FQ_OK, 0);
}

FQueueResult fibril_queue_enqueue(FQueue *queue, const FQueueRequest *request, int64_t *id, int *created) {
  if (id) *id = 0;
  if (created) *created = 0;
  if (!queue || !request || !id || !created ||
      !identity_valid(request->tenant, request->tenant_length) ||
      !identity_valid(request->key, request->key_length) ||
      !request->payload || !request->payload_length || request->payload_length > 65536)
    return result(FQ_INVALID, 0);
  sqlite3 *db = queue->db;
  int code = execute(db, "BEGIN IMMEDIATE");
  if (code != SQLITE_OK) return sql_result(code);
  sqlite3_stmt *s = NULL;
  code = sqlite3_prepare_v2(db, "SELECT id,payload FROM fibril_queue WHERE tenant=?1 AND key=?2", -1, &s, NULL);
  if (code == SQLITE_OK) code = identity_bind(s, request->tenant, request->tenant_length, request->key, request->key_length);
  int64_t row = 0;
  int inserted = 0, conflict = 0;
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_ROW) {
      int length = sqlite3_column_bytes(s, 1);
      const void *stored = sqlite3_column_blob(s, 1);
      conflict = length != (int)request->payload_length || !stored ||
                 memcmp(stored, request->payload, request->payload_length) != 0;
      row = sqlite3_column_int64(s, 0); code = SQLITE_OK;
    } else if (code == SQLITE_DONE) { inserted = 1; code = SQLITE_OK; }
  }
  sqlite3_finalize(s); s = NULL;
  if (code == SQLITE_OK && !conflict && inserted) {
    code = sqlite3_prepare_v2(db, "INSERT INTO fibril_queue(tenant,key,payload) VALUES(?1,?2,?3)", -1, &s, NULL);
    if (code == SQLITE_OK) code = identity_bind(s, request->tenant, request->tenant_length, request->key, request->key_length);
    if (code == SQLITE_OK) code = sqlite3_bind_blob(s, 3, request->payload, (int)request->payload_length, SQLITE_TRANSIENT);
    if (code == SQLITE_OK) { code = sqlite3_step(s); if (code == SQLITE_DONE) code = SQLITE_OK; }
    if (code == SQLITE_OK) row = sqlite3_last_insert_rowid(db);
    sqlite3_finalize(s);
  }
  if (code == SQLITE_OK && !conflict) code = execute(db, "COMMIT");
  if (code != SQLITE_OK || conflict) {
    rollback(db); return conflict ? result(FQ_CONFLICT, 0) : sql_result(code);
  }
  *id = row; *created = inserted; return result(FQ_OK, 0);
}

FQueueResult fibril_queue_get(FQueue *queue, const unsigned char *tenant, size_t tn,
                            const unsigned char *key, size_t kn, unsigned char *payload,
                            size_t capacity, size_t *length, int64_t *id) {
  if (length) *length = 0;
  if (id) *id = 0;
  if (!queue || !length || !id || !identity_valid(tenant, tn) || !identity_valid(key, kn) ||
      (capacity && !payload)) return result(FQ_INVALID, 0);
  sqlite3_stmt *s = NULL;
  int code = sqlite3_prepare_v2(queue->db, "SELECT id,payload FROM fibril_queue WHERE tenant=?1 AND key=?2", -1, &s, NULL);
  if (code == SQLITE_OK) code = identity_bind(s, tenant, tn, key, kn);
  FQueueStatus status = FQ_OK;
  if (code == SQLITE_OK) {
    code = sqlite3_step(s);
    if (code == SQLITE_DONE) { status = FQ_NOT_FOUND; code = SQLITE_OK; }
    else if (code == SQLITE_ROW) {
      int count = sqlite3_column_bytes(s, 1);
      const void *stored = sqlite3_column_blob(s, 1);
      if (count <= 0 || count > 65536 || !stored) code = SQLITE_CORRUPT;
      else {
        *length = (size_t)count; *id = sqlite3_column_int64(s, 0);
        if (capacity < *length) status = FQ_BUFFER_SMALL;
        else memcpy(payload, stored, *length);
        code = SQLITE_OK;
      }
    }
  }
  sqlite3_finalize(s);
  if (code != SQLITE_OK) { *length = 0; *id = 0; return sql_result(code); }
  return result(status, 0);
}
