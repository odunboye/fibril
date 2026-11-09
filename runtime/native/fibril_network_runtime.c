/* TCP profile. Generated network C includes fibril_runtime.c, fibril_network.c, then this
   file, in one translation unit, because it uses the runtime's statics. */
#define F_MAX_NETWORK_REQUESTS ((size_t)4096)
#define F_MAX_NETWORK_PENDING ((size_t)4096)

FValue *f_network(FRuntime *r, FEnv *e, size_t operation, FEval arguments) {
  FValue *v = new_value(r, V_NETWORK_EFFECT);
  if (v) { v->as.network.operation = operation; v->as.network.arguments = thunk(r, arguments, e); }
  return v;
}
static FValue *net_variant(FRuntime *r, size_t tag, FValue *payload) {
  FValue *v = new_value(r, V_VARIANT);
  if (v) { v->as.variant.tag = tag; v->as.variant.payload = payload ? ready(r, payload) : NULL; }
  return v;
}
static FValue *net_error(FRuntime *r, FNResult status) {
  return owned_pair(r, f_word(r, (uint64_t)status.status), f_word(r, (uint64_t)status.transferred));
}
static FValue *net_result(FRuntime *r, FNResult status, FValue *value) {
  return status.status == FN_OK ? net_variant(r, 1, value) : net_variant(r, 0, net_error(r, status));
}
static FValue *net_handle(FRuntime *r, FNHandle handle, int listener) {
  FValue *v = new_value(r, listener ? V_NETWORK_LISTENER : V_NETWORK_STREAM);
  if (v) { v->as.socket.identity = handle.identity; v->as.socket.generation = handle.generation; }
  return v;
}
static int net_unpack(FRuntime *r, FThunk *arguments, size_t count, FValue **values) {
  FValue *pair = force(r, arguments);
  for (size_t i = 0; i < count; i++) {
    if (!pair || pair->tag != V_PAIR) { fail(r, "malformed network arguments"); return 0; }
    values[i] = force(r, pair->as.pair.first);
    pair = force(r, pair->as.pair.second);
    if (!values[i]) return 0;
  }
  if (!pair || pair->tag != V_UNIT) { fail(r, "malformed network argument terminator"); return 0; }
  return 1;
}
static int net_word(FRuntime *r, FValue *v, uint64_t *out) {
  if (!v || v->tag != V_WORD) { fail(r, "network argument expects Word"); return 0; }
  *out = v->as.word; return 1;
}
static int net_owned(FRuntime *r, FNSession *session, FValue *v, int listener, FNHandle *out) {
  if (!v || v->tag != (listener ? V_NETWORK_LISTENER : V_NETWORK_STREAM)) {
    fail(r, "network operation has the wrong socket kind"); return 0;
  }
  *out = (FNHandle){v->as.socket.identity, v->as.socket.generation};
  if (!out->identity || out->identity > FN_MAX_SOCKETS) { fail(r, "invalid network handle"); return 0; }
  FNEntry *entry = &session->entries[out->identity - 1];
  if (entry->fd < 0 || entry->generation != out->generation || entry->listener != listener) {
    fail(r, "stale or closed network handle"); return 0;
  }
  return 1;
}
static FValue *net_execute(FRuntime *r, FNSession *session, FValue *effect) {
  size_t op = effect->as.network.operation;
  size_t count = op < 2 || op == 3 || op == 4 ? 3 : op == 2 ? 2 : 1;
  if (op > 8) { fail(r, "unknown network operation"); return NULL; }
  FValue *a[3];
  if (!net_unpack(r, effect->as.network.arguments, count, a)) return NULL;
  FNResult status = { FN_INVALID, 0, 0 };
  if (op < 2) {
    uint64_t port, limit;
    if (a[0]->tag != V_STRING || !net_word(r, a[1], &port) || !net_word(r, a[2], &limit)) {
      fail(r, "network address expects String"); return NULL;
    }
    /* Numeric IPv6 fits in 45 bytes; reject NUL and all longer input before copying. */
    size_t length = a[0]->as.string.length;
    FNHandle handle = {0};
    if (length && length < 46 && !memchr(a[0]->as.string.bytes, 0, length)) {
      char address[46]; memcpy(address, a[0]->as.string.bytes, length); address[length] = 0;
      status = op == 0 ? fn_connect(session, address, port, limit, &handle)
                       : fn_listen(session, address, port, limit, &handle);
    }
    return net_result(r, status, status.status == FN_OK ? net_handle(r, handle, op == 1) : NULL);
  }
  int listener = op == 2 || op == 6 || op == 7;
  FNHandle handle;
  if (!net_owned(r, session, a[0], listener, &handle)) return NULL;
  FValue *payload = NULL;
  if (op == 2) {
    uint64_t timeout; FNHandle client = {0};
    if (!net_word(r, a[1], &timeout)) return NULL;
    status = fn_accept(session, &handle, timeout, &client);
    payload = net_result(r, status, status.status == FN_OK ? net_handle(r, client, 0) : NULL);
  } else if (op == 3) {
    uint64_t capacity, timeout;
    if (!net_word(r, a[1], &capacity) || !net_word(r, a[2], &timeout)) return NULL;
    /* Invalid capacity still consumes and returns ownership through fn_read. */
    unsigned char *buffer = capacity && capacity <= FN_MAX_TRANSFER ? allocate(r, (size_t)capacity) : NULL;
    if (r->error) return NULL;
    status = fn_read(session, &handle, buffer, capacity <= FN_MAX_TRANSFER ? (size_t)capacity : 0, timeout);
    if (status.status == FN_OK) {
      FValue *bytes = new_value(r, V_BYTES);
      if (!bytes) return NULL;
      bytes->as.bytes.data = buffer; bytes->as.bytes.length = status.transferred;
      payload = net_variant(r, 1, bytes);
    } else if (status.status == FN_EOF) payload = net_variant(r, 0, NULL);
    else payload = net_variant(r, 2, net_error(r, status));
  } else if (op == 4) {
    uint64_t timeout;
    if (a[1]->tag != V_BYTES || !net_word(r, a[2], &timeout)) { fail(r, "network write expects Bytes"); return NULL; }
    status = fn_write_all(session, &handle, a[1]->as.bytes.data, a[1]->as.bytes.length, timeout);
    payload = net_result(r, status, status.status == FN_OK ? f_word(r, status.transferred) : NULL);
  } else if (op == 5 || op == 6) {
    status = fn_close(session, &handle, listener);
    return net_result(r, status, status.status == FN_OK ? f_unit(r) : NULL);
  } else if (op == 7) {
    uint16_t port = 0; status = fn_local_port(session, &handle, &port);
    payload = net_result(r, status, status.status == FN_OK ? f_word(r, port) : NULL);
  } else {
    status = fn_shutdown_write(session, &handle);
    payload = net_result(r, status, status.status == FN_OK ? f_unit(r) : NULL);
  }
  return owned_pair(r, net_handle(r, handle, listener), payload);
}

typedef struct FNetworkPending { FThunk *next; struct FNetworkPending *tail; } FNetworkPending;
static FValue *net_interact(FRuntime *r, FNSession *session, FValue *io) {
  FNetworkPending *pending = NULL, *available = NULL;
  size_t depth = 0, requests = 0;
  for (;;) {
    if (!enter(r)) return NULL;
    r->depth--;
    if (!io) { fail(r, "missing network IO description"); return NULL; }
    if (io->tag == V_BIND) {
      if (depth >= F_MAX_NETWORK_PENDING) { fail(r, "network continuation budget exhausted"); return NULL; }
      FNetworkPending *node;
      if (available) { node = available; available = node->tail; }
      else node = allocate(r, sizeof(*node));
      if (!node) return NULL;
      node->next = io->as.io.second; node->tail = pending; pending = node; depth++;
      io = force(r, io->as.io.first); continue;
    }
    FValue *value = NULL;
    if (io->tag == V_PURE) value = force(r, io->as.io.first);
    else if (io->tag == V_NETWORK_EFFECT) {
      if (requests >= F_MAX_NETWORK_REQUESTS) { fail(r, "network operation budget exhausted"); return NULL; }
      requests++; value = net_execute(r, session, io);
    } else if (io->tag == V_WRITE) {
      if (requests >= F_MAX_NETWORK_REQUESTS) { fail(r, "network operation budget exhausted"); return NULL; }
      requests++;
      FValue *text = force(r, io->as.io.first);
      if (!text || text->tag != V_STRING || (text->as.string.length && memchr(text->as.string.bytes, 0, text->as.string.length))) {
        fail(r, "invalid network console output"); return NULL;
      }
      if (fwrite(text->as.string.bytes, 1, text->as.string.length, stdout) != text->as.string.length || fputc('\n', stdout) == EOF || fflush(stdout) != 0) {
        fail(r, "network console output failed"); return NULL;
      }
      value = f_unit(r);
    } else { fail(r, "IO operation is unsupported by the network profile"); return NULL; }
    if (!value || r->error) return NULL;
    if (!pending) return value;
    FNetworkPending *node = pending; pending = node->tail; depth--;
    FThunk *continuation = node->next; node->tail = available; available = node;
    FValue *next = force(r, continuation);
    io = next ? apply_thunk(r, next, ready(r, value)) : NULL;
  }
}
int fibril_native_network_run(FEval entry) {
  FRuntime r = {0}; FNSession session; fn_init(&session);
  if (!entry) fail(&r, "missing network entry");
  FValue *io = entry ? evaluate(&r, entry, NULL) : NULL;
  FValue *value = io ? net_interact(&r, &session, io) : NULL;
  if (!r.error && (!value || value->tag != V_UNIT)) fail(&r, "network main did not return Unit");
  FNResult cleanup = fn_dispose(&session);
  if (cleanup.status != FN_OK) fail(&r, "network socket cleanup failed");
  int status = r.error ? 1 : 0;
  if (r.error) fprintf(stderr, "Fibril network error: %s\n", r.error);
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return status;
}
