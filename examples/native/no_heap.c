/* Link with emit-c-embedded output and fibril_runtime.c, all with FIBRIL_NO_HEAP.
   This sample uses only caller-owned static memory and a memory sink. */
#include "fibril_embedded.h"
#include <string.h>

static FEmbeddedCell cells[512];
static unsigned char scratch[4096];
typedef struct { unsigned char data[64]; size_t length, flushes; } Sink;
static int write_bytes(void *context, const unsigned char *data, size_t length) {
  Sink *sink=context;
  if(length>sizeof(sink->data)-sink->length) return 1;
  memcpy(sink->data+sink->length,data,length);sink->length+=length;return 0;
}
static int flush(void *context) { ((Sink *)context)->flushes++;return 0; }
int main(void) {
  /* Explicit UTF-8 octets, independent of the host execution character set. */
  static const unsigned char expected[]={118,97,108,117,101,61,54,51,10};
  FEmbeddedArena arena={.cells=cells,.cell_capacity=512,.bytes=scratch,.byte_capacity=sizeof(scratch)};
  for(int i=0;i<3;i++) {
    Sink sink={0};FNativeHost host={&sink,write_bytes,flush};
    FNativeResult result=fibril_program_embed_arena(&host,&arena);
    if(result.status!=F_NATIVE_OK) return 1;
    if(sink.length!=sizeof(expected) || memcmp(sink.data,expected,sizeof(expected)) || sink.flushes!=1) return 2;
    /* arena.cells_used and arena.bytes_used describe this invocation's usage. */
  }
  return 0;
}
