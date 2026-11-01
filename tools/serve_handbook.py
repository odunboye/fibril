#!/usr/bin/env python3
"""Serve the generated handbook on loopback with browser revalidation."""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1] / "build/handbook"


class HandbookHandler(SimpleHTTPRequestHandler):
    def end_headers(self):
        # HTML must be revalidated too: old pages can lack new token markup.
        self.send_header("Cache-Control", "no-cache")
        super().end_headers()


def make_server(port=8000, directory=DIRECTORY):
    handler = partial(HandbookHandler, directory=str(directory))
    return ThreadingHTTPServer(("127.0.0.1", port), handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()
    if not 0 <= args.port <= 65535:
        parser.error("port must be in 0..65535")
    if not (DIRECTORY / "index.html").is_file():
        parser.error("build the handbook first: make handbook")
    with make_server(args.port) as server:
        print(f"Handbook: http://127.0.0.1:{server.server_address[1]}/", flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == "__main__":
    main()
