"""
The graphical interface, run locally:

    python -m pyfunction.gui [--port 8765] [--no-browser]

starts a small web server on this machine (standard library only) and opens
the interface in the browser; the analysis runs in this Python process.
Stop it with Ctrl+C.
"""

import argparse
import json
import sys
import threading
import webbrowser
from http.server import HTTPServer, BaseHTTPRequestHandler

from . import web

API = {'analyze': web.analyze, 'view': web.view}


class Handler(BaseHTTPRequestHandler):

    def _send(self, code, body, ctype='text/plain; charset=utf-8'):
        data = body.encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if self.path in ('/', '/index.html'):
            # rebuilt at each request: reloading the page picks up any change
            self._send(200, web.page(), 'text/html; charset=utf-8')
        else:
            self._send(404, 'not found')

    def do_POST(self):
        name = self.path[len('/api/'):] if self.path.startswith('/api/') else None
        if name not in API:
            return self._send(404, 'unknown function')
        try:
            args = json.loads(self.rfile.read(int(self.headers.get('Content-Length', 0))) or b'[]')
            self._send(200, API[name](*args), 'application/json')
        except Exception as e:
            self._send(500, '%s: %s' % (type(e).__name__, e))

    def log_message(self, fmt, *args):  # quiet
        pass


def main(argv=None):
    ap = argparse.ArgumentParser(prog='python -m pyfunction.gui', description='The graphical interface of PyFuncTion.')
    ap.add_argument('--port', type=int, default=8765)
    ap.add_argument('--no-browser', action='store_true', help='do not open the browser')
    args = ap.parse_args(argv)
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    # only reachable from this machine
    server = HTTPServer(('127.0.0.1', args.port), Handler)
    url = 'http://127.0.0.1:%d/' % server.server_port
    print('PyFuncTion interface at %s (Ctrl+C to stop)' % url)
    if not args.no_browser:
        threading.Timer(0.5, webbrowser.open, (url,)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
