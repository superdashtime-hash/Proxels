#!/usr/bin/env python3
"""
Zero-dependency web proxy (Python 3.8+ standard library only).

Run:  python3 proxy.py                     -> http://127.0.0.1:8080
      python3 proxy.py --host 0.0.0.0      -> for Codespaces / containers

Pages are fetched server-side and served from /_px?u=<encoded-url>. HTML and CSS are
rewritten so links, images, scripts, forms and redirects stay inside the proxy, and a
small JS shim rewrites fetch/XHR/window.open at runtime. Cookies are kept server-side.
"""
import argparse
import http.cookiejar
import http.cookies
import http.server
import ipaddress
import json
import re
import secrets
import socket
import urllib.error
import urllib.request
from html import escape, unescape
from urllib.parse import quote, urlencode, urljoin, urlsplit, parse_qsl

PX = "/_px"
ALLOW_PRIVATE = False
OPENERS = {}  # session id -> urllib opener (with its own cookie jar)

HOME = """<!doctype html>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Proxy</title>
<style>
  body{margin:0;min-height:100vh;display:grid;place-items:center;background:#0f1115;color:#e8eaf0;
       font:16px system-ui,sans-serif}
  form{display:flex;gap:8px;width:min(640px,90vw)}
  input{flex:1;padding:14px 16px;border-radius:10px;border:1px solid #2a2f3a;background:#171a21;color:inherit;font-size:16px}
  button{padding:14px 20px;border-radius:10px;border:0;background:#6c8cff;color:#fff;font-size:16px;cursor:pointer}
  h1{font-weight:600;margin:0 0 16px;text-align:center}
</style>
<div><h1>Web Proxy</h1>
<form action="/go" method="get">
  <input name="q" placeholder="Enter a URL or search term" autofocus>
  <button>Go</button>
</form></div>
"""

SHIM = """<script>(function(){
  var BASE=__BASE__, PX="/_px";
  function px(u){
    if(!u||/^(data:|blob:|javascript:|mailto:|tel:|about:|#)/i.test(u)||u.indexOf(PX)===0)return u;
    try{return PX+"?u="+encodeURIComponent(new URL(u,BASE).href)}catch(e){return u}
  }
  var f=window.fetch;
  if(f)window.fetch=function(i,o){
    if(typeof i==="string")i=px(i);
    else if(i&&i.url)i=new Request(px(i.url),i);
    return f.call(this,i,o);
  };
  var xo=XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open=function(m,u){arguments[1]=px(String(u));return xo.apply(this,arguments)};
  var wo=window.open;
  window.open=function(u,a,b){return wo.call(window,u?px(String(u)):u,a,b)};
  document.addEventListener("click",function(e){
    var a=e.target.closest&&e.target.closest("a[href]");
    if(!a)return;
    var h=a.getAttribute("href");
    if(h&&h.indexOf(PX)!==0&&!/^(javascript:|#|mailto:|tel:)/i.test(h)){e.preventDefault();location.href=px(h)}
  },true);
})();</script>"""

# ---------------------------------------------------------------- rewriting
SKIP = re.compile(r"^(data:|blob:|javascript:|mailto:|tel:|about:|#)", re.I)
ATTR = re.compile(
    r"""(\s(?:href|src|action|poster|data-src|formaction)\s*=\s*)(?:"([^"]*)"|'([^']*)')""", re.I)
SRCSET = re.compile(r"""(\ssrcset\s*=\s*)(?:"([^"]*)"|'([^']*)')""", re.I)
STYLE_ATTR = re.compile(r"""(\sstyle\s*=\s*)(?:"([^"]*)"|'([^']*)')""", re.I)
STYLE_BLOCK = re.compile(r"(<style\b[^>]*>)(.*?)(</style>)", re.I | re.S)
FORM = re.compile(r"<form\b[^>]*>", re.I)
BASE_TAG = re.compile(r"""<base\b[^>]*\shref\s*=\s*["']([^"']*)["'][^>]*>""", re.I)
META_REFRESH = re.compile(
    r"""(<meta[^>]+http-equiv\s*=\s*["']?refresh["']?[^>]*content\s*=\s*["'])(\s*\d+\s*;\s*url=)([^"']*)""", re.I)
INTEGRITY = re.compile(
    r"""\s(?:integrity|nonce|crossorigin)(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s>]+))?""", re.I)
CSS_URL = re.compile(r"""url\(\s*(['"]?)(.*?)\1\s*\)""", re.I)
CSS_IMPORT = re.compile(r"""@import\s+(['"])(.*?)\1""", re.I)


def px(url, base):
    url = url.strip()
    if not url or SKIP.match(url) or url.startswith(PX):
        return url
    return PX + "?u=" + quote(urljoin(base, url), safe="")


def _quoted(m, fn):
    val = m.group(2) if m.group(2) is not None else m.group(3)
    q = '"' if m.group(2) is not None else "'"
    return f"{m.group(1)}{q}{fn(unescape(val))}{q}"


def rewrite_css(css, base):
    css = CSS_URL.sub(lambda m: f"url({m.group(1)}{px(m.group(2), base)}{m.group(1)})", css)
    return CSS_IMPORT.sub(lambda m: f"@import {m.group(1)}{px(m.group(2), base)}{m.group(1)}", css)


def rewrite_srcset(value, base):
    out = []
    for item in value.split(","):
        bits = item.strip().split()
        if bits:
            bits[0] = px(bits[0], base)
            out.append(" ".join(bits))
    return ", ".join(out)


def rewrite_form(m, base):
    """GET forms drop the action's query string in browsers, so route them via a hidden field."""
    tag = m.group(0)
    meth = re.search(r"""\smethod\s*=\s*["']?(\w+)""", tag, re.I)
    if meth and meth.group(1).lower() == "post":
        return tag  # action gets rewritten by ATTR
    act = re.search(r"""\saction\s*=\s*(?:"([^"]*)"|'([^']*)')""", tag, re.I)
    raw = unescape((act.group(1) or act.group(2) or "") if act else "")
    target = urljoin(base, raw) if raw else base
    tag = re.sub(r"""\saction\s*=\s*(?:"[^"]*"|'[^']*')""", "", tag, flags=re.I)
    return tag[:-1] + f' action="{PX}">' + f'<input type="hidden" name="u" value="{escape(target)}">'


def rewrite_html(html, base):
    b = BASE_TAG.search(html)
    if b:
        base = urljoin(base, unescape(b.group(1)))
        html = BASE_TAG.sub("", html, count=1)

    html = INTEGRITY.sub("", html)
    html = FORM.sub(lambda m: rewrite_form(m, base), html)
    html = ATTR.sub(lambda m: _quoted(m, lambda v: px(v, base)), html)
    html = SRCSET.sub(lambda m: _quoted(m, lambda v: rewrite_srcset(v, base)), html)
    html = STYLE_ATTR.sub(lambda m: _quoted(m, lambda v: rewrite_css(v, base)), html)
    html = STYLE_BLOCK.sub(lambda m: m.group(1) + rewrite_css(m.group(2), base) + m.group(3), html)
    html = META_REFRESH.sub(lambda m: m.group(1) + m.group(2) + px(unescape(m.group(3)), base), html)

    shim = SHIM.replace("__BASE__", json.dumps(base).replace("</", "<\\/"))
    head = re.search(r"<head\b[^>]*>", html, re.I)
    if head:
        return html[: head.end()] + shim + html[head.end():]
    return shim + html


def decode(raw, ctype):
    m = re.search(r"charset=([\w-]+)", ctype, re.I)
    for enc in ([m.group(1)] if m else []) + ["utf-8"]:
        try:
            return raw.decode(enc)
        except (LookupError, UnicodeDecodeError):
            continue
    return raw.decode("latin-1")


# ---------------------------------------------------------------- networking
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None  # let 3xx surface so we can rewrite Location ourselves


def new_opener():
    jar = http.cookiejar.CookieJar()
    return urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar), NoRedirect)


def is_blocked(url):
    """Refuse localhost / private ranges so the proxy can't be pointed at your own network."""
    if ALLOW_PRIVATE:
        return False
    host = urlsplit(url).hostname
    if not host:
        return True
    try:
        for info in socket.getaddrinfo(host, None):
            ip = ipaddress.ip_address(info[4][0])
            if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast:
                return True
    except socket.gaierror:
        return True
    return False


PASS_HEADERS = ("content-type", "content-range", "accept-ranges", "cache-control",
                "content-disposition", "expires")
UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"


class Handler(http.server.BaseHTTPRequestHandler):
    server_version = "MiniProxy/1.0"

    def log_message(self, fmt, *args):
        pass

    # --- helpers
    def session(self):
        c = http.cookies.SimpleCookie(self.headers.get("Cookie", ""))
        sid = c["psid"].value if "psid" in c else None
        if sid not in OPENERS:
            sid = secrets.token_urlsafe(16)
            OPENERS[sid] = new_opener()
        return OPENERS[sid], sid

    def send_simple(self, status, body, ctype="text/html; charset=utf-8", extra=()):
        data = body.encode() if isinstance(body, str) else body
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        for k, v in extra:
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    # --- routing
    def handle_any(self):
        parts = urlsplit(self.path)
        if parts.path == "/":
            return self.send_simple(200, HOME)
        if parts.path == "/go":
            q = dict(parse_qsl(parts.query)).get("q", "").strip()
            if not q:
                return self.send_simple(302, "", extra=[("Location", "/")])
            if re.match(r"^https?://", q, re.I):
                url = q
            elif "." in q and " " not in q:
                url = "https://" + q
            else:
                url = "https://duckduckgo.com/html/?q=" + quote(q)
            return self.send_simple(302, "", extra=[("Location", PX + "?u=" + quote(url, safe=""))])
        if parts.path != PX:
            return self.send_simple(404, "Not found", "text/plain")
        self.proxy(parts)

    do_GET = do_POST = do_PUT = do_DELETE = do_PATCH = do_HEAD = do_OPTIONS = handle_any

    # --- the proxy itself
    def proxy(self, parts):
        qs = parse_qsl(parts.query, keep_blank_values=True)
        target = next((v for k, v in qs if k == "u"), None)
        extra = [(k, v) for k, v in qs if k != "u"]
        if not target or not re.match(r"^https?://", target, re.I):
            return self.send_simple(400, "Only http(s) URLs are supported", "text/plain")
        if extra:  # GET form fields
            target += ("&" if "?" in target else "?") + urlencode(extra)
        if is_blocked(target):
            return self.send_simple(403, "Blocked address", "text/plain")

        opener, sid = self.session()
        site = urlsplit(target)
        origin = f"{site.scheme}://{site.netloc}"
        headers = {"User-Agent": self.headers.get("User-Agent", UA),
                   "Accept-Encoding": "identity", "Referer": origin + "/"}
        for h in ("Accept", "Accept-Language", "Range", "Content-Type"):
            if self.headers.get(h):
                headers[h] = self.headers[h]
        body = None
        if self.command not in ("GET", "HEAD", "OPTIONS"):
            n = int(self.headers.get("Content-Length") or 0)
            body = self.rfile.read(n) if n else b""
            headers["Origin"] = origin

        try:
            req = urllib.request.Request(target, data=body, headers=headers, method=self.command)
            try:
                resp = opener.open(req, timeout=20)
            except urllib.error.HTTPError as e:  # 3xx/4xx/5xx still carry a response
                resp = e
        except (urllib.error.URLError, socket.timeout, ValueError, OSError) as e:
            return self.send_simple(502, f"Upstream error: {e}", "text/plain")

        status = getattr(resp, "status", None) or resp.code
        final = resp.geturl()
        ctype = resp.headers.get("Content-Type", "")
        cookie = [("Set-Cookie", f"psid={sid}; Path=/; HttpOnly; SameSite=Lax")]
        passthru = [(h, resp.headers[h]) for h in PASS_HEADERS if resp.headers.get(h)]

        if 300 <= status < 400 and resp.headers.get("Location"):
            loc = px(resp.headers["Location"], final)
            return self.send_simple(status, "", extra=[("Location", loc)] + cookie)

        low = ctype.lower()
        if "text/html" in low or "text/css" in low:
            text = decode(resp.read(), ctype)
            text = rewrite_html(text, final) if "text/html" in low else rewrite_css(text, final)
            hdrs = [(k, v) for k, v in passthru if k.lower() not in ("content-type", "content-range")]
            return self.send_simple(status, text, f"{low.split(';')[0]}; charset=utf-8", hdrs + cookie)

        # everything else: stream through untouched
        self.send_response(status)
        for k, v in passthru:
            self.send_header(k, v)
        if resp.headers.get("Content-Length"):
            self.send_header("Content-Length", resp.headers["Content-Length"])
        self.send_header("Set-Cookie", cookie[0][1])
        self.end_headers()
        if self.command == "HEAD":
            return
        try:
            while True:
                chunk = resp.read(64 * 1024)
                if not chunk:
                    break
                self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass


def main():
    global ALLOW_PRIVATE
    ap = argparse.ArgumentParser()
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--allow-private", action="store_true", help="allow localhost/LAN targets")
    args = ap.parse_args()
    ALLOW_PRIVATE = args.allow_private
    srv = http.server.ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"Proxy running on http://{args.host}:{args.port}")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
