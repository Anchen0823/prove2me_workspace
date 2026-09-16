#!/usr/bin/env python
"""Small Prove2me API client used from the command line.

Usage:
  python scripts/p2m_api.py token
  python scripts/p2m_api.py get  <path> [query]
  python scripts/p2m_api.py raw  <path>            # print raw JSON
  python scripts/p2m_api.py verify <theorem_id> <file> [proof_type]
  python scripts/p2m_api.py patch-explain <submission_id> <explanation_file>
"""
import json
import os
import ssl
import sys
import time
import urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CRED = os.path.join(ROOT, "credentials.json")
BASE = "https://prove2.me/api/v1"

_CTX = ssl.create_default_context()
_OPENER = urllib.request.build_opener(urllib.request.ProxyHandler())


def _load():
    with open(CRED, "r", encoding="utf-8") as fh:
        return json.load(fh)


def _save(creds):
    with open(CRED, "w", encoding="utf-8") as fh:
        json.dump(creds, fh, indent=2)


def _request(method, path, token=None, data=None, ctype="application/json", raw_body=None):
    url = BASE + path
    headers = {}
    if token:
        headers["Authorization"] = "Bearer " + token
    if raw_body is not None:
        body = raw_body
        headers["Content-Type"] = ctype
    elif data is not None:
        body = json.dumps(data).encode("utf-8")
        headers["Content-Type"] = "application/json"
    else:
        body = None
    req = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with _OPENER.open(req, timeout=120) as resp:
            return resp.status, resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "replace")


def get_token(force=False):
    creds = _load()
    now = int(time.time())
    if not force and creds.get("access_token") and creds.get("expires_at", 0) > now + 120:
        return creds["access_token"]
    status, body = _request("POST", "/agent/refresh", data={"api_key": creds["api_key"]})
    if status != 200:
        raise SystemExit("refresh failed: %s %s" % (status, body))
    payload = json.loads(body)
    creds["access_token"] = payload.get("access_token") or payload.get("token")
    exp = payload.get("expires_in") or payload.get("expires_in_seconds") or 3600
    creds["expires_at"] = now + int(exp) - 60
    if payload.get("version"):
        creds["version"] = payload["version"]
    _save(creds)
    print("version=%s" % payload.get("version"), file=sys.stderr)
    return creds["access_token"]


def _multipart(fields, files):
    boundary = "----p2mBoundary7f3a9c2b"
    out = []
    for k, v in fields.items():
        out.append(("--%s\r\nContent-Disposition: form-data; name=\"%s\"\r\n\r\n%s\r\n" % (boundary, k, v)).encode("utf-8"))
    for k, (fname, content) in files.items():
        out.append(("--%s\r\nContent-Disposition: form-data; name=\"%s\"; filename=\"%s\"\r\n"
                    "Content-Type: text/plain\r\n\r\n" % (boundary, k, fname)).encode("utf-8"))
        out.append(content.encode("utf-8") if isinstance(content, str) else content)
        out.append(b"\r\n")
    out.append(("--%s--\r\n" % boundary).encode("utf-8"))
    return b"".join(out), "multipart/form-data; boundary=%s" % boundary


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    cmd = sys.argv[1]

    if cmd == "token":
        print(get_token(force="--force" in sys.argv))
        return 0

    if cmd == "get":
        tok = get_token()
        path = sys.argv[2]
        if len(sys.argv) > 3:
            path = path + "?" + sys.argv[3]
        status, body = _request("GET", path, token=tok)
        try:
            print(json.dumps(json.loads(body), indent=2, ensure_ascii=False))
        except Exception:
            print(status, body)
        return 0

    if cmd == "raw":
        tok = get_token()
        status, body = _request("GET", sys.argv[2], token=tok)
        print(status)
        print(body)
        return 0

    if cmd == "post":
        # post <path> <json_file_or_inline>
        tok = get_token()
        arg = sys.argv[3]
        if os.path.exists(arg):
            with open(arg, "r", encoding="utf-8") as fh:
                data = json.load(fh)
        else:
            data = json.loads(arg)
        status, body = _request("POST", sys.argv[2], token=tok, data=data)
        print(status)
        try:
            print(json.dumps(json.loads(body), indent=2, ensure_ascii=False))
        except Exception:
            print(body)
        return 0

    if cmd == "patch":
        tok = get_token()
        arg = sys.argv[3]
        if os.path.exists(arg):
            with open(arg, "r", encoding="utf-8") as fh:
                data = json.load(fh)
        else:
            data = json.loads(arg)
        status, body = _request("PATCH", sys.argv[2], token=tok, data=data)
        print(status)
        print(body)
        return 0

    if cmd == "patch-explain":
        tok = get_token()
        sub = sys.argv[2]
        with open(sys.argv[3], "r", encoding="utf-8") as fh:
            text = fh.read()
        status, body = _request("PATCH", "/submissions/" + sub, token=tok, data={"explanation": text})
        print(status)
        print(body)
        return 0

    if cmd == "verify":
        tok = get_token()
        theorem_id = sys.argv[2]
        path = sys.argv[3]
        proof_type = sys.argv[4] if len(sys.argv) > 4 else "prove"
        explanation = None
        if len(sys.argv) > 5 and os.path.exists(sys.argv[5]):
            with open(sys.argv[5], "r", encoding="utf-8") as fh:
                explanation = fh.read()
        with open(path, "r", encoding="utf-8") as fh:
            src = fh.read()
        fields = {"theorem_id": theorem_id, "proof_type": proof_type}
        if explanation:
            fields["explanation"] = explanation
        body, ctype = _multipart(fields, {"file": (os.path.basename(path), src)})
        status, resp = _request("POST", "/verify", token=tok, raw_body=body, ctype=ctype)
        print(status)
        print(resp)
        return 0

    print("unknown command", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
