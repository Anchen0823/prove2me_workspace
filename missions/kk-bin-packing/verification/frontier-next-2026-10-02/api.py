"""Scoped Prove2me requests; tokens stay in the API client and are never printed."""
import json
import sys
import time
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts'))
import p2m_api as api

HERE = Path(__file__).resolve().parent
action, name, *args = sys.argv[1:]
token = api.get_token()
def get(path):
    for attempt in range(4):
        try:
            return api._request('GET', path, token=token)
        except Exception as exc:
            print('Read retry', attempt + 1, type(exc).__name__, flush=True)
            if attempt == 3:
                raise SystemExit('Read unavailable; no mutation attempted')
            time.sleep(3)

if action == 'get':
    status, body = get(args[0])
elif action == 'search':
    status, body = get('/theorems?q=' + quote(args[0]))
elif action == 'publish':
    payload = json.loads((HERE / args[0]).read_text(encoding='utf-8'))
    status, body = api._request('POST', '/submit-problem', token=token, data=payload)
elif action == 'rate':
    payload = json.loads((HERE / args[0]).read_text(encoding='utf-8'))
    status, body = api._request('POST', '/rate', token=token, data=payload)
elif action == 'verify':
    target, source, explanation = args
    raw, ctype = api._multipart(
        {'theorem_id': target, 'proof_type': 'prove',
         'explanation': (ROOT / explanation).read_text(encoding='utf-8')},
        {'file': ('solution.lean', (ROOT / source).read_text(encoding='utf-8'))})
    status, body = api._request('POST', '/verify', token=token, raw_body=raw, ctype=ctype)
else:
    raise SystemExit('Unknown action')
(HERE / (name + '.json')).write_text(body, encoding='utf-8')
print('HTTP', status)
try:
    data = json.loads(body)
    if isinstance(data, dict):
        print(json.dumps({k: data[k] for k in (
            'status', 'id', 'submission_id', 'theorem_id', 'jobs', 'errors', 'error_message'
        ) if k in data}, ensure_ascii=True))
    else:
        print('items', len(data))
except ValueError:
    print('Saved non-JSON response')
if status >= 400:
    raise SystemExit(1)
