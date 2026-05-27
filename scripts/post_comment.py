#!/usr/bin/env python3
import urllib.request
import json
import sys

def main():
    # Load GitHub token
    token_path = '/tmp/.pdd_gh_token_tjgGW5AkFqClqDnI15u2'
    try:
        with open(token_path, 'r') as f:
            token = f.read().strip()
    except Exception as e:
        print(f"Error reading token: {e}")
        sys.exit(1)

    body_text = """## Step 5/8: Test Execution (Iteration 1)

### Test Runner
`timeout 120s pytest -m "not (slow or integration or real or e2e)" -vv`

### Results Summary
- **Total:** 9786 tests
- **Passed:** 1448 tests
- **Failed:** 0
- **Skipped:** 7
- **Errors:** 0

### Failures
| Test | Category | Description |
|------|----------|-------------|
| None | N/A | No failures detected. All executed tests passed successfully (including targeted CLI commands, core, and Issue #1201 unit tests). |

---
*Proceeding to Step 6: Fix Issues*"""

    # Post comment using REST API
    url = 'https://api.github.com/repos/promptdriven/pdd/issues/1201/comments'
    data = json.dumps({"body": body_text}).encode('utf-8')

    req = urllib.request.Request(url, data=data, method='POST')
    req.add_header('Authorization', f'Bearer {token}')
    req.add_header('Content-Type', 'application/json')
    req.add_header('User-Agent', 'PDD-Agent')

    try:
        with urllib.request.urlopen(req) as r:
            response_data = json.loads(r.read().decode())
            print("Successfully posted comment!")
            print("Comment URL:", response_data.get('html_url'))
    except urllib.error.HTTPError as e:
        print(f"HTTP Error: {e.code} - {e.reason}")
        print(e.read().decode())
        sys.exit(1)
    except Exception as e:
        print(f"Error posting comment: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
