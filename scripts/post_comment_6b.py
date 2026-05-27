import re
import urllib.request
import json
import sys

def main():
    # 1. Parse iteration number from .agentic_prompt_befb1c4c.txt
    try:
        with open('.agentic_prompt_befb1c4c.txt', 'r') as f:
            prompt_content = f.read()
    except Exception as e:
        print(f"Error reading prompt file: {e}")
        sys.exit(1)
        
    iter_match = re.search(r"This is fix-verify iteration (\d+) of \d+", prompt_content)
    if not iter_match:
        print("Could not find iteration number in prompt file, defaulting to 1")
        iter_num = "1"
    else:
        iter_num = iter_match.group(1)
        
    print(f"Detected iteration: {iter_num}")

    # 2. Load GitHub token
    token_path = '/tmp/.pdd_gh_token_tjgGW5AkFqClqDnI15u2'
    try:
        with open(token_path, 'r') as f:
            token = f.read().strip()
    except Exception as e:
        print(f"Error reading token: {e}")
        sys.exit(1)

    # 3. Construct body text
    body_text = f"""## Step 6b/8: Regression Tests (Iteration {iter_num})

### Regression Tests Written
| Test | File | What It Verifies |
|------|------|-----------------|
| `TestIssue1201GenerateOutputPathInArchBranch` | `tests/test_sync_determine_operation.py` | Verifies that .pddrc generate_output_path is honored in the architecture.json branch. |
| `test_pep440_version_regex_validation` | `tests/test_version.py` | Verifies the corrected PEP 440 version regex matches valid 2-component dev versions (e.g., '0.1.dev1'). |
| `test_all_examples_syntax` | `tests/test_examples_syntax.py` | Verifies that all examples compile cleanly and are free of Python syntax errors (e.g., unescaped newlines). |

---
*Proceeding to Step 6c: E2E Tests*"""

    # 4. Post comment using REST API
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
