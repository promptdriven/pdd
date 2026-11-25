import '../../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { performance } from 'node:perf_hooks';
import {
  ADVERSARIAL_BOUNDARY_SURFACES,
  classifyNativeOnlySurfaces,
  detectAdversarialProbesInTest,
  inspectAdversarialBoundaryEvidence,
} from '../../../src/core/lint/adversarial-boundary.mjs';
import { EXIT_NOT_PROVED, EXIT_PROVED, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../../src/core/prove.mjs';
import {
  detectRealHostProbesInTest,
  evaluateValidationOutcome,
} from '../../../src/autopilot-validator.mjs';

function makeSink() {
  let text = '';
  return { write(s) { text += String(s); }, get text() { return text; } };
}

function writeFile(root, rel, content) {
  const abs = join(root, rel);
  mkdirSync(dirname(abs), { recursive: true });
  writeFileSync(abs, content);
}

function initRepo(t, prefix) {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', '-b', 'main'], { cwd: dir });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: dir });
  execFileSync('git', ['config', 'user.email', 'test@example.com'], { cwd: dir });
  return dir;
}

function commitAll(dir, msg) {
  execFileSync('git', ['add', '.'], { cwd: dir });
  execFileSync('git', ['commit', '-q', '-m', msg], { cwd: dir });
}

test('#3633 surface classification maps all 4 boundary surfaces accurately without misclassifying SQLite HTTP error text', () => {
  assert.deepEqual(ADVERSARIAL_BOUNDARY_SURFACES, [
    'http-auth-browser-mcp',
    'binary-parser',
    'storage-dr',
    'cli-day0',
  ]);
  assert.deepEqual(
    classifyNativeOnlySurfaces({
      modulePath: 'src/trust/store.mjs',
      promptText: '---\nkind: native-only\nreason: SQLite adapter.\n---\n# Store\nOpens SQLite DB.\nMaps SQLITE_BUSY to HTTP 503.',
      moduleSource: "import { DatabaseSync } from 'node:sqlite';\nexport const open = (p) => new DatabaseSync(p);\n",
    }),
    ['storage-dr'],
  );
  assert.deepEqual(
    classifyNativeOnlySurfaces({
      modulePath: 'src/records/service.py',
      promptText: '---\nkind: native-only\nreason: FastAPI PDF/XLSX upload redaction service.\n---\n# Records\n',
      moduleSource: 'from fastapi import APIRouter\nimport zipfile\n',
    }),
    ['binary-parser', 'http-auth-browser-mcp'],
  );
  assert.deepEqual(
    classifyNativeOnlySurfaces({
      modulePath: 'bin/ledger-cli.mjs',
      promptText: '---\nkind: native-only\nreason: Day-0 CLI entrypoint.\n---\n',
      moduleSource: 'console.log(process.argv);\n',
    }),
    ['cli-day0'],
  );
  assert.deepEqual(
    classifyNativeOnlySurfaces({
      modulePath: 'src/hsm/signer.mjs',
      promptText: '---\nkind: native-only\nreason: Hardware HSM signing.\n---\n',
      moduleSource: 'export const sign = () => Buffer.alloc(1);\n',
    }),
    ['general-native-boundary'],
  );
});

test('#3633 anti-bypass suite: all comment, docstring, dead-branch, skip, tautology, title, mock, shadow, and file-leak cheats are blocked; valid JS regex literal passes', () => {
  const bypasses = [
    ['happy-path HTTPServer daemon Thread + sqlite3.connect', 'tests/test_http_thread.py',
      'import sqlite3, threading, unittest, urllib.request\nfrom http.server import HTTPServer\nclass T(unittest.TestCase):\n    def test_ok(self):\n        conn = sqlite3.connect(":memory:")\n        srv = HTTPServer(("127.0.0.1", 0), Handler)\n        t = threading.Thread(target=srv.serve_forever, daemon=True)\n        t.start()\n        resp = urllib.request.urlopen(f"http://127.0.0.1:{srv.server_port}/health")\n        self.assertEqual(resp.status, 200)\n        conn.close()\n'],
    ['happy-path TestClient + sqlite3.connect', 'tests/test_smoke.py',
      'import sqlite3\nfrom fastapi.testclient import TestClient\ndef test_health(app):\n    conn = sqlite3.connect(":memory:")\n    assert TestClient(app).get("/health").status_code == 200\n    conn.close()\n'],
    ['comment stuffing', 'tests/test_comment.py',
      'from fastapi.testclient import TestClient\n# csrf Origin ../ ../../escaped_pwned bool("false") /ObjStm <!ENTITY 401 403\ndef test_smoke(app):\n    assert TestClient(app).get("/health").status_code == 200\n'],
    ['2-letter prefix docstring rf"""..."""', 'tests/test_rf_doc.py',
      'from fastapi.testclient import TestClient\ndef test_smoke(app):\n    rf"""csrf Origin ../ assert resp.status_code == 403"""\n    assert TestClient(app).get("/health").status_code == 200\n'],
    ['function name stuffing + plain 404', 'tests/test_fn_name.py',
      'from fastapi.testclient import TestClient\ndef test_path_traversal(app):\n    assert TestClient(app).get("/missing").status_code == 404\n'],
    ['JS test title stuffing + failure msg', 'test/title.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf origin path_traversal ssrf forged', async () => {\n  const res = await fetch('http://127.0.0.1/health');\n  assert.equal(res.status, 200, 'should not fail');\n});\n"],
    ['parenthesized tautology assert not (False)', 'tests/test_paren_taut.py',
      'from fastapi.testclient import TestClient\ndef test_smoke(app):\n    assert TestClient(app).get("/health").status_code == 200\n    assert not (False)\n'],
    ['authenticated happy GET + errors == []', 'tests/test_auth_happy.py',
      'from fastapi.testclient import TestClient\ndef test_health(app):\n    r = TestClient(app).get("/health", headers={"Authorization": "Bearer valid"})\n    assert r.status_code == 200\n    assert r.json()["errors"] == []\n'],
    ['happy GET + resp.is_error is False', 'tests/test_is_error.py',
      'from fastapi.testclient import TestClient\ndef test_health(app):\n    resp = TestClient(app).get("/health")\n    assert resp.status_code == 200\n    assert resp.is_error is False\n'],
    ['plain 404 on %20 URL space', 'tests/test_pct20.py',
      'from fastapi.testclient import TestClient\ndef test_space(app):\n    assert TestClient(app).get("/hello%20world").status_code == 404\n'],
    ['happy CLI --help only (returncode == 0)', 'tests/test_cli_help.py',
      'import subprocess\ndef test_help(tmp_path):\n    r = subprocess.run(["node", "bin/mycli.mjs", "--help"], env={"HOME": str(tmp_path)})\n    assert r.returncode == 0\n'],
    ['happy 200 GET /browser CSP form only (no negative HTTP probe)', 'tests/test_csp_only.py',
      'from fastapi.testclient import TestClient\ndef test_browser(app):\n    r = TestClient(app).get("/browser")\n    assert r.status_code == 200 and "script-src \'none\'" in r.headers["Content-Security-Policy"] and "<form" in r.text\n'],
    ['JS tautology assert.equal(0, 0)', 'test/js-taut.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  const r = await fetch('http://127.0.0.1/health');\n  assert.equal(r.status, 200);\n  assert.equal(0, 0);\n});\n"],
    ['Python dead if False: branch', 'tests/test_if_false.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    assert TestClient(app).get("/health").status_code == 200\n    if False:\n        assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['JS dead if (false) branch', 'test/if-false.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  assert.equal((await fetch('http://127.0.0.1/health')).status, 200);\n  if (false) {\n    const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n    assert.equal(r.status, 403);\n  }\n});\n"],
    ['early return before fake 403', 'tests/test_early_ret.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    assert TestClient(app).get("/health").status_code == 200\n    return\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['bare string + plain 404', 'tests/test_bare_str.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    "../escaped_pwned"\n    assert TestClient(app).get("/missing").status_code == 404\n'],
    ['multiline unused dict + unused dict()', 'tests/test_dead_dict.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    u1 = {\n        "Origin": "https://evil.test"\n    }\n    u2 = dict(early_exercise_allowed="false")\n    r = TestClient(app).get("/health")\n    assert r.status_code == 200\n'],
    ['uncalled nested Python def', 'tests/test_nested_def.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    def never_called():\n        assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n    assert TestClient(app).get("/health").status_code == 200\n'],
    ['uncalled nested JS arrow fn', 'test/nested-arrow.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  const neverCalled = async () => { assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403); };\n  assert.equal((await fetch('http://127.0.0.1/health')).status, 200);\n});\n"],
    ['@pytest.mark.skip + comment gap', 'tests/test_skip_gap.py',
      'import pytest\nfrom fastapi.testclient import TestClient\n@pytest.mark.skip(reason="todo")\n# comment between decorator and def\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['multiline @pytest.mark.skipif', 'tests/test_skip_ml.py',
      'import pytest\nfrom fastapi.testclient import TestClient\n@pytest.mark.skipif(\n    True,\n    reason="skip"\n)\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['module-level pytestmark skip', 'tests/test_pytestmark.py',
      'import pytest\nfrom fastapi.testclient import TestClient\npytestmark = pytest.mark.skip(reason="all")\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['class-level @pytest.mark.skip', 'tests/test_skip_cls.py',
      'import pytest\nfrom fastapi.testclient import TestClient\n@pytest.mark.skip(reason="cls")\nclass TestAdv:\n    def test_csrf(self, app):\n        assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['Node test({ skip: "reason" })', 'test/node-skip-str.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', { skip: 'not ready' }, async () => {\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\n"],
    ['JS describe.skip wrapper', 'test/desc-skip.test.mjs',
      "import { describe, it } from 'node:test';\nimport assert from 'node:assert/strict';\ndescribe.skip('adv', () => {\n  it('csrf', async () => {\n    assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n  });\n});\n"],
    ['Python TestClient = FakeAppClient shadow', 'tests/test_tc_assign.py',
      'TestClient = FakeAppClient\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['Python class TestClient shadow', 'tests/test_tc_cls.py',
      'class TestClient:\n    def post(self, *a, **k): return type("R", (), {"status_code": 403})()\ndef test_csrf():\n    assert TestClient().post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['JS function fetch() shadow', 'test/fn-fetch.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nfunction fetch() { return Promise.resolve({ status: 403 }); }\ntest('csrf', async () => {\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\n"],
    ['httpx.MockTransport', 'tests/test_httpx_mock.py',
      'import httpx\ndef test_csrf():\n    c = httpx.Client(transport=httpx.MockTransport(lambda r: httpx.Response(403)))\n    assert c.post("http://test/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['file-scope leak: sqlite in test_smoke + stub in test_csrf', 'tests/test_leak.py',
      'import sqlite3\ndef test_smoke():\n    sqlite3.connect(":memory:").close()\ndef test_csrf():\n    class Stub:\n        def post(self, *a, **k): return type("R", (), {"status_code": 403})()\n    assert Stub().post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['vi.fn() mocked binary parser', 'test/mock-pdf.test.mjs',
      "import { vi } from 'vitest';\nimport test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('pdf', () => {\n  const parse = vi.fn(() => ({ blocked: true }));\n  assert.equal(parse(Buffer.from('%PDF-1.5 /ObjStm')).blocked, true);\n});\n"],
    // Round-2 anti-bypass regressions (R2-01..R2-24)
    ['R2-01 assertion msg embeds fake 403 + Origin', 'tests/test_r2_01.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).get("/health")\n    assert r.status_code == 200, "status_code == 403 Origin: https://evil.test"\n'],
    ['R2-02 parenthesized bare string no-op', 'tests/test_r2_02.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    ("assert r.status_code == 403; Origin: https://evil.test")\n    assert TestClient(app).get("/health").status_code == 200\n'],
    ['R2-03 JS assert msg embeds fake 403 + evil.test', 'test/r2-03.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  const r = await fetch('http://127.0.0.1/health');\n  assert.equal(r.status, 200, 'status === 403 https://evil.test');\n});\n"],
    ['R2-04 happy 200 + tautological status_code != 201', 'tests/test_r2_04.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).post("/health", headers={"Origin": "https://evil.test"})\n    assert r.status_code == 200\n    assert r.status_code != 201\n'],
    ['R2-05 permissive status_code in (403, 200) / or == 200', 'tests/test_r2_05.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    assert r.status_code in (403, 200)\n    assert r.status_code == 403 or r.status_code == 200\n'],
    ['R2-06 swallowed AssertionError via try/except pass', 'tests/test_r2_06.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    try:\n        assert r.status_code == 403\n    except AssertionError:\n        pass\n'],
    ['R2-06b swallowed JS try/catch', 'test/r2-06b.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  try { assert.equal(r.status, 403); } catch {}\n});\n"],
    ['R2-07 happy 200 OK checking revoked is False', 'tests/test_r2_07.py',
      'from fastapi.testclient import TestClient\ndef test_session(app):\n    r = TestClient(app).get("/session", headers={"Authorization": "Bearer valid"})\n    assert r.status_code == 200\n    assert r.json()["revoked"] is False\n'],
    ['R2-08 benign %PDF-1.4 + findings == []', 'tests/test_r2_08.py',
      'from src.records.service import inspect_pdf\ndef test_clean_pdf():\n    valid = b"%PDF-1.4\\n1 0 obj << >> endobj"\n    assert inspect_pdf(valid)["findings"] == []\n'],
    ['R2-09 benign ZipFile + macros == []', 'tests/test_r2_09.py',
      'import io, zipfile\nfrom src.records.service import inspect_xlsx\ndef test_clean_xlsx():\n    buf = io.BytesIO()\n    with zipfile.ZipFile(buf, "w") as zf: zf.writestr("xl/sheet1.xml", "<sheet/>")\n    assert inspect_xlsx(buf.getvalue())["macros"] == []\n'],
    ['R2-10 single-threaded SQLite PRAGMA busy_timeout', 'tests/test_r2_10.py',
      'import sqlite3\ndef test_db():\n    conn = sqlite3.connect(":memory:")\n    conn.execute("PRAGMA busy_timeout = 5000")\n    assert conn.execute("SELECT 1").fetchone() == (1,)\n'],
    ['R2-11 Python dead branch if not True: / while False:', 'tests/test_r2_11.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    assert TestClient(app).get("/health").status_code == 200\n    if not True:\n        assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n    while False:\n        assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['R2-12 JS dead branch if (!true) / while (false)', 'test/r2-12.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  assert.equal((await fetch('http://127.0.0.1/health')).status, 200);\n  if (!true) { assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403); }\n  while (false) { assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403); }\n});\n"],
    ['R2-13 uncalled Python lambda holding fake assert', 'tests/test_r2_13.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).get("/health")\n    dead = lambda: r.status_code == 403 and {"Origin": "https://evil.test"}\n    assert r.status_code == 200\n'],
    ['R2-14 multiline pytestmark skip list', 'tests/test_r2_14.py',
      'import pytest\nfrom fastapi.testclient import TestClient\npytestmark = [\n    pytest.mark.skip(reason="all")\n]\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['R2-15 unittest self.skipTest', 'tests/test_r2_15.py',
      'import unittest\nfrom fastapi.testclient import TestClient\nclass T(unittest.TestCase):\n    def test_csrf(self):\n        self.skipTest("todo")\n        self.assertEqual(TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code, 403)\n'],
    ['R2-16 Node { timeout: 5000, skip: true }', 'test/r2-16.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', { timeout: 5000, skip: true }, async () => {\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\n"],
    ['R2-17 Node { todo: true } and describe(..., { skip: true })', 'test/r2-17.test.mjs',
      "import { describe, it, test } from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', { todo: true }, async () => {\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\ndescribe('adv', { skip: true }, () => {\n  it('csrf2', async () => {\n    assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n  });\n});\n"],
    ['R2-18 Python requests = SimpleNamespace shadow', 'tests/test_r2_18.py',
      'from types import SimpleNamespace\nrequests = SimpleNamespace(post=lambda *a, **k: SimpleNamespace(status_code=403))\ndef test_csrf():\n    assert requests.post("http://127.0.0.1/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['R2-19 Python import alias FakeClient as TestClient', 'tests/test_r2_19.py',
      'from fake_client import FakeClient as TestClient\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['R2-20 JS destructuring const { fetch } = ...', 'test/r2-20.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nconst { fetch } = { fetch: async () => ({ status: 403 }) };\ntest('csrf', async () => {\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\n"],
    ['R2-21 Node t.mock.method(globalThis, fetch)', 'test/r2-21.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', async (t) => {\n  t.mock.method(globalThis, 'fetch', async () => ({ status: 403 }));\n  assert.equal((await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } })).status, 403);\n});\n"],
    ['R2-22 mixed happy TestClient + MagicMock faking 403', 'tests/test_r2_22.py',
      'from unittest.mock import MagicMock\nfrom fastapi.testclient import TestClient\ndef test_csrf(app):\n    assert TestClient(app).get("/health").status_code == 200\n    fake = MagicMock(return_value=MagicMock(status_code=403))\n    assert fake("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n'],
    ['R2-23 tautology self.assertIs(False, False) / strictEqual(!true, false)', 'tests/test_r2_23.py',
      'import unittest\nfrom fastapi.testclient import TestClient\nclass T(unittest.TestCase):\n    def test_csrf(self):\n        r = TestClient(app).post("/health", headers={"Origin": "https://evil.test"})\n        self.assertEqual(r.status_code, 200)\n        self.assertIs(False, False)\n'],
    ['R2-24 CLI trivial binary subprocess.run(["false"])', 'tests/test_r2_24.py',
      'import subprocess\ndef test_cli(tmp_path):\n    r = subprocess.run(["false"], env={"HOME": str(tmp_path)})\n    assert r.returncode != 0\n'],
    // Round-3 bypass regressions (R2-06a/b, R3-BYP-01..08)
    ['R2-06a Python contextlib.suppress(AssertionError)', 'tests/test_r3_supp.py',
      'import contextlib\nfrom fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    with contextlib.suppress(AssertionError):\n        assert r.status_code == 403\n'],
    ['R3-BYP-01a Python non-asserted if r.status_code == 403: pass', 'tests/test_r3_byp01_py.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    if r.status_code == 403:\n        pass\n'],
    ['R3-BYP-01b JS non-asserted if (res.status === 401) {}', 'test/r3-byp01-js.test.mjs',
      "import test from 'node:test';\ntest('ok', async () => {\n  const res = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  if (res.status === 401) {}\n});\n"],
    ['R3-BYP-02 multi-line K&R JS swallowed try/catch', 'test/r3-byp02.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  const res = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  try {\n    assert.equal(res.status, 403);\n  } catch (e) {\n  }\n});\n"],
    ['R3-BYP-03 inverted empty findings == [] on /JavaScript PDF', 'tests/test_r3_byp03.py',
      'from src.records.service import inspect_pdf\ndef test_pdf():\n    assert inspect_pdf(b"%PDF-1.4\\n/JavaScript")["findings"] == []\n'],
    ['R3-BYP-04a runtime tautology assert (not True) is False', 'tests/test_r3_byp04a.py',
      'from fastapi.testclient import TestClient\ndef test_ok(app):\n    TestClient(app).post("/grant", json={"early_exercise_allowed": "false"})\n    assert (not True) is False\n'],
    ['R3-BYP-04b runtime tautology assert True is True on corrupt DB', 'tests/test_r3_byp04b.py',
      'from pathlib import Path\nfrom src.ledger.service import create_app\ndef test_db(tmp_path):\n    p = tmp_path / "app.sqlite"\n    p.write_bytes(b"CORRUPT")\n    create_app(p)\n    assert True is True\n'],
    ['R3-BYP-05 JS ESM import { fetch } from ./fake-fetch.mjs', 'test/r3-byp05.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { fetch } from './fake-fetch.mjs';\ntest('csrf', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n});\n"],
    ['R3-BYP-06 JS spawnSync("sh", ["-c", "exit 1"])', 'test/r3-byp06.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { spawnSync } from 'node:child_process';\nimport { mkdtempSync } from 'node:fs';\ntest('cli', () => {\n  const home = mkdtempSync('/tmp/h-');\n  const r = spawnSync('sh', ['-c', 'exit 1'], { env: { HOME: home } });\n  assert.notEqual(r.status, 0);\n});\n"],
    ['R3-BYP-08 CJS const { createServer } = require("./fake-http.mjs")', 'test/r3-byp08.test.cjs',
      "const test = require('node:test');\nconst assert = require('node:assert/strict');\nconst { createServer } = require('./fake-http.mjs');\ntest('csrf', async () => {\n  const s = createServer(); s.listen(0);\n  assert.equal(403, s.status);\n});\n"],
    // Round-4 regressions (R4-01..R4-03)
    ['R4-01b happy-path title containing "function" + multiline options + body.revoked === false', 'test/r4-01b.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('session function checks happy path', {\n  timeout: 5000,\n}, async () => {\n  const res = await fetch('http://127.0.0.1:8080/session');\n  const body = await res.json();\n  assert.equal(body.revoked, false);\n});\n"],
    ['R4-02 single-line try with inner { method: "POST" } + swallowed catch (e) {}', 'test/r4-02.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('ok', async () => {\n  try { const res = await fetch('http://127.0.0.1:8080/admin', { method: 'POST' }); assert.equal(res.status, 403); } catch (e) {}\n});\n"],
    ['R4-03a default ESM import fetch from ./fake-fetch.mjs', 'test/r4-03a.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport fetch from './fake-fetch.mjs';\ntest('csrf', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n});\n"],
    ['R4-03b multiline CJS destructuring require(./fake-http.mjs)', 'test/r4-03b.test.cjs',
      "const test = require('node:test');\nconst assert = require('node:assert/strict');\nconst {\n  createServer,\n} = require('./fake-http.mjs');\ntest('csrf', async () => {\n  const s = createServer(); s.listen(0);\n  assert.equal(s.status, 403);\n});\n"],
  ];

  for (const [label, filePath, code] of bypasses) {
    const adv = detectAdversarialProbesInTest(filePath, code);
    assert.equal(adv.hasAdversarialProbes, false, `${label}: detectAdversarialProbesInTest MUST block (${JSON.stringify(adv)})`);
    const rh = detectRealHostProbesInTest(filePath, code);
    assert.equal(rh.hasAdversarialProbes, false, `${label}: detectRealHostProbesInTest MUST block (${JSON.stringify(rh)})`);
  }

  // Valid JS adversarial test containing regex literal `/\/*/` MUST still pass (E12 regression)
  const validJsRegex = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    'const slashRe = /\\/*/;',
    "test('csrf rejected', async () => {",
    "  const r = await fetch('http://127.0.0.1/grant', { method: 'POST', headers: { Origin: 'https://evil.test' } });",
    '  assert.equal(r.status, 403);',
    '  assert.ok(slashRe.test("/"));',
    '});',
  ].join('\n');
  const jsReAdv = detectAdversarialProbesInTest('test/csrf-regex.test.mjs', validJsRegex);
  assert.equal(jsReAdv.hasAdversarialProbes, true);
  assert.ok(jsReAdv.surfaces.includes('http-auth-browser-mcp'));

  // Round-3 legitimate idiom regressions (R3-FN-01..R3-FN-10 MUST NOT false-negative!)
  const legitIdioms = [
    ['R3-FN-01 CJS require("node:http")', 'test/cjs-http.test.cjs',
      "const test = require('node:test');\nconst assert = require('node:assert/strict');\nconst { createServer } = require('node:http');\ntest('csrf', async () => {\n  const s = createServer((req, res) => { res.statusCode = 403; res.end(); });\n  s.listen(0);\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n});\n"],
    ['R3-FN-04a async function + t.after(() => ...)', 'test/fn-arrow.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', async function (t) {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n  t.after(() => {});\n});\n"],
    ['R3-FN-04b async arrow + nested function()', 'test/arrow-fn.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n  setTimeout(function cleanup() {}, 0);\n});\n"],
    ['R3-FN-05 multi-line Python def test_...(', 'tests/test_ml_def.py',
      'from fastapi.testclient import TestClient\ndef test_csrf(\n    app,\n    tmp_path,\n):\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    assert r.status_code == 403\n'],
    ['R3-FN-07 top-level await test(...)', 'test/await-test.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nawait test('csrf', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { headers: { Origin: 'https://evil.test' } });\n  assert.equal(r.status, 403);\n});\n"],
    ['R3-FN-08 JSON body { todo: "buy milk" } not dropped as skip', 'test/json-todo.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('csrf', async () => {\n  const r = await fetch('http://127.0.0.1/grant', { method: 'POST', headers: { Origin: 'https://evil.test' }, body: JSON.stringify({ todo: 'buy milk' }) });\n  assert.equal(r.status, 403);\n});\n"],
    ['R3-FN-10 Python local requests = [] not shadowed', 'tests/test_req_list.py',
      'from fastapi.testclient import TestClient\ndef test_csrf(app):\n    requests = []\n    r = TestClient(app).post("/grant", headers={"Origin": "https://evil.test"})\n    requests.append(r)\n    assert r.status_code == 403\n'],
    ['R4-01a title containing "function" + multiline options + adversarial PDF parser', 'test/r4-01a.test.mjs',
      "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { inspectPdf } from '../src/records/parser.mjs';\ntest('parser function blocks evil pdf', {\n  timeout: 5000,\n}, () => {\n  const buf = Buffer.from('%PDF-1.4\\n/JavaScript');\n  assert.equal(inspectPdf(buf).blocked, true);\n});\n"],
  ];
  for (const [label, filePath, code] of legitIdioms) {
    assert.equal(detectAdversarialProbesInTest(filePath, code).hasAdversarialProbes, true, `${label}: MUST PASS (no false negative)`);
  }

  // Linear O(N) performance on 100KB hostile input
  const huge = `from fastapi.testclient import TestClient\n# ${'csrf ../ '.repeat(12000)}\ndef test_ok(app):\n    assert TestClient(app).get("/health").status_code == 200\n`;
  const t0 = performance.now();
  assert.equal(detectAdversarialProbesInTest('tests/test_perf.py', huge).hasAdversarialProbes, false);
  assert.ok(performance.now() - t0 < 250);
});

test('#3633 end-to-end pdd prove & policy: Case A fails closed (incl decoy file, multi-module gap, fake replay-evidence.json, metadata-free policy), Case B passes with split, Case C has 0 regressions', (t) => {
  const nodeBin = JSON.stringify(process.execPath);
  const pyRun = 'python3 -m unittest discover -s tests -p "test_*.py"';

  const repo = initRepo(t, 'pdd-3633-e2e-');
  writeFile(repo, 'pdd.json', JSON.stringify({
    verify: {
      test: pyRun,
      paths: [{ id: 'native-adapters', when: ['src/**'], run: pyRun }],
    },
  }, null, 2) + '\n');
  writeFile(repo, 'prompts/ledger/service.prompt.md', [
    '---',
    'kind: native-only',
    'reason: HTTP routes, SQLite WAL persistence, and PDF/XLSX upload inspection.',
    '---',
    '# Ledger & Records Adapter',
    '## Boundary contract',
    'Exposes HTTP routes (CSRF/Origin, bearer auth, CSP script-src none HTML form), SQLite WAL storage, and PDF/XLSX redaction parser.',
    '## Error mapping',
    'Returns 401/403 on forged/unauthenticated access, degrades safely on corrupt SQLite.',
    '## Real-host verification cases',
    'Real-host adversarial probes against HTTP routes, SQLite DR, and malformed PDF/XLSX bytes.',
    '## Dependencies',
    'None.',
  ].join('\n') + '\n');
  writeFile(repo, 'src/ledger/__init__.py', '');
  writeFile(repo, 'src/ledger/service.py', [
    '# Prompt: prompts/ledger/service.prompt.md',
    'import io, sqlite3, zipfile',
    'def create_app(db_path):',
    '    try:',
    '        conn = sqlite3.connect(str(db_path)); conn.execute("CREATE TABLE IF NOT EXISTS t(id INT)"); return {"ledger_usable": True, "conn": conn}',
    '    except sqlite3.DatabaseError: return {"ledger_usable": False, "conn": None}',
    'def inspect_pdf(b): return {"safe": b"/ObjStm" not in b and b"/Fl#61teDecode" not in b}',
    'def inspect_xlsx(b):',
    '    with zipfile.ZipFile(io.BytesIO(b)) as z: return {"safe": all(b"<!ENTITY" not in z.read(n) and b"=HYPERLINK" not in z.read(n) for n in z.namelist())}',
  ].join('\n') + '\n');
  writeFile(repo, 'tests/ledger_vectors.json', JSON.stringify({ cases: [{ name: 'simulated_grant', ok: true }] }, null, 2) + '\n');
  writeFile(repo, 'tests/test_smoke.py', [
    'import sqlite3, tempfile, unittest',
    'from pathlib import Path',
    'from src.ledger.service import create_app',
    'class T(unittest.TestCase):',
    '    def test_happy_smoke(self):',
    '        with tempfile.TemporaryDirectory() as td:',
    '            app = create_app(Path(td) / "app.sqlite")',
    '            conn = sqlite3.connect(str(Path(td) / "app.sqlite"))',
    '            self.assertTrue(app["ledger_usable"])',
    '            conn.close(); app["conn"].close()',
  ].join('\n') + '\n');
  commitAll(repo, 'base');

  execFileSync('git', ['checkout', '-q', '-b', 'feat-native-change'], { cwd: repo });
  writeFile(repo, 'src/ledger/service.py', [
    '# Prompt: prompts/ledger/service.prompt.md',
    'import io, sqlite3, zipfile',
    'def create_app(db_path):',
    '    try:',
    '        conn = sqlite3.connect(str(db_path)); conn.execute("CREATE TABLE IF NOT EXISTS t(id INT)"); return {"ledger_usable": True, "conn": conn}',
    '    except sqlite3.DatabaseError: return {"ledger_usable": False, "conn": None}',
    'def inspect_pdf(b): return {"safe": b"/ObjStm" not in b and b"/Fl#61teDecode" not in b}',
    'def inspect_xlsx(b):',
    '    with zipfile.ZipFile(io.BytesIO(b)) as z: return {"safe": all(b"<!ENTITY" not in z.read(n) and b"=HYPERLINK" not in z.read(n) for n in z.namelist())}',
    '# modified',
  ].join('\n') + '\n');
  // Spoofed replay-evidence.json MUST NOT bypass gate
  writeFile(repo, 'replay-evidence.json', JSON.stringify({ adversarial_real_host: { status: 'proved', passed: 99 } }) + '\n');

  const caseA = runProve({ cwd: repo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(caseA.exitCode, EXIT_NOT_PROVED);
  assert.equal(caseA.outcome, OUTCOME_NOT_PROVED);
  assert.equal(caseA.receipt.evidence.simulated_vectors.totalFiles, 1);
  assert.equal(caseA.receipt.evidence.simulated_vectors.executesNativeOnlyBoundaries, false);
  assert.equal(caseA.receipt.evidence.adversarial_real_host.status, 'happy-path-only');
  assert.deepEqual(caseA.receipt.evidence.adversarial_real_host.missingSurfaces, ['binary-parser', 'http-auth-browser-mcp', 'storage-dr']);
  assert.ok(caseA.receipt.notProvedReasons.some((r) => r.includes('[native-only-adversarial-missing]')));

  // Unexecuted decoy file (E4): pdd.json runs only tests/test_smoke.py -> decoy never executed -> STILL FAILS CLOSED!
  rmSync(join(repo, 'replay-evidence.json'), { force: true });
  const decoyRepo = initRepo(t, 'pdd-3633-decoy-');
  writeFile(decoyRepo, 'pdd.json', JSON.stringify({
    verify: { test: 'python3 -m unittest tests/test_smoke.py', paths: [{ id: 's', when: ['src/**'], run: 'python3 -m unittest tests/test_smoke.py' }] },
  }) + '\n');
  writeFile(decoyRepo, 'prompts/api/routes.prompt.md', '---\nkind: native-only\nreason: HTTP API routes.\n---\n# API\n## Boundary contract\nHTTP routes.\n## Error mapping\n401/403.\n## Real-host verification\nHTTP probes.\n## Dependencies\nNone.\n');
  writeFile(decoyRepo, 'src/api/routes.py', '# Prompt: prompts/api/routes.prompt.md\nfrom fastapi import APIRouter\n');
  writeFile(decoyRepo, 'tests/test_smoke.py', 'import unittest\nclass T(unittest.TestCase):\n    def test_ok(self): self.assertTrue(True)\n');
  commitAll(decoyRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-decoy'], { cwd: decoyRepo });
  writeFile(decoyRepo, 'src/api/routes.py', '# Prompt: prompts/api/routes.prompt.md\nfrom fastapi import APIRouter\n# change\n');
  writeFile(decoyRepo, 'tests/test_never_executed_decoy.py', 'from fastapi.testclient import TestClient\nfrom src.api.routes import *\nraise RuntimeError("never runs")\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n');
  const decoyRes = runProve({ cwd: decoyRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(decoyRes.exitCode, EXIT_NOT_PROVED, 'unexecuted decoy file MUST NOT satisfy adversarial gate');

  // Multi-module bypass (E3): 2 touched native-only modules (auth tested, billing untested) -> FAILS CLOSED!
  const multiRepo = initRepo(t, 'pdd-3633-multi-');
  writeFile(multiRepo, 'pdd.json', JSON.stringify({
    verify: { test: `${nodeBin} --test test/auth.test.mjs`, paths: [{ id: 's', when: ['src/**'], run: `${nodeBin} --test test/auth.test.mjs` }] },
  }) + '\n');
  writeFile(multiRepo, 'prompts/auth.prompt.md', '---\nkind: native-only\nreason: HTTP auth routes.\n---\n# Auth\n## Boundary contract\nHTTP routes.\n## Error mapping\n401.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(multiRepo, 'prompts/billing.prompt.md', '---\nkind: native-only\nreason: HTTP billing routes.\n---\n# Billing\n## Boundary contract\nHTTP routes.\n## Error mapping\n401.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(multiRepo, 'src/auth/routes.mjs', '// Prompt: prompts/auth.prompt.md\nexport const auth = 1;\n');
  writeFile(multiRepo, 'src/billing/routes.mjs', '// Prompt: prompts/billing.prompt.md\nexport const bill = 1;\n');
  writeFile(multiRepo, 'test/auth.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { auth } from '../src/auth/routes.mjs';\ntest('auth', async () => { assert.equal(auth, 1); if (auth === 999) { const r = await fetch('http://127.0.0.1/auth', { headers: { Origin: 'https://evil.test' } }); assert.equal(r.status, 403); } });\n");
  commitAll(multiRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-multi'], { cwd: multiRepo });
  writeFile(multiRepo, 'src/auth/routes.mjs', '// Prompt: prompts/auth.prompt.md\nexport const auth = 2;\n');
  writeFile(multiRepo, 'src/billing/routes.mjs', '// Prompt: prompts/billing.prompt.md\nexport const bill = 2;\n');
  writeFile(multiRepo, 'test/auth.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { auth } from '../src/auth/routes.mjs';\ntest('auth', async () => { assert.equal(auth, 2); });\n");
  const multiRes = runProve({ cwd: multiRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(multiRes.exitCode, EXIT_NOT_PROVED, 'untested second native-only module MUST fail closed');
  assert.ok(multiRes.receipt.notProvedReasons.some((r) => r.includes('src/billing/routes.mjs')));

  // Policy E5: metadata-free real-host-smoke on concrete native-only surface MUST fail closed
  const metaFreeBlocked = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/api/routes.py'],
    nativeOnlyFiles: ['src/api/routes.py'],
    offlinePassed: true,
    e2eChecks: [{ kind: 'real-host-smoke', command: 'pytest', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0 }],
  });
  assert.equal(metaFreeBlocked.eligible, false);
  assert.equal(metaFreeBlocked.bucket, 3);
  assert.equal(metaFreeBlocked.waitKind, 'needs-real-host-smoke');

  // Case B: real executable adversarial tests targeting src/ledger/service.py across all 3 surfaces -> Proved (exit 0)!
  writeFile(repo, 'tests/test_adversarial.py', [
    'import io, tempfile, unittest, urllib.request, zipfile',
    'from pathlib import Path',
    'from src.ledger.service import create_app, inspect_pdf, inspect_xlsx',
    'class TestAdversarial(unittest.TestCase):',
    '    def test_http_auth_csrf_coercion_traversal(self):',
    '        with self.assertRaises(Exception):',
    '            urllib.request.urlopen(urllib.request.Request("http://127.0.0.1:1/ledger/../../escaped_pwned", data=b\'{"early_exercise_allowed": "false"}\', headers={"Origin": "https://evil.example", "Authorization": "Bearer forged"}, method="POST"))',
    '    def test_binary_pdf_and_xlsx(self):',
    '        evil_pdf = b"%PDF-1.5\\n1 0 obj << /Type /ObjStm /Filter /Fl#61teDecode >> endobj"',
    '        self.assertIs(inspect_pdf(evil_pdf)["safe"], False)',
    '        buf = io.BytesIO()',
    '        with zipfile.ZipFile(buf, "w") as zf:',
    '            zf.writestr("xl/sheet1.xml", "<!ENTITY xxe SYSTEM \'file:///etc/passwd\'>=HYPERLINK(\'http://evil\')")',
    '        self.assertIs(inspect_xlsx(buf.getvalue())["safe"], False)',
    '    def test_corrupt_sqlite_dr(self):',
    '        with tempfile.TemporaryDirectory() as td:',
    '            db_path = Path(td) / "continuity.sqlite"',
    '            db_path.write_bytes(b"CORRUPT_NOT_SQLITE" * 32)',
    '            app = create_app(db_path)',
    '            self.assertIs(app["ledger_usable"], False)',
  ].join('\n') + '\n');
  const caseBJsonOut = makeSink();
  const caseB = runProve({ cwd: repo, json: true }, { stdout: caseBJsonOut, stderr: makeSink() });
  assert.equal(caseB.exitCode, EXIT_PROVED, caseBJsonOut.text);
  assert.equal(caseB.receipt.evidence.simulated_vectors.totalFiles, 1);
  assert.equal(caseB.receipt.evidence.adversarial_real_host.status, 'proved');
  assert.deepEqual(caseB.receipt.evidence.adversarial_real_host.coveredSurfaces, ['binary-parser', 'http-auth-browser-mcp', 'storage-dr']);
  const caseBHumanOut = makeSink();
  assert.equal(runProve({ cwd: repo, json: false }, { stdout: caseBHumanOut, stderr: makeSink() }).exitCode, EXIT_PROVED);
  assert.match(caseBHumanOut.text, /simulated_vectors=1 \(simulated ports only\)/);
  assert.match(caseBHumanOut.text, /Adversarial real-host: proved \(3\/3 surface\(s\) covered\)/);

  // Case C: Pure-logic repo with ZERO kind: native-only modules -> 0 regressions!
  const pureRepo = initRepo(t, 'pdd-3633-pure-');
  writeFile(pureRepo, 'pdd.json', JSON.stringify({
    verify: { test: `${nodeBin} -e "process.exit(0)"`, paths: [{ id: 'math', when: ['src/**'], run: `${nodeBin} -e "process.exit(0)"` }] },
  }) + '\n');
  writeFile(pureRepo, 'prompts/math.prompt.md', '# Math\n\nOwn `src/math.mjs`.\n\n## Dependencies\nNone.\n');
  writeFile(pureRepo, 'src/math.mjs', '// Prompt: prompts/math.prompt.md\nexport const add = (a, b) => a + b;\n');
  commitAll(pureRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-math'], { cwd: pureRepo });
  writeFile(pureRepo, 'src/math.mjs', '// Prompt: prompts/math.prompt.md\nexport const add = (a, b) => Number(a) + Number(b);\n');
  const caseC = runProve({ cwd: pureRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(caseC.exitCode, EXIT_PROVED);
  assert.equal(caseC.receipt.evidence.adversarial_real_host.applicable, false);
  assert.equal(caseC.receipt.evidence.adversarial_real_host.status, 'not-applicable');

  // R2-25..R2-30 end-to-end & policy regressions
  // R2-25: directory-scoped runner (tests/unit) MUST ignore decoy in tests/decoy/
  const dirDecoy = initRepo(t, 'pdd-3633-r2-25-');
  writeFile(dirDecoy, 'pdd.json', JSON.stringify({
    verify: { test: 'python3 -m unittest discover -s tests/unit -p "test_*.py"', paths: [{ id: 's', when: ['src/**'], run: 'python3 -m unittest discover -s tests/unit -p "test_*.py"' }] },
  }) + '\n');
  writeFile(dirDecoy, 'prompts/api.prompt.md', '---\nkind: native-only\nreason: HTTP API.\n---\n# API\n## Boundary contract\nHTTP routes.\n## Error mapping\n403.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(dirDecoy, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\nfrom fastapi import APIRouter\n');
  writeFile(dirDecoy, 'tests/unit/test_ok.py', 'import unittest\nclass T(unittest.TestCase):\n    def test_ok(self): self.assertTrue(True)\n');
  commitAll(dirDecoy, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-dir'], { cwd: dirDecoy });
  writeFile(dirDecoy, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\nfrom fastapi import APIRouter\n# edit\n');
  writeFile(dirDecoy, 'tests/decoy/test_never_runs.py', 'from fastapi.testclient import TestClient\nfrom src.api.routes import *\nraise RuntimeError("never runs")\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n');
  assert.equal(runProve({ cwd: dirDecoy, json: true }, { stdout: makeSink(), stderr: makeSink() }).exitCode, EXIT_NOT_PROVED);

  // R2-26: dotted unittest module / python3 --version MUST NOT credit unexecuted decoy
  const dotRepo = initRepo(t, 'pdd-3633-r2-26-');
  writeFile(dotRepo, 'pdd.json', JSON.stringify({
    verify: { test: 'python3 -m unittest tests.test_smoke', paths: [{ id: 's', when: ['src/**'], run: 'python3 -m unittest tests.test_smoke' }] },
  }) + '\n');
  writeFile(dotRepo, 'prompts/api.prompt.md', '---\nkind: native-only\nreason: HTTP API.\n---\n# API\n## Boundary contract\nHTTP routes.\n## Error mapping\n403.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(dotRepo, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\nfrom fastapi import APIRouter\n');
  writeFile(dotRepo, 'tests/__init__.py', '');
  writeFile(dotRepo, 'tests/test_smoke.py', 'import unittest\nclass T(unittest.TestCase):\n    def test_ok(self): self.assertTrue(True)\n');
  commitAll(dotRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-dot'], { cwd: dotRepo });
  writeFile(dotRepo, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\nfrom fastapi import APIRouter\n# edit\n');
  writeFile(dotRepo, 'tests/test_decoy.py', 'from fastapi.testclient import TestClient\nfrom src.api.routes import *\nraise RuntimeError("never runs")\ndef test_csrf(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n');
  assert.equal(runProve({ cwd: dotRepo, json: true }, { stdout: makeSink(), stderr: makeSink() }).exitCode, EXIT_NOT_PROVED);

  // R2-27: test title mentioning sibling module "billing" MUST NOT bind src/billing/routes.mjs
  writeFile(multiRepo, 'test/auth.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { auth } from '../src/auth/routes.mjs';\ntest('auth and billing csrf', async () => {\n  assert.equal(auth, 2);\n  if (auth === 999) { const r = await fetch('http://127.0.0.1/auth', { headers: { Origin: 'https://evil.test' } }); assert.equal(r.status, 403); }\n});\n");
  assert.equal(runProve({ cwd: multiRepo, json: true }, { stdout: makeSink(), stderr: makeSink() }).exitCode, EXIT_NOT_PROVED);

  // R2-28: policy with 2 nativeOnlyFiles + 1 adv check + 1 non-adv local-server-or-db check MUST fail closed
  const r2Policy = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/orders/routes.py', 'src/billing/routes.py'],
    nativeOnlyFiles: ['src/orders/routes.py', 'src/billing/routes.py'],
    offlinePassed: true,
    e2eChecks: [
      { kind: 'real-host-smoke', command: 'pytest tests/test_orders.py', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0, adversarialSurfaces: ['http-auth-browser-mcp'], adversarialProbes: ['csrf-origin'] },
      { kind: 'local-server-or-db', command: 'pytest tests/test_orders_http.py', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0 },
    ],
  });
  assert.equal(r2Policy.eligible, false);
  assert.equal(r2Policy.waitKind, 'needs-real-host-smoke');

  // R2-29: conftest.py TestClient fixture declared in test_csrf(client) but never invoked MUST NOT satisfy gate
  const fixRepo = initRepo(t, 'pdd-3633-r2-29-');
  writeFile(fixRepo, 'pdd.json', JSON.stringify({
    verify: { test: 'python3 -m unittest discover -s tests -p "test_*.py"', paths: [{ id: 's', when: ['src/**'], run: 'python3 -m unittest discover -s tests -p "test_*.py"' }] },
  }) + '\n');
  writeFile(fixRepo, 'prompts/api.prompt.md', '---\nkind: native-only\nreason: HTTP API.\n---\n# API\n## Boundary contract\nHTTP routes.\n## Error mapping\n403.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(fixRepo, 'src/api/__init__.py', '');
  writeFile(fixRepo, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\ndef route(): return 200\n');
  writeFile(fixRepo, 'tests/conftest.py', 'import pytest\nfrom fastapi.testclient import TestClient\n@pytest.fixture\ndef client(): return TestClient(object())\n');
  writeFile(fixRepo, 'tests/test_api.py', 'import unittest\nfrom src.api.routes import route\nclass T(unittest.TestCase):\n    def test_ok(self): self.assertEqual(route(), 200)\n');
  commitAll(fixRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-fix'], { cwd: fixRepo });
  writeFile(fixRepo, 'src/api/routes.py', '# Prompt: prompts/api.prompt.md\ndef route(): return 201\n');
  writeFile(fixRepo, 'tests/test_api.py', 'import unittest\nfrom src.api.routes import route\ndef test_csrf(client):\n    class Stub:\n        def post(self, *a, **k): return type("R", (), {"status_code": 403})()\n    assert Stub().post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\nclass T(unittest.TestCase):\n    def test_ok(self): self.assertEqual(route(), 201)\n');
  assert.equal(runProve({ cwd: fixRepo, json: true }, { stdout: makeSink(), stderr: makeSink() }).exitCode, EXIT_NOT_PROVED);

  // R2-30: legitimate repo with verify.test = "npm run test:unit" MUST PASS (no false negative!)
  const npmUnitRepo = initRepo(t, 'pdd-3633-r2-30-');
  writeFile(npmUnitRepo, 'package.json', JSON.stringify({
    name: 'npm-unit-repro',
    type: 'module',
    scripts: { 'test:unit': `${nodeBin} --test test/csrf.test.mjs` },
  }, null, 2) + '\n');
  writeFile(npmUnitRepo, 'pdd.json', JSON.stringify({
    verify: { test: 'npm run test:unit', paths: [{ id: 'api', when: ['src/**'], run: 'npm run test:unit' }] },
  }) + '\n');
  writeFile(npmUnitRepo, 'prompts/api.prompt.md', '---\nkind: native-only\nreason: HTTP API.\n---\n# API\n## Boundary contract\nHTTP routes.\n## Error mapping\n403.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(npmUnitRepo, 'src/api/routes.mjs', '// Prompt: prompts/api.prompt.md\nexport const checkOrigin = (o) => o === "https://app.local";\n');
  writeFile(npmUnitRepo, 'test/csrf.test.mjs', [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { checkOrigin } from '../src/api/routes.mjs';",
    "test('rejects evil origin', async () => {",
    "  assert.equal(checkOrigin('https://evil.test'), false);",
    "  await assert.rejects(fetch('http://127.0.0.1:1/grant', { method: 'POST', headers: { Origin: 'https://evil.test' } }));",
    '});',
  ].join('\n') + '\n');
  commitAll(npmUnitRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-npm-unit'], { cwd: npmUnitRepo });
  writeFile(npmUnitRepo, 'src/api/routes.mjs', '// Prompt: prompts/api.prompt.md\nexport const checkOrigin = (o) => o === "https://app.local" || false;\n');
  const npmUnitRes = runProve({ cwd: npmUnitRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(npmUnitRes.exitCode, EXIT_PROVED, `R2-30 npm run test:unit must pass: ${JSON.stringify(npmUnitRes.receipt.notProvedReasons)}`);
  assert.equal(npmUnitRes.receipt.evidence.adversarial_real_host.status, 'proved');

  // R3-FN-06 (multi-line ESM import) + R3-FN-09 (NODE_ENV=test npm test) MUST PASS!
  const mlImportRepo = initRepo(t, 'pdd-3633-r3-fn06-');
  writeFile(mlImportRepo, 'package.json', JSON.stringify({ name: 'ml-imp', type: 'module', scripts: { test: `${nodeBin} --test test/security.test.mjs` } }, null, 2) + '\n');
  writeFile(mlImportRepo, 'pdd.json', JSON.stringify({ verify: { test: 'NODE_ENV=test npm test', paths: [{ id: 'b', when: ['src/**'], run: 'NODE_ENV=test npm test' }] } }) + '\n');
  writeFile(mlImportRepo, 'prompts/billing.prompt.md', '---\nkind: native-only\nreason: HTTP billing.\n---\n# Billing\n## Boundary contract\nHTTP routes.\n## Error mapping\n403.\n## Real-host verification\nHTTP.\n## Dependencies\nNone.\n');
  writeFile(mlImportRepo, 'src/billing.mjs', '// Prompt: prompts/billing.prompt.md\nexport const bill = () => 1;\n');
  writeFile(mlImportRepo, 'test/security.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport {\n  bill,\n} from '../src/billing.mjs';\ntest('csrf', async () => {\n  assert.equal(bill(), 1);\n  await assert.rejects(fetch('http://127.0.0.1:1/bill', { method: 'POST', headers: { Origin: 'https://evil.test' } }));\n});\n");
  commitAll(mlImportRepo, 'base');
  execFileSync('git', ['checkout', '-q', '-b', 'feat-ml'], { cwd: mlImportRepo });
  writeFile(mlImportRepo, 'src/billing.mjs', '// Prompt: prompts/billing.prompt.md\nexport const bill = () => 1 + 0;\n');
  const mlRes = runProve({ cwd: mlImportRepo, json: true }, { stdout: makeSink(), stderr: makeSink() });
  assert.equal(mlRes.exitCode, EXIT_PROVED, `R3-FN-06/09 must pass: ${JSON.stringify(mlRes.receipt.notProvedReasons)}`);

  // R3-BYP-07: same-file pytest nodeid `tests/test_auth.py::test_smoke` MUST NOT credit unexecuted `test_adv` in same file
  writeFile(fixRepo, 'tests/test_auth.py', 'from fastapi.testclient import TestClient\nfrom src.api.routes import route\ndef test_smoke(app):\n    assert TestClient(app).get("/health").status_code == 200\ndef test_adv_never_executed(app):\n    assert TestClient(app).post("/grant", headers={"Origin": "https://evil.test"}).status_code == 403\n');
  const nodeIdEv2 = inspectAdversarialBoundaryEvidence({
    root: fixRepo,
    touchedFiles: ['src/api/routes.py'],
    repoFiles: ['prompts/api.prompt.md', 'src/api/routes.py', 'tests/test_auth.py'],
    testResult: { ok: true, command: 'pytest tests/test_auth.py::test_smoke' },
  });
  assert.notEqual(nodeIdEv2.adversarial_real_host.status, 'proved', 'same-file pytest ::test_smoke MUST NOT credit unexecuted test_adv_never_executed');
});
