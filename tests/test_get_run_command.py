import pytest
import os
import shlex
import subprocess
import tempfile
from pathlib import Path
from pdd.get_run_command import (
    get_run_command,
    get_run_command_for_file,
    shell_safe_substitute,
)

# Mock CSV data with run_command column
mock_csv_data = """language,comment,extension,run_command
Python,#,.py,python {file}
JavaScript,//,.js,node {file}
TypeScript,//,.ts,npx tsx {file}
Go,//,.go,go run {file}
Ruby,#,.rb,ruby {file}
JSON,del,.json,
Markdown,del,.md,
"""

@pytest.fixture
def mock_csv_file(tmp_path):
    """Creates a temporary CSV file with mock data for testing."""
    data_dir = tmp_path / "data"
    data_dir.mkdir(exist_ok=True)
    csv_file = data_dir / "language_format.csv"
    csv_file.write_text(mock_csv_data)
    return csv_file

@pytest.fixture
def mock_environment(monkeypatch, tmp_path):
    """Mocks the environment variable PDD_PATH to point to a temporary path."""
    monkeypatch.setenv("PDD_PATH", str(tmp_path))


class TestGetRunCommand:
    """Tests for get_run_command function."""

    def test_get_run_command_python(self, mock_environment, mock_csv_file):
        """Tests get_run_command for Python files."""
        assert get_run_command('.py') == 'python {file}'

    def test_get_run_command_javascript(self, mock_environment, mock_csv_file):
        """Tests get_run_command for JavaScript files."""
        assert get_run_command('.js') == 'node {file}'

    def test_get_run_command_typescript(self, mock_environment, mock_csv_file):
        """Tests get_run_command for TypeScript files."""
        assert get_run_command('.ts') == 'npx tsx {file}'

    def test_get_run_command_go(self, mock_environment, mock_csv_file):
        """Tests get_run_command for Go files."""
        assert get_run_command('.go') == 'go run {file}'

    def test_get_run_command_without_dot(self, mock_environment, mock_csv_file):
        """Tests get_run_command with extension without leading dot."""
        assert get_run_command('py') == 'python {file}'

    def test_get_run_command_case_insensitive(self, mock_environment, mock_csv_file):
        """Tests get_run_command for case insensitivity."""
        assert get_run_command('.PY') == 'python {file}'
        assert get_run_command('.Js') == 'node {file}'

    def test_get_run_command_no_run_command(self, mock_environment, mock_csv_file):
        """Tests get_run_command for languages without run commands."""
        assert get_run_command('.json') == ''
        assert get_run_command('.md') == ''

    def test_get_run_command_not_found(self, mock_environment, mock_csv_file):
        """Tests get_run_command with an extension not in the CSV."""
        assert get_run_command('.xyz') == ''

    def test_get_run_command_empty_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command with an empty extension."""
        assert get_run_command('') == ''

    def test_get_run_command_missing_environment_variable(self, monkeypatch):
        """Tests get_run_command when PDD_PATH is not set."""
        monkeypatch.delenv("PDD_PATH", raising=False)
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            get_run_command('.py')

    def test_get_run_command_file_not_found(self, mock_environment, tmp_path):
        """Tests get_run_command when CSV file is not found."""
        assert get_run_command('.py') == ''


class TestGetRunCommandForFile:
    """Tests for get_run_command_for_file function."""

    def test_get_run_command_for_python_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for Python files."""
        assert get_run_command_for_file('/path/to/script.py') == 'python /path/to/script.py'

    def test_get_run_command_for_javascript_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for JavaScript files."""
        assert get_run_command_for_file('/path/to/app.js') == 'node /path/to/app.js'

    def test_get_run_command_for_go_file(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for Go files."""
        assert get_run_command_for_file('/path/to/main.go') == 'go run /path/to/main.go'

    def test_get_run_command_for_file_with_spaces(self, mock_environment, mock_csv_file):
        """A path with spaces must be shell-quoted (callers run it via bash -lc)."""
        import shlex
        result = get_run_command_for_file('/path/to/my script.py')
        assert result == "python '/path/to/my script.py'"
        assert shlex.split(result) == ['python', '/path/to/my script.py']

    def test_get_run_command_for_file_shell_metacharacters_not_injected(self, mock_environment, mock_csv_file):
        """A path with $()/;/spaces must not inject under bash -lc / shell=True."""
        import shlex
        evil = '/repo/$(touch PWN)/a; b.py'
        result = get_run_command_for_file(evil)
        argv = shlex.split(result)
        assert argv == ['python', evil], (result, argv)
        assert '$(touch' not in argv, argv

    def test_get_run_command_for_non_executable(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for non-executable files."""
        assert get_run_command_for_file('/path/to/data.json') == ''
        assert get_run_command_for_file('/path/to/README.md') == ''

    def test_get_run_command_for_unknown_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for unknown extensions."""
        assert get_run_command_for_file('/path/to/file.xyz') == ''

    def test_get_run_command_for_file_no_extension(self, mock_environment, mock_csv_file):
        """Tests get_run_command_for_file for files without extension."""
        assert get_run_command_for_file('/path/to/Makefile') == ''

    def test_get_run_command_for_file_missing_environment(self, monkeypatch):
        """Tests get_run_command_for_file when PDD_PATH is not set."""
        monkeypatch.delenv("PDD_PATH", raising=False)
        with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
            get_run_command_for_file('/path/to/script.py')

    def test_adjacent_placeholder_csv_templates_still_resolve(self):
        """Shipped CSV templates whose ``{file}`` sits adjacent to literal text —
        Fortran ``gfortran -o {file}.out {file} && ./{file}.out`` and Pascal
        ``fpc {file} && ./{file}`` — MUST still produce a command (a prior over-strict
        adjacency rejection returned ``''`` and silently disabled crash verification
        for those languages). Uses the REAL project CSV via PDD_PATH."""
        import shlex as _shlex
        repo = str(Path(__file__).parent.parent)
        os.environ["PDD_PATH"] = repo
        try:
            f90 = get_run_command_for_file("/proj/main.f90")
            pas = get_run_command_for_file("/proj/main.pas")
        finally:
            os.environ.pop("PDD_PATH", None)
        assert f90 and "gfortran" in f90 and "/proj/main.f90" in f90, f90
        assert pas and "fpc" in pas and "/proj/main.pas" in pas, pas
        # A metacharacter path stays inert (single-quoted) even in adjacency.
        evil_path = "/p/$(touch PWN).f90"
        os.environ["PDD_PATH"] = repo
        try:
            evil = get_run_command_for_file(evil_path)
        finally:
            os.environ.pop("PDD_PATH", None)
        assert _shlex.quote(evil_path) in evil, evil          # payload single-quoted
        assert "touch" in evil and " $(touch PWN)" not in evil  # never a bare $()


class TestShellSafeSubstitute:
    """Direct tests for the shell-lexical-aware substitution helper.

    The result is executed with ``shell=True`` by callers, so every inserted
    value must be neutralized (``shlex.quote``) AND placed only where quoting
    can protect it — a standalone, unquoted bare word."""

    def test_bare_word_value_is_single_quoted_and_inert(self):
        """A metacharacter-laden value at a bare-word placeholder is single-quoted,
        so ``$(...)``/``;`` in the path are literal, not executed."""
        evil = "/x/$(touch PWN)/a; b.py"
        out = shell_safe_substitute("pytest {file}", {"{file}": evil})
        assert shlex.split(out) == ["pytest", evil], out
        assert "$(touch" not in shlex.split(out)

    def test_quoted_or_dollar_prefixed_placeholder_is_refused(self):
        """A placeholder nested in the template's own quotes/backticks, or immediately
        preceded by ``$``/``\\`` (``${file}`` → ``$'...'`` ANSI-C), cannot be made safe
        by ``shlex.quote`` — the helper returns None so the caller falls through rather
        than emit an injectable command. A space-surrounded placeholder that is still
        *inside* an enclosing quote is refused too."""
        for tpl in ('pytest "{file}"', "pytest '{file}'", "run `{file}`",
                    'echo "a {file} b"', "echo ${file}"):
            assert shell_safe_substitute(tpl, {"{file}": "x"}) is None, tpl

    def test_literal_adjacency_is_safe_and_inert(self):
        """A placeholder adjacent to ORDINARY literal word characters (a suffix
        ``{file}.out`` or prefix ``./{file}``) is safe: ``shlex.quote`` yields a
        self-contained word, so concatenated literals extend the same argument and a
        ``$(...)`` in the value stays inert. Verified by real ``bash -lc`` execution."""
        # Fortran/Pascal-style adjacent templates substitute (no longer refused).
        out = shell_safe_substitute(
            "gfortran -o {file}.out {file}", {"{file}": "main.f90"})
        assert out == "gfortran -o main.f90.out main.f90", out
        # A malicious value in adjacency does not execute under bash -lc.
        cmd = shell_safe_substitute(
            "echo pre-{file}.suf", {"{file}": "$(touch PWN_ADJ)"})
        with tempfile.TemporaryDirectory() as d:
            proc = subprocess.run(["bash", "-lc", cmd], cwd=d,
                                  capture_output=True, text=True, timeout=10)
            assert "PWN_ADJ" not in os.listdir(d), os.listdir(d)
            assert "$(touch PWN_ADJ)" in proc.stdout, proc.stdout

    def test_heredoc_comment_and_multiline_are_refused(self):
        """A here-document body, a shell comment, or any multiline template is not an
        ordinary word context — ``shlex.quote`` single-quoting does not stop a
        ``$(...)`` in a heredoc body, and a newline in the value would break out of a
        comment. All are refused (None). Verified by real ``bash -lc`` execution of the
        naive (rejected) form to prove the exploit is real."""
        heredoc = "cat <<EOF\n{file}\nEOF"
        assert shell_safe_substitute(heredoc, {"{file}": "$(touch PWN_HD)"}) is None
        assert shell_safe_substitute("echo hi # {file}",
                                     {"{file}": "\n$(touch PWN_CM)"}) is None
        assert shell_safe_substitute("echo {file}\r\necho x", {"{file}": "a"}) is None
        # Prove the heredoc exploit the guard prevents is genuine: the naive
        # single-quoted substitution WOULD execute the payload under bash.
        with tempfile.TemporaryDirectory() as d:
            naive = heredoc.replace("{file}", shlex.quote("$(touch PWN_HD)"))
            subprocess.run(["bash", "-lc", naive], cwd=d,
                           capture_output=True, text=True, timeout=10)
            assert "PWN_HD" in os.listdir(d), "expected the naive heredoc form to inject"

    def test_expansion_and_operator_comment_contexts_are_refused(self):
        """Command-evaluation contexts — arithmetic `$(( ))`, command substitution
        `$( )`, parameter expansion `${ }`, backticks, and `(...)` subshells /
        process substitution — plus a `#` comment that starts right after a `;`/`&`/`|`
        control operator are not ordinary word contexts and are refused (None). Proven
        with real `bash -lc` execution of the naive forms."""
        for tpl in ("printf X:$(({file}))", "echo $({file})", "echo ${x:-{file}}",
                    "( {file} )", "cat <({file})", "run `{file}`",
                    "printf SAFE;# {file}", "printf X&# {file}", "printf X|# {file}"):
            assert shell_safe_substitute(tpl, {"{file}": "x"}) is None, tpl
        # A `#` that is mid-word (not a comment) must NOT cause refusal.
        assert shell_safe_substitute("echo a#b {file}", {"{file}": "x"}) == "echo a#b x"
        # Prove the arithmetic-context exploit the guard prevents is genuine.
        with tempfile.TemporaryDirectory() as d:
            naive = "printf X:$((" + shlex.quote("$(touch PWN_AR >&2)") + "))"
            subprocess.run(["bash", "-lc", naive], cwd=d,
                           capture_output=True, text=True, timeout=10)
            assert "PWN_AR" in os.listdir(d), "expected the naive arithmetic form to inject"

    def test_values_are_not_rescanned_for_other_placeholders(self):
        """Substitution is single-pass: a value that itself contains another
        placeholder's text is inserted verbatim (single-quoted), never re-expanded.
        A sequential ``str.replace`` chain would wrongly expand ``{b}`` inside a's
        value into ``$(touch PWN)``."""
        out = shell_safe_substitute(
            "run {a} {b}", {"{a}": "{b}", "{b}": "$(touch PWN)"})
        assert shlex.split(out) == ["run", "{b}", "$(touch PWN)"], out
        assert "touch" in out  # present, but literal inside the quotes for {b}
        # The '{b}' inserted for {a} was NOT re-expanded into the $() payload.
        assert out.count("$(touch PWN)") == 1

    def test_absent_placeholder_returns_template_unchanged(self):
        """A template with no placeholder is returned as-is (still a valid command)."""
        assert shell_safe_substitute("pytest --version", {"{file}": "x"}) == "pytest --version"

    def test_empty_key_and_escaped_placeholder_are_handled(self):
        """An empty placeholder key would match at every position and never advance the
        cursor — it must be rejected up front (no hang), returning None. An ESCAPED
        placeholder (``\\{test}``) cannot be filled and is declined rather than emitted
        with the token left unresolved."""
        # Empty key → None, and crucially returns quickly (no infinite loop).
        assert shell_safe_substitute("echo", {"": "x"}) is None
        assert shell_safe_substitute("pytest {test}", {"": "x", "{test}": "/a.py"}) is None
        # Escaped placeholder → None (unfillable), while the unescaped form still works.
        assert shell_safe_substitute(r"pytest \{test}", {"{test}": "x"}) is None
        assert shell_safe_substitute("pytest {test}", {"{test}": "/a.py"}) == "pytest /a.py"

    def test_brace_and_glob_contexts_are_refused(self):
        """A brace-expansion or pathname-expansion metacharacter OUTSIDE a placeholder
        (`{a,b}`, `*`, `?`, `[…]`, `~`) would change the command's word count under bash
        (and a value's ``,`` is left unquoted by ``shlex.quote``, so it would re-split
        inside a template brace). Such templates are refused. Ordinary adjacency
        (`{file}.out`, `./{file}`) is unaffected. Proven with real ``bash -lc``."""
        for tpl in ('printf "<%s>" pre{{file},tail}', "ls {file}*", "ls {file}[abc]",
                    "cat ~/{file}", "echo {a,b}{file}"):
            assert shell_safe_substitute(tpl, {"{file}": "a,b"}) is None, tpl
        # A comma-bearing value in a NON-brace template stays a single argument.
        cmd = shell_safe_substitute("python {file}", {"{file}": "a,b"})
        assert cmd == "python a,b"
        proc = subprocess.run(["bash", "-lc", cmd.replace("python", "printf '%s\\n'")],
                              capture_output=True, text=True, timeout=10)
        assert proc.stdout == "a,b\n", proc.stdout  # one argument, not brace-split

    def test_reevaluation_contexts_are_refused(self):
        """A template that RE-EVALUATES the value as code — ``eval`` or a shell with
        ``-c`` — is refused, because the second parse undoes ``shlex.quote``. A bare
        ``sh {file}`` / ``bash {file}`` (run the file as a script — the shipped
        Shell/Bash/Zsh run-commands) and a non-shell ``-c`` option (``pytest -c cfg``)
        are safe and still substitute. Proven with real ``bash -lc`` execution."""
        for tpl in ("eval {file}", "bash -c {file}", "sh -c {file}", "dash -c {file}",
                    "build && eval {file}", "CI=1 eval {file}"):
            assert shell_safe_substitute(tpl, {"{file}": "x"}) is None, tpl
        # Safe: the shell runs the FILE (value is a filename, single-quoted).
        assert shell_safe_substitute("sh {file}", {"{file}": "/a.sh"}) == "sh /a.sh"
        assert shell_safe_substitute(
            "pytest -c cfg {file}", {"{file}": "/t.py"}) == "pytest -c cfg /t.py"
        # Prove the eval exploit the guard prevents is genuine.
        with tempfile.TemporaryDirectory() as d:
            naive = "eval " + shlex.quote("$(touch PWN_EVAL)")
            subprocess.run(["bash", "-lc", naive], cwd=d, capture_output=True, timeout=10)
            assert "PWN_EVAL" in os.listdir(d), "expected the naive eval form to inject"
