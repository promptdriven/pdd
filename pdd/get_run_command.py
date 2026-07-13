"""Module to retrieve run commands for programming languages."""

import os
import csv
import re
import shlex
from typing import Dict, Optional
from pdd.path_resolution import get_default_resolver

# Commands/forms that RE-EVALUATE an argument as code, undoing ``shlex.quote``'s single
# quoting: ``eval <arg>`` and a shell invoked with ``-c`` (``bash -c``/``sh -c``…).
_REEVAL_SHELLS = frozenset({"sh", "bash", "dash", "zsh", "ksh", "ash"})


def _is_dash_c_option(tok: str) -> bool:
    """True for a shell ``-c`` code option, INCLUDING a combined single-dash short-option
    cluster that contains ``c`` (``-lc``, ``-xc``) — but not a long ``--`` option."""
    if tok.startswith("--"):
        return False
    return bool(re.match(r"^-[A-Za-z]*c[A-Za-z]*$", tok))


def _feeds_value_into_reevaluation(template: str) -> bool:
    """True when ``template`` would RE-EVALUATE an inserted value as code — so a
    ``shlex.quote``-d ``$(...)`` in the value would still execute at the second parse.
    The value is unsafe when a shell RE-EVALUATES it as code, whether it arrives as a
    ``-c`` argument (``bash -c {file}``, ``bash -lc {file}``, ``timeout 5 bash -c`` — a
    shell hidden behind an option-bearing wrapper) OR as STDIN piped into a shell
    (``printf %s {file} | bash``) OR via a here-string / here-document redirect
    (``bash <<< {file}``). Detection is conservative:

    * an ``eval`` token anywhere → unsafe;
    * a clause containing both a shell name and a ``-c``-bearing option → unsafe;
    * a re-evaluating shell name anywhere in the template together with a pipe ``|`` or an
      input redirect / here-string (``<``) → unsafe (the value could flow into it).

    A bare ``sh {file}`` / ``bash {file}`` (run the *file* as a script — the shipped
    Shell/Bash/Zsh templates) has no ``-c``, pipe, or ``<``, so it stays SAFE; a non-shell
    ``-c`` option (``pytest -c cfg``) has no shell and stays safe. Comment parsing is
    disabled so a mid-word ``#`` (``echo a#b``) cannot hide a later clause. An unparseable
    template fails closed (True). Called only after ``$``/backtick/``()``/brace/glob/
    newline forms are already refused, so the tokenizer sees a simple command line."""
    try:
        lex = shlex.shlex(template, posix=True, punctuation_chars=True)
        lex.whitespace_split = True
        lex.commenters = ""  # Bash does not treat a mid-word '#' as a comment
        clauses, clause = [], []
        for tok in lex:
            if tok in (";", "&", "&&", "|", "||"):
                clauses.append(clause)
                clause = []
            else:
                clause.append(tok)
        clauses.append(clause)
    except ValueError:
        return True
    all_bases = [t.split("/")[-1] for clause in clauses for t in clause]
    if "eval" in all_bases:
        return True
    # ``env -S`` / ``env --split-string`` re-parses its argument(s) into a fresh command
    # line, so a shell + ``-c`` can hide inside a quoted string beyond the top-level token
    # scan (``env -S 'bash -c' {file}`` → ``bash -c '<path>'`` second-parses the path). No
    # run/verify template needs ``env -S`` — refuse it.
    if "env" in all_bases:
        for clause in clauses:
            if any(t.startswith("-S") or t == "--split-string"
                   or t.startswith("--split-string=") for t in clause):
                return True
    has_shell = any(b in _REEVAL_SHELLS for b in all_bases)
    # A shell that could RECEIVE the value as code via a pipe or an input
    # redirect/here-string — the ``-c`` check would miss both.
    if has_shell and ("|" in template or "<" in template):
        return True
    for toks in clauses:
        bases = [t.split("/")[-1] for t in toks]
        if any(b in _REEVAL_SHELLS for b in bases) \
                and any(_is_dash_c_option(t) for t in toks):
            return True
        # A shell command STRING hidden inside a single quoted token (a wrapper's
        # re-parsed argument) — re-tokenize each multi-word token and re-check.
        for t in toks:
            try:
                sub = shlex.split(t)
            except ValueError:
                continue
            sub_bases = [x.split("/")[-1] for x in sub]
            if len(sub) > 1 and (
                "eval" in sub_bases
                or (any(b in _REEVAL_SHELLS for b in sub_bases)
                    and any(_is_dash_c_option(x) for x in sub))):
                return True
    return False


def shell_safe_substitute(template: str, values: Dict[str, str]) -> Optional[str]:
    """Substitute ``{placeholder}`` tokens in a shell-command ``template`` with
    shell-quoted values in a SINGLE left-to-right pass, or return ``None`` when the
    template is unsafe.

    ``shlex.quote`` returns a *self-contained shell word* — a value with no
    metacharacters is returned bare, otherwise it is single-quoted. Such a word is
    safe to splice in, and safe to concatenate with ORDINARY LITERAL characters on
    either side (so a suffix ``{file}.out`` or prefix ``./{file}`` stays a single
    correctly-quoted argument).

    The value is only reinterpreted where the surrounding template creates a context
    the single quoting cannot survive: a command-evaluation context (``$(...)``,
    ``${...}``, arithmetic ``$((...))``, a ``$``-variable, backticks, or a
    ``(...)``/process-substitution subshell), the template's own quotes, a shell
    comment, or a here-document body. Rather than model all of those, this helper
    ALLOWLISTS simple command lines: it refuses (returns ``None``) any template that

    * contains a newline (the only way to form a here-document body);
    * contains ``$``, a backtick, or ``(``/``)`` anywhere (every command-substitution,
      parameter/arithmetic expansion, and subshell/process-substitution form requires
      one of these — real ``run``/verify templates like ``python {file}`` or
      ``gfortran -o {file}.out {file}`` need none of them);
    * contains a brace-expansion / pathname-expansion metacharacter (`{`, `}`, `*`, `?`,
      `[`, `]`, `~`) OUTSIDE a placeholder token — an unquoted `{a,b}` or glob would
      change the command's word count (and ``shlex.quote`` leaves a value's ``,``
      unquoted, so a value inside such a brace would re-split);
    * places a placeholder inside its own single/double quotes, immediately after a
      backslash, or inside a shell comment (a ``#`` that starts a comment — at a word
      boundary or right after a ``;``/``&``/``|`` control operator — where a newline in
      the value would break out onto a new command line);
    * RE-EVALUATES the value as code — an ``eval`` command or a shell invoked with
      ``-c`` (``bash -c {file}``) — where the second parse undoes the single quoting.
      (A bare ``sh {file}`` / ``bash {file}`` that runs the *file* as a script is safe
      and still substitutes; only the ``-c`` code argument is refused.)

    Substitution is single-pass, so a value that itself contains a ``{...}`` token is
    never rescanned as a placeholder. An empty placeholder key is rejected up front (it
    would match everywhere and never advance), and an ESCAPED placeholder (``\\{test}``)
    is declined rather than emitted with the placeholder left unresolved.
    """
    # Refuse constructs the single-pass allowlist cannot reason about: multiline
    # (here-document bodies) and any command-evaluation context. `$` covers `$(`,
    # `${`, `$((`, and `$var`; backtick covers command substitution; `(`/`)` cover
    # subshells and `$(`/`<(`/`>(`. No legitimate run/verify template needs these.
    if "\n" in template or "\r" in template:
        return None
    if any(ch in template for ch in "$`()"):
        return None
    # An empty placeholder key would match at every position (``startswith("", i)``)
    # and never advance the cursor — reject rather than loop forever.
    if any(not key for key in values):
        return None
    # Reject brace-expansion (`{a,b}`), pathname-expansion (`*`/`?`/`[…]`), and tilde
    # metacharacters that appear OUTSIDE a placeholder token: an unquoted `{…,…}` or a
    # glob would re-split/expand the command into a DIFFERENT word count under bash
    # (e.g. `pre{X,tail}` → `preX pretail`), and a bare ``,`` from ``shlex.quote`` (which
    # leaves ``,`` unquoted) inside such a brace would be reinterpreted. Placeholders
    # legitimately contain `{`/`}`, so mask them out first; ordinary adjacency like
    # ``./{file}`` and ``{file}.out`` has none of these and is unaffected.
    masked = template
    for key in values:
        masked = masked.replace(key, "\x00")
    if any(ch in masked for ch in "{}[]*?~"):
        return None
    # Refuse templates that re-evaluate an inserted value as code (``eval {file}``,
    # ``bash -c {file}``) — the second parse would undo ``shlex.quote``'s single quoting.
    if _feeds_value_into_reevaluation(template):
        return None
    out: list = []
    i, n = 0, len(template)
    in_single = in_double = False
    in_comment = False       # after an unquoted comment-starting '#' to end of line
    prev_significant = ""     # last emitted template char (for comment-boundary/escape)
    while i < n:
        placeholder = next(
            (k for k in values if template.startswith(k, i)), None)
        if placeholder is not None:
            if in_single or in_double or in_comment:
                return None
            out.append(shlex.quote(values[placeholder]))
            i += len(placeholder)
            prev_significant = "x"  # placeholder resolves to a non-boundary word char
            continue
        char = template[i]
        if char == "\\" and not in_single:
            # An escaped placeholder (``\{test}``) cannot be filled meaningfully — its
            # brace is now a literal — so decline rather than emit a command with the
            # placeholder left unresolved.
            if any(template.startswith(k, i + 1) for k in values):
                return None
            out.append(char)
            nxt = template[i + 1] if i + 1 < n else ""
            if nxt:
                out.append(nxt)
                i += 2
            else:
                i += 1
            prev_significant = "x"  # an escaped char is a word char, not a boundary
            continue
        if char == "'" and not in_double and not in_comment:
            in_single = not in_single
        elif char == '"' and not in_single and not in_comment:
            in_double = not in_double
        elif char == "#" and not in_single and not in_double and not in_comment \
                and (prev_significant in ("", " ", "\t", ";", "&", "|")):
            # `#` begins a comment at a command-word boundary — start-of-line, after
            # whitespace, or right after a control operator (`;`/`&`/`|`).
            in_comment = True
        out.append(char)
        prev_significant = char
        i += 1
    return "".join(out)


def get_run_command(extension: str) -> str:
    """
    Retrieves the run command for a given file extension.

    Args:
        extension: The file extension (e.g., ".py", ".js").

    Returns:
        The run command template with {file} placeholder (e.g., "python {file}"),
        or an empty string if not found or not executable.

    Raises:
        ValueError: If the PDD_PATH environment variable is not set.
    """
    # Step 1: Resolve CSV path from PDD_PATH
    resolver = get_default_resolver()
    try:
        csv_path = resolver.resolve_data_file("data/language_format.csv")
    except ValueError as exc:
        raise ValueError("PDD_PATH environment variable is not set") from exc

    # Step 2: Ensure the extension starts with a dot and convert to lowercase
    if not extension.startswith('.'):
        extension = '.' + extension
    extension = extension.lower()

    # Step 3: Look up the run command
    try:
        with open(csv_path, 'r') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row['extension'].lower() == extension:
                    run_command = row.get('run_command', '').strip()
                    return run_command if run_command else ''
    except FileNotFoundError:
        print(f"CSV file not found at {csv_path}")
    except csv.Error as e:
        print(f"Error reading CSV file: {e}")
    except KeyError:
        # run_command column doesn't exist
        pass

    return ''


def get_run_command_for_file(file_path: str) -> str:
    """
    Retrieves the run command for a given file, with the {file} placeholder replaced.

    Args:
        file_path: The path to the file to run.

    Returns:
        The complete run command (e.g., "python /path/to/script.py"),
        or an empty string if no run command is available for this file type.

    Raises:
        ValueError: If the PDD_PATH environment variable is not set.
    """
    _, extension = os.path.splitext(file_path)
    if not extension:
        return ''

    run_command_template = get_run_command(extension)
    if not run_command_template:
        return ''

    # Shell-quote the substituted path: callers run this command with `bash -lc`
    # / `shell=True`, so an unquoted path with spaces or shell metacharacters
    # (e.g. `/repo/$(touch PWN)/x.py`) would be re-split or executed via command
    # substitution. But `shlex.quote` is only safe when `{file}` is a standalone bare
    # word — a CSV template that quotes it (`printf %s "{file}"`) would let the value's
    # `$(...)` still execute — so refuse such a template (return '' = no command).
    substituted = shell_safe_substitute(run_command_template, {'{file}': file_path})
    return substituted if substituted is not None else ''
