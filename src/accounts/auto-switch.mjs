// Generated from prompts/cli/accounts-cli.prompt.md.
// Shell auto-switch wrapper generator and atomic profile installer/updater.
// By default BOTH `codex()` and `claude()` delegate to `pdd-codex` and `pdd-claude` with fail-open.
// Legacy PTY rotation (`pdd accounts sync` + `pdd accounts codex --`) stays behind PDD_LEGACY_PTY_ROTATE=1.
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { writeAtomicPreservingSymlinkAndMode } from '../shared/atomic-fs.mjs';

export const AUTO_BEGIN = '# >>> pdd accounts auto >>>';
export const AUTO_END = '# <<< pdd accounts auto <<<';

export function renderAutoSwitchBlock(shell = 'sh') {
  if (shell === 'fish') {
    return [
      AUTO_BEGIN,
      'functions -e codex claude 2>/dev/null; or true',
      'function codex --wraps codex',
      '  set -l _pdd_mhome "$HOME/.local/state/pdd/codex-home"',
      '  if set -q XDG_STATE_HOME; and test -n "$XDG_STATE_HOME"',
      '    set _pdd_mhome (string replace -r \'/+$\' \'\' -- "$XDG_STATE_HOME")"/pdd/codex-home"',
      '  end',
      '  if set -q PDD_STATE_DIR; and test -n "$PDD_STATE_DIR"',
      '    set _pdd_mhome (string replace -r \'/+$\' \'\' -- "$PDD_STATE_DIR")"/codex-home"',
      '  end',
      '  set _pdd_mhome (string replace -a \'/./\' \'/\' -- "$_pdd_mhome")',
      '  set -l _pdd_cur_home ""',
      '  set -l _pdd_is_mhome 0',
      '  if set -q CODEX_HOME; and test -n "$CODEX_HOME"',
      '    set _pdd_cur_home (string replace -a \'/./\' \'/\' -- (string replace -r \'/+$\' \'\' -- "$CODEX_HOME"))',
      '    if test "$_pdd_cur_home" = "$_pdd_mhome"',
      '      set _pdd_is_mhome 1',
      '    else if test -e "$_pdd_cur_home"; and test -e "$_pdd_mhome"; and test "$_pdd_cur_home" -ef "$_pdd_mhome"',
      '      set _pdd_is_mhome 1',
      '    end',
      '  end',
      '  set -l _pdd_sub ""',
      '  set -l _pdd_next ""',
      '  set -l _pdd_skip 0',
      '  for _pdd_arg in $argv',
      '    if test $_pdd_skip -eq 1',
      '      set _pdd_skip 0',
      '      continue',
      '    end',
      '    if test "$_pdd_arg" = "--"',
      '      break',
      '    end',
      '    if test -z "$_pdd_sub"',
      '      switch "$_pdd_arg"',
      '        case -c --config --enable --disable --remote --remote-auth-token-env -i --image -m --model --local-provider -p --profile -s --sandbox -C --cd --add-dir -a --ask-for-approval --color -o --output-last-message',
      '          set _pdd_skip 1',
      '          continue',
      '        case \'-*\'',
      '          continue',
      '        case logout login',
      '          set _pdd_sub "$_pdd_arg"',
      '          continue',
      '        case agents exec e review mcp mcp-server plugin app-server remote-control app completion update doctor sandbox debug apply a resume queue archive delete migrate-rollouts migrate-nfs-db unarchive fork cloud exec-server features help',
      '          set _pdd_sub "$_pdd_arg"',
      '          break',
      '        case \'*\'',
      '          break',
      '      end',
      '    else if test -z "$_pdd_next"',
      '      switch "$_pdd_arg"',
      '        case \'-*\'',
      '          continue',
      '      end',
      '      set _pdd_next "$_pdd_arg"',
      '      break',
      '    end',
      '  end',
      '  if test "$_pdd_sub" = "logout"; or begin; test "$_pdd_sub" = "login"; and test "$_pdd_next" != "status"; end',
      '    if test $_pdd_is_mhome -eq 1',
      '      echo "pdd accounts: refusing to run \'codex $_pdd_sub\' inside PDD-managed CODEX_HOME ($_pdd_mhome) so the Cloud token is not revoked. Use \'pdd accounts pause\', \'pdd accounts remove\', or \'pdd accounts use\' instead (or set -e CODEX_HOME to manage ~/.codex)." >&2',
      '      return 1',
      '    end',
      '    command codex $argv',
      '    return $status',
      '  end',
      '  if test -z "$_pdd_cur_home"; or test $_pdd_is_mhome -eq 1',
      '    if test "$PDD_LEGACY_PTY_ROTATE" = "1"',
      '      set -l _pdd_cx_home ""',
      '      if command -sq pdd',
      '        set _pdd_cx_home (env PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null; or true)',
      '      end',
      '      if test -n "$_pdd_cx_home"; and test -f "$_pdd_cx_home/auth.json"',
      '        if isatty stdin; and isatty stdout; and begin; test -z "$_pdd_sub"; or test "$_pdd_sub" = "resume"; or test "$_pdd_sub" = "fork"; end',
      '          CODEX_HOME="$_pdd_cx_home" pdd accounts codex -- $argv',
      '          return $status',
      '        end',
      '        CODEX_HOME="$_pdd_cx_home" command codex $argv',
      '        return $status',
      '      end',
      '    else if command -sq pdd-codex',
      '      if test $_pdd_is_mhome -eq 1',
      '        env -u CODEX_HOME PDD_CODEX_AUTO_FAIL_OPEN=1 pdd-codex $argv',
      '      else',
      '        PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex $argv',
      '      end',
      '      return $status',
      '    end',
      '    if set -q CODEX_HOME',
      '      env -u CODEX_HOME codex $argv',
      '      return $status',
      '    end',
      '  end',
      '  command codex $argv',
      'end',
      'function claude --wraps claude',
      '  if set -q CLAUDE_CONFIG_DIR; and test -n "$CLAUDE_CONFIG_DIR"',
      '    command claude $argv',
      '    return $status',
      '  end',
      '  if test (count $argv) -gt 0',
      '    switch $argv[1]',
      '      case auth login logout setup-token -v --version -h --help',
      '        command claude $argv',
      '        return $status',
      '    end',
      '  end',
      '  if command -sq pdd-claude',
      '    PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude $argv',
      '    return $status',
      '  end',
      '  command claude $argv',
      'end',
      AUTO_END,
    ].join('\n');
  }
  return [
    AUTO_BEGIN,
    'unalias codex claude 2>/dev/null || true',
    'codex() {',
    '  local _pdd_mhome="$HOME/.local/state/pdd/codex-home"',
    '  if [ -n "${XDG_STATE_HOME:-}" ]; then',
    '    _pdd_mhome="${XDG_STATE_HOME%/}/pdd/codex-home"',
    '  fi',
    '  if [ -n "${PDD_STATE_DIR:-}" ]; then',
    '    _pdd_mhome="${PDD_STATE_DIR%/}/codex-home"',
    '  fi',
    '  while [ "${_pdd_mhome#*/./}" != "$_pdd_mhome" ]; do _pdd_mhome="${_pdd_mhome%%/./*}/${_pdd_mhome#*/./}"; done',
    '  local _pdd_cur_home="${CODEX_HOME:-}" _pdd_is_mhome=0',
    '  while [ -n "$_pdd_cur_home" ] && [ "${_pdd_cur_home%/}" != "$_pdd_cur_home" ]; do _pdd_cur_home="${_pdd_cur_home%/}"; done',
    '  while [ "${_pdd_cur_home#*/./}" != "$_pdd_cur_home" ]; do _pdd_cur_home="${_pdd_cur_home%%/./*}/${_pdd_cur_home#*/./}"; done',
    '  if [ -n "$_pdd_cur_home" ]; then',
    '    if [ "$_pdd_cur_home" = "$_pdd_mhome" ]; then',
    '      _pdd_is_mhome=1',
    '    elif [ -e "$_pdd_cur_home" ] && [ -e "$_pdd_mhome" ] && [ "$_pdd_cur_home" -ef "$_pdd_mhome" ]; then',
    '      _pdd_is_mhome=1',
    '    fi',
    '  fi',
    '  local _pdd_sub="" _pdd_next="" _pdd_skip=0 _pdd_arg',
    '  for _pdd_arg in "$@"; do',
    '    if [ "$_pdd_skip" -eq 1 ]; then',
    '      _pdd_skip=0',
    '      continue',
    '    fi',
    '    if [ "$_pdd_arg" = "--" ]; then',
    '      break',
    '    fi',
    '    if [ -z "$_pdd_sub" ]; then',
    '      case "$_pdd_arg" in',
    '        -c|--config|--enable|--disable|--remote|--remote-auth-token-env|-i|--image|-m|--model|--local-provider|-p|--profile|-s|--sandbox|-C|--cd|--add-dir|-a|--ask-for-approval|--color|-o|--output-last-message)',
    '          _pdd_skip=1',
    '          continue',
    '          ;;',
    '        -*) continue ;;',
    '        logout|login)',
    '          _pdd_sub="$_pdd_arg"',
    '          continue',
    '          ;;',
    '        agents|exec|e|review|mcp|mcp-server|plugin|app-server|remote-control|app|completion|update|doctor|sandbox|debug|apply|a|resume|queue|archive|delete|migrate-rollouts|migrate-nfs-db|unarchive|fork|cloud|exec-server|features|help)',
    '          _pdd_sub="$_pdd_arg"',
    '          break',
    '          ;;',
    '        *)',
    '          break',
    '          ;;',
    '      esac',
    '    elif [ -z "$_pdd_next" ]; then',
    '      case "$_pdd_arg" in',
    '        -*) continue ;;',
    '      esac',
    '      _pdd_next="$_pdd_arg"',
    '      break',
    '    fi',
    '  done',
    '  if [ "$_pdd_sub" = "logout" ] || { [ "$_pdd_sub" = "login" ] && [ "$_pdd_next" != "status" ]; }; then',
    '    if [ "$_pdd_is_mhome" -eq 1 ]; then',
    '      printf \'%s\\n\' "pdd accounts: refusing to run \'codex $_pdd_sub\' inside PDD-managed CODEX_HOME ($_pdd_mhome) so the Cloud token is not revoked. Use \'pdd accounts pause\', \'pdd accounts remove\', or \'pdd accounts use\' instead (or unset CODEX_HOME to manage ~/.codex)." >&2',
    '      return 1',
    '    fi',
    '    command codex "$@"',
    '    return $?',
    '  fi',
    '  if [ -z "$_pdd_cur_home" ] || [ "$_pdd_is_mhome" -eq 1 ]; then',
    '    if [ "${PDD_LEGACY_PTY_ROTATE:-}" = "1" ]; then',
    '      local _pdd_cx_home=""',
    '      if command -v pdd >/dev/null 2>&1; then',
    '        _pdd_cx_home="$(PDD_PRINT_CODEX_HOME=1 pdd accounts sync --provider codex --quiet --timeout-ms 1200 2>/dev/null || true)"',
    '      fi',
    '      if [ -n "$_pdd_cx_home" ] && [ -f "$_pdd_cx_home/auth.json" ]; then',
    '        if [ -t 0 ] && [ -t 1 ] && { [ -z "$_pdd_sub" ] || [ "$_pdd_sub" = "resume" ] || [ "$_pdd_sub" = "fork" ]; }; then',
    '          CODEX_HOME="$_pdd_cx_home" pdd accounts codex -- "$@"',
    '          return $?',
    '        fi',
    '        CODEX_HOME="$_pdd_cx_home" command codex "$@"',
    '        return $?',
    '      fi',
    '    elif command -v pdd-codex >/dev/null 2>&1; then',
    '      if [ "$_pdd_is_mhome" -eq 1 ]; then',
    '        (unset CODEX_HOME; PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex "$@")',
    '      else',
    '        PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex "$@"',
    '      fi',
    '      return $?',
    '    fi',
    '    if [ -n "${CODEX_HOME:-}" ]; then',
    '      (unset CODEX_HOME; command codex "$@")',
    '      return $?',
    '    fi',
    '  fi',
    '  command codex "$@"',
    '}',
    'claude() {',
    '  if [ -n "${CLAUDE_CONFIG_DIR:-}" ]; then',
    '    command claude "$@"',
    '    return $?',
    '  fi',
    '  case "${1:-}" in',
    '    auth|login|logout|setup-token|-v|--version|-h|--help)',
    '      command claude "$@"',
    '      return $?',
    '      ;;',
    '  esac',
    '  if command -v pdd-claude >/dev/null 2>&1; then',
    '    PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude "$@"',
    '    return $?',
    '  fi',
    '  command claude "$@"',
    '}',
    AUTO_END,
  ].join('\n');
}

export function applyAutoSwitchBlock(existingText = '', shell = 'sh') {
  const block = `${renderAutoSwitchBlock(shell)}\n`;
  const source = String(existingText ?? '');
  if (source.includes(AUTO_BEGIN) && source.includes(AUTO_END)) {
    return source.replace(/# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/, () => block);
  }
  if (!source) return block;
  return source.endsWith('\n') ? `${source}\n${block}` : `${source}\n\n${block}`;
}

export function removeAutoSwitchBlock(existingText = '') {
  const source = String(existingText ?? '');
  if (!source.includes(AUTO_BEGIN)) return source;
  let cleaned = source.replace(/\n\n# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/g, '\n');
  cleaned = cleaned.replace(/\n?# >>> pdd accounts auto >>>[\s\S]*?# <<< pdd accounts auto <<<\n?/g, '');
  return cleaned;
}

export function shellProfileEntries(env = process.env, { requireExplicitHome = false } = {}) {
  const explicitHome = typeof env?.HOME === 'string' ? env.HOME.trim() : '';
  if (requireExplicitHome && !explicitHome) return [];
  const home = explicitHome || homedir();
  const xdgConfig = (typeof env?.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim()) ? env.XDG_CONFIG_HOME.trim() : join(home, '.config');
  return [
    { path: join(home, '.zshrc'), shell: 'zsh' },
    { path: join(home, '.bashrc'), shell: 'bash' },
    { path: join(xdgConfig, 'fish', 'config.fish'), shell: 'fish' },
  ];
}

export function refreshInstalledAutoSwitchBlocks({ env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (typeof fs?.readFileSync !== 'function' || typeof fs?.writeFileSync !== 'function') return [];
  const entries = shellProfileEntries(env, { requireExplicitHome: true });
  if (!entries.length) return [];
  const upgraded = [];
  for (const entry of entries) {
    try {
      const existingText = fs.readFileSync(entry.path, 'utf8');
      if (typeof existingText !== 'string' || !existingText.includes(AUTO_BEGIN) || !existingText.includes(AUTO_END)) continue;
      const beginIdx = existingText.indexOf(AUTO_BEGIN);
      const endIdx = existingText.indexOf(AUTO_END, beginIdx + AUTO_BEGIN.length);
      if (beginIdx < 0 || endIdx < 0) continue;
      const nextText = applyAutoSwitchBlock(existingText, entry.shell);
      if (nextText === existingText) continue;
      writeAtomicPreservingSymlinkAndMode(fs, entry.path, nextText, { defaultMode: 0o644 });
      upgraded.push(entry.path);
    } catch {}
  }
  return upgraded;
}
