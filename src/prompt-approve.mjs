// Generated from prompts/cli/prompt-approve.prompt.md (sha256: 52675828c996c633195c39cdae8da57a41e4579877563ade1f385690c3a5d7c6).
import { approvalActor, readApprovalPolicy, readSaidWords, readPromptApprovals, recordPromptApproval } from './approval-policy.mjs';
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { realpathSync, writeFileSync } from 'node:fs';
import { relative, resolve, sep, join } from 'node:path';
import { buildHumanBoundaryCard, formatApproveBoundaryCard } from './human-boundary-card.mjs';
import { runtimePreflightSlice } from './runtime-seam.mjs';
import { lineReader } from './shared/line-reader.mjs';
import { createPromptApproval, describeInterface } from './core/approve-prompt.mjs';

const { gitFiles, interfaceBlocks, promptSchemaRefusals, readPrompt, proseSha256 } = runtimePreflightSlice();
const { approvePromptText, askApproval, promptPath } = createPromptApproval({
  gitFiles,
  interfaceBlocks,
  promptSchemaRefusals,
  readPrompt,
  proseSha256,
  formatBoundaryCardLines: ({ root, focusPrompt, env }) =>
    formatApproveBoundaryCard(buildHumanBoundaryCard({ root, focusPrompt, env })),
});

export { approvePromptText, askApproval, describeInterface, lineReader, promptPath };

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
const line = (stream, text) => stream.write(`${text}\n`);

// pdd approve PROMPT. Returns the exit code.
export async function runApprove({ words = [], cwd = process.cwd(), said } = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout;
  const stderr = ports.stderr ?? process.stderr;
  const stdin = ports.stdin ?? process.stdin;
  const interactive = ports.interactive ?? (!!process.stdin.isTTY && !!process.stdout.isTTY);
  try {
    if (words.length !== 1) throw new Stop(2, 'Name one prompt: pdd approve prompts/<name>.prompt.md');
    const gitRun = async (args, dir) => ports.execFile
      ? ports.execFile('git', args, { cwd: dir, encoding: 'utf8' }).then(result => ({ ...result, status: result.code ?? 0 }))
      : (ports.spawnSync ?? spawnSync)('git', args, { cwd: dir, encoding: 'utf8' });
    const top = await gitRun(['rev-parse', '--show-toplevel'], cwd);
    if (top.status !== 0) throw new Stop(2, 'pdd approve works in a Git repository.');
    const root = realpathSync(top.stdout.trim());
    const path = promptPath(root, cwd, words[0]);
    if (!path) throw new Stop(2, `${relative(root, resolve(realpathSync(cwd), words[0])).split(sep).join('/')} is not a Git-visible *.prompt.md file in this repository.`);
    const { strictApprovals } = readApprovalPolicy({ root }, ports);
    const env = ports.env ?? process.env;
    const agent = approvalActor(env).kind === 'agent';
    const pane = Boolean(strictApprovals && env.HERDR_PANE_ID);
    if (strictApprovals ? said !== undefined || !interactive || agent || pane : said === undefined && !interactive) {
      throw new Stop(2, `pdd approve is for a person at a terminal. Ask the person to run: pdd approve ${path}`);
    }
    const common = await gitRun(['rev-parse', '--path-format=absolute', '--git-common-dir'], root);
    if (common.status !== 0) throw new Stop(4, 'Cannot resolve Git common directory.');
    const commonDir = common.stdout.trim();
    const approvals = readPromptApprovals({ commonDir }, ports);
    if (said !== undefined) {
      try { said = await readSaidWords(said, { ...ports, stdin }); }
      catch (error) { throw new Stop(2, error.message); }
    }
    const answers = said === undefined ? lineReader(stdin) : { close() {} };
    const commit = async ({ text, next, hash, prompt }) => {
      const fs = ports.fs ?? { writeFileSync };
      const iface = prompt?.interface;
      const evidence = {
        id: (ports.randomUUID ?? randomUUID)(),
        route: said === undefined ? 'terminal' : 'said',
        actor: approvalActor(env),
        at: (ports.now ?? Date.now)(),
        words: said ?? null,
        prompts: [{ path, proseSha256: hash, kind: iface?.kind ?? 'full', ...(iface?.kind === 'native-only' ? { reason: iface.reason } : {}) }],
      };
      try {
        if (next !== null) fs.writeFileSync(join(root, path), next);
        await recordPromptApproval({ commonDir, evidence }, ports);
      } catch (error) {
        if (next !== null) {
          try { fs.writeFileSync(join(root, path), text); }
          catch { throw new Stop(4, `Approval evidence failed; rollback failed for ${path}.`); }
        }
        throw error;
      }
      line(stdout, `${path} ${hash}`);
      line(stdout, `Approval route: ${evidence.route}; actor: ${evidence.actor.kind} ${evidence.actor.id}; at: ${evidence.at}`);
    };
    try {
      const result = await askApproval({ root, path, stdout, answers, said, commit, approvals, commonDir, strictApprovals, env });
      if (result.exitCode === 1) line(stdout, 'Not approved. Nothing changed.');
      else if (result.exitCode === 4 && result.message.startsWith('Fix these')) line(stdout, 'Fix these before you approve.');
      else line(result.exitCode === 4 ? stderr : stdout, result.message);
      return result.exitCode;
    } finally { answers.close(); }
  } catch (error) {
    if (error instanceof Stop) { line(stderr, error.message); return error.exitCode; }
    line(stderr, error.message || 'Approval failed.');
    return 4;
  }
}
