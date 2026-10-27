import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));
const skills = join(root, 'skills');
const read = path => readFileSync(join(skills, path), 'utf8');
// G2: bug and feature stop at PR 1 (prompt PR) and ask before the code area.
// 0.1.3: every code PR ends with a formal step after verify.
const AREAS = {
  'pdd-small-change': [['plan', ['scope'], [], 'approve'], ['build', ['change', 'verify', 'formal'], [], 'pr']],
  // 0.1.4 #13: the person tries it and approves before pdd opens PR 1 ("before":"approve").
  'pdd-bug': [['story', ['reproduce', 'prompt-story'], [], 'approve'], ['prompt-pr', ['check', 'try'], ['try'], 'pr', 'ask-code', 'approve'],
    ['code', ['build', 'verify', 'formal'], [], 'pr']],
  'pdd-feature': [['story', ['understand', 'visual', 'prompt-story'], ['visual'], 'approve'],
    ['prompt-pr', ['check', 'try'], ['try'], 'pr', 'ask-code', 'approve'], ['code', ['build', 'verify', 'formal'], [], 'pr']],
};
const ALL_SKILLS = ['pdd-prompting', 'pdd-setup', ...Object.keys(AREAS)];
const frontmatter = text => {
  const match = text.match(/^---\n([\s\S]*?)\n---\n/);
  assert.ok(match, 'SKILL.md starts with frontmatter');
  return { fields: Object.fromEntries(match[1].split('\n').map(line => [line.slice(0, line.indexOf(':')), line.slice(line.indexOf(':') + 1).trim()])),
    body: text.slice(match[0].length) };
};
const filesUnder = dir => readdirSync(dir, { withFileTypes: true })
  .flatMap(entry => entry.isDirectory() ? filesUnder(join(dir, entry.name)) : [join(dir, entry.name)]);

// Wrong: a skill folder that Codex or Claude cannot load (no name/description, or a name that differs from its folder).
test('SKILLS1: each new skill has standard frontmatter that names its own folder', () => {
  assert.deepEqual(readdirSync(skills).sort(), [...ALL_SKILLS].sort());
  for (const name of ALL_SKILLS) {
    const { fields } = frontmatter(read(`${name}/SKILL.md`));
    assert.equal(fields.name, name);
    assert.ok(fields.description && fields.description.length <= 1024, name);
    // Agents pick a skill on their own only from its description.
    assert.match(fields.description, /Use (it )?when /, name);
  }
});

// Wrong: the skill copy of the guide drifts from docs/prompting-guide.md.
test('SKILLS2: pdd-prompting guide.md and RUNBOOK.md equal the canonical files byte for byte', () => {
  assert.deepEqual(readFileSync(join(skills, 'pdd-prompting/guide.md')), readFileSync(join(root, 'docs/prompting-guide.md')));
  assert.deepEqual(readFileSync(join(skills, 'pdd-prompting/RUNBOOK.md')), readFileSync(join(root, 'RUNBOOK.md')));
  assert.deepEqual(readdirSync(join(skills, 'pdd-prompting')).sort(), ['RUNBOOK.md', 'SKILL.md', 'guide.md', 'review.md']);
});

// Wrong: the core page grows past one page or loses the core rules that pdd session inlines.
test('SKILLS3: pdd-prompting SKILL.md is at most 400 words with 1 to 8 core rules', () => {
  const { body } = frontmatter(read('pdd-prompting/SKILL.md'));
  assert.ok(body.split(/\s+/).filter(Boolean).length <= 400);
  const section = body.split(/^## /m).find(part => part.startsWith('Core rules\n'));
  const rules = section.split('\n').filter(line => line.startsWith('- '));
  assert.ok(rules.length >= 1 && rules.length <= 8, String(rules.length));
});

// Wrong: workflow.json, SKILL.md areas and the step files disagree, or a workflow outgrows the size limits.
test('SKILLS4: workflow skills have version 2 areas, one step file per step, and stay small', () => {
  for (const [name, areas] of Object.entries(AREAS)) {
    const definition = JSON.parse(read(`${name}/workflow.json`));
    assert.deepEqual(definition, { version: 2, areas: areas.map(([area, steps, optional, gate, then, before]) => ({ name: area, steps, optional, gate, ...(before ? { before } : {}), ...(then ? { then } : {}) })) });
    const steps = [...new Set(areas.flatMap(([, list]) => list))];
    assert.deepEqual(readdirSync(join(skills, name, 'steps')).sort(), steps.map(step => `${step}.md`).sort(), name);
    for (const step of steps) {
      const lines = read(`${name}/steps/${step}.md`).trimEnd().split('\n');
      assert.ok(lines.length <= 15, `${name}/${step} has ${lines.length} lines`);
    }
    const { body } = frontmatter(read(`${name}/SKILL.md`));
    for (const [area, list, optional, gate, , before] of areas) {
      const shown = list.map(step => optional.includes(step) ? `${step}?` : step).join(', ');
      assert.ok(body.includes(`${area}: ${shown} → ${before ? `${before}, then ` : ''}gate: ${gate}`), `${name} lists ${area}`);
    }
    const bytes = filesUnder(join(skills, name)).reduce((sum, file) => sum + statSync(file).size, 0);
    // 6.5 KB: the PR 2 method lives in RUNBOOK section 17; the steps only point to it.
    // pdd-bug needs the most room: the story-gate verdict lines, the real-user rules (0.1.3) and the 0.1.4 Story rules.
    assert.ok(bytes <= 6656, `${name} is ${bytes} bytes`);
    assert.deepEqual(readdirSync(join(skills, name)).sort(), ['SKILL.md', 'steps', 'workflow.json']);
  }
});

// Wrong: steps that do not write prompts load the 16 KB guide, or prompt-story and check do not load what they need.
test('SKILLS5: only prompt-writing steps read the guide; check reads the core page and review.md', () => {
  for (const name of Object.keys(AREAS)) {
    for (const file of readdirSync(join(skills, name, 'steps'))) {
      const text = read(`${name}/steps/${file}`), step = file.slice(0, -3);
      const readsGuide = /guide\.md/.test(text);
      if (step === 'prompt-story') assert.match(text, /guide\.md in full/, `${name}/${step}`);
      else if (name === 'pdd-small-change' && step === 'change') assert.match(text, /prompt[\s\S]*guide\.md in full/);
      else assert.equal(readsGuide, false, `${name}/${step} must not read the guide`);
      if (step === 'check') { assert.match(text, /pdd-prompting/); assert.match(text, /SKILL\.md/); assert.match(text, /review\.md/);
        assert.match(text, /If the pdd-prompting skill has a RUNBOOK\.md/); assert.match(text, /pdd check/); assert.match(text, /`done` summary/); }
    }
    assert.equal(/guide\.md/.test(read(`${name}/SKILL.md`)), false, `${name}/SKILL.md must not send every step to the guide`);
  }
});

// Wrong: runtime steps run without a runbook, an agent may edit a test until it passes, or the code PR starts without the person.
test('SKILLS6: runtime lines depend on RUNBOOK.md, expected values stay with the person, and PR 1 asks before code', () => {
  for (const name of Object.keys(AREAS)) assert.match(read(`${name}/SKILL.md`), /A person decides expected values\. Never change a test to make it pass\./);
  for (const name of ['pdd-bug', 'pdd-feature']) {
    assert.match(read(`${name}/steps/try.md`), /If the pdd-prompting skill has a RUNBOOK\.md[^\n]*`pdd try STORY`[^\n]*Try link before the gate/);
    const text = read(`${name}/SKILL.md`);
    assert.match(text, /Before PR 1, show the `Runtime check:` line with its report link and the Try link/);
    assert.match(text, /pdd opens PR 1 only after the approval\. Then show the PR 1 link/);
    // The same words as pdd's gate text, so a person who stops knows how to make the code PR later.
    assert.ok(text.includes('"Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve N`."'), name);
  }
  assert.match(read('pdd-bug/steps/reproduce.md'), /If a prompt owns this behavior[^\n]*section 14[^\n]*`pdd check`[^\n]*CURRENT prompt/);
  assert.match(read('pdd-bug/steps/check.md'), /before ✗ → after ✓/);
  for (const file of ['pdd-bug', 'pdd-feature', 'pdd-small-change'].flatMap(name => [`${name}/SKILL.md`, ...readdirSync(join(skills, name, 'steps')).map(step => `${name}/steps/${step}`)]))
    assert.equal(/session intro/.test(read(file)), false, file);
});

// Wrong: the setup skill and pdd setup write different blocks, or the block grows into a pasted guide.
test('SKILLS7: pdd-setup states one marked block of at most 10 lines that names every PDD skill', () => {
  const text = read('pdd-setup/SKILL.md'), lines = text.split('\n');
  const block = lines.slice(lines.indexOf('<!-- pdd:start -->'), lines.indexOf('<!-- pdd:end -->') + 1);
  assert.ok(block.length >= 3 && block.length <= 10, `${block.length} lines`);
  for (const word of ['/pdd-prompting', '/pdd-feature', '/pdd-bug', '/pdd-small-change', 'pdd workflow run NAME ISSUE', 'RUNBOOK.md'])
    assert.ok(block.join('\n').includes(word), word);
  assert.equal(lines.filter(line => line === '<!-- pdd:start -->').length, 1);
  assert.ok(Buffer.byteLength(text) <= 3584);
});

// Wrong (plan D4): in a normal chat the agent writes a prompt and tests but never runs the runtime check unless asked.
test('SKILLS8: after prompt work the agent runs pdd check on its own, offers pdd try, and small-change checks before verify', () => {
  const prompting = read('pdd-prompting/SKILL.md');
  assert.ok(prompting.includes('After you write or change a prompt, its Story and its test file, run `pdd check` as RUNBOOK.md says, and show the person the `Runtime check:` line and the report link. Then offer `pdd try STORY` so they can use it by hand. If a check fails, show it; never change the expected value yourself.'));
  assert.match(read('pdd-small-change/steps/change.md'), /If you changed a prompt that has a test file, run `pdd check` as [^\n]*RUNBOOK\.md says before verify\./);
});

// Wrong (0.1.3): the steps repeat RUNBOOK section 17 (two homes for one method), or the runbook copy lacks it.
const RUNBOOK = () => readFileSync(join(skills, 'pdd-prompting/RUNBOOK.md'), 'utf8');
// Every "section N" that a skill names, with the RUNBOOK title it must have. Add a row when a skill names a new section.
const RUNBOOK_SECTIONS = { 14: 'Bug workflow', 17: 'The code PR (PR 2): test vectors and the formal check' };
const section14 = () => RUNBOOK().slice(RUNBOOK().indexOf(`## 17. ${RUNBOOK_SECTIONS[17]}`));

// Wrong (0.1.3 vectors): PR 2 tests drift from the approved PR 1 cases, or a failing case is hidden.
test('SKILLS9: build and verify point to RUNBOOK section 17 for the replay test, and a failure loops back to build twice', () => {
  for (const word of ['tests/<story>.json', 'Never edit it in PR 2', 'replay test', 'planted mistake', 'A crash does not count', 'Not replayed', 'never a pass', 'unchanged since PR 1', '✗ N vectors fail'])
    assert.ok(section14().includes(word), `RUNBOOK section 17: ${word}`);
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const build = read(`${name}/steps/build.md`), verify = read(`${name}/steps/verify.md`), skill = read(`${name}/SKILL.md`);
    assert.match(build, /replay test[^\n]*section 17 of RUNBOOK\.md/, name);
    assert.match(build, /Never edit `tests\/<story>\.json`/, name);
    assert.match(verify, /section 17 of RUNBOOK\.md/, name);
    assert.match(verify, /planted mistake/, name);
    assert.match(verify, /table/, name);
    assert.equal(verify.includes('| Case | Criterion |'), false, `${name}: the table format lives in the RUNBOOK`);
    assert.match(skill, /back to build in a new subagent, at most 2 times/, name);
    assert.ok(skill.includes('"✗ N vectors fail"'), name);
    assert.match(read(`${name}/steps/prompt-story.md`), /## Rules to check/, name);
  }
});

// Wrong (0.1.3 formal): the formal step repeats the method, or the runbook loses the honest result words.
test('SKILLS10: every workflow has a short formal step that points to RUNBOOK section 17', () => {
  for (const word of ['Proved (bounded)', 'Proved (solver)', 'Failed + counterexample', 'Not run + reason', 'Not applicable + reason', 'Rules to check',
    'EVERY input', 'Z3', 'CrossHair', 'planted mistake must fail the formal check', 'Do not commit raw logs'])
    assert.ok(section14().includes(word), `RUNBOOK section 17: ${word}`);
  for (const name of Object.keys(AREAS)) {
    const text = read(`${name}/steps/formal.md`);
    assert.match(text, /section 17 of RUNBOOK\.md/);
    assert.match(text, /## Formal check/);
    assert.ok(text.trimEnd().split('\n').length <= 8, `${name}/formal.md is short`);
  }
  assert.equal(read('pdd-bug/steps/formal.md'), read('pdd-feature/steps/formal.md'));
  assert.equal(read('pdd-bug/steps/formal.md'), read('pdd-small-change/steps/formal.md'));
});

// Wrong (real-user ISSUES 1 and 3): reproduce skips the prompt check in silence, or PR 1 adds repo tests that turn main red.
test('SKILLS11: reproduce says plainly when no prompt exists, and PR 1 holds only the prompt, the Story and tests/*.json', () => {
  // RUNBOOK section 14 owns the exact sentence; reproduce points to it.
  assert.ok(RUNBOOK().includes('"No prompt exists yet for this behavior, so the bug can only be'));
  assert.match(read('pdd-bug/steps/reproduce.md'), /If no prompt exists, say so plainly, in the words of section 14\./);
  for (const name of ['pdd-bug', 'pdd-feature']) {
    for (const file of [`${name}/SKILL.md`, `${name}/steps/prompt-story.md`]) {
      const text = read(file);
      assert.match(text, /PR 1 holds only the prompt, the Story and `tests\/\*\.json`/, file);
      assert.match(text, /fail on today's code[^\n]*PR 2/, file);
    }
    assert.match(read(`${name}/SKILL.md`), /Merging PR 1 must never turn main red\./);
  }
});

// Wrong (real-user web FLOW B6-B7): a one-line bug in a repo with no prompts got two full module prompts and 709 lines in PR 1.
test('SKILLS12: with no prompt yet, prompt-story writes the smallest prompt for the issue only and keeps PR 1 small', () => {
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const step = read(`${name}/steps/prompt-story.md`);
    assert.match(step, /SMALLEST prompt that owns only the issue's behavior \(one function or one endpoint\), not the whole module/, name);
    assert.match(step, /cases only for the issue's criteria/, name);
    assert.match(step, /PR 1 under about 200 lines/, name);
    assert.ok(read(`${name}/SKILL.md`).includes('"adopt PDD for this module"'), name);
  }
});

// Wrong (owner, 0.1.3): the bug story gate buries the answer; the person must see first where the bug is.
test('SKILLS13: the bug story gate starts with exactly one of three verdict lines', () => {
  const skill = read('pdd-bug/SKILL.md');
  assert.match(skill, /At the story gate, start with one verdict line, then the details/);
  for (const verdict of ['Verdict: the bug is in the PROMPT (its check fails on the issue\'s case).',
    'Verdict: the prompt is right; the bug is only in the CODE.', 'Verdict: no prompt covers this yet; the bug can only be in the code.'])
    assert.ok(skill.includes(`"${verdict}"`), verdict);
});

// Wrong (RUNBOOK renumbered in 0.1.3): a skill sends the agent to a section that moved or does not exist.
test('SKILLS14: every RUNBOOK section that a skill names exists with the expected title', () => {
  const runbook = RUNBOOK(), named = new Set();
  for (const name of readdirSync(skills)) for (const file of filesUnder(join(skills, name)).filter(file => file.endsWith('.md') && !/\/(RUNBOOK|guide)\.md$/.test(file)))
    for (const [, number] of readFileSync(file, 'utf8').matchAll(/section (\d+) of RUNBOOK\.md/g)) named.add(Number(number));
  assert.ok(named.size >= 2, [...named].join(','));
  for (const number of named) {
    assert.ok(RUNBOOK_SECTIONS[number], `section ${number} is named by a skill but has no expected title in this test`);
    assert.ok(runbook.split('\n').includes(`## ${number}. ${RUNBOOK_SECTIONS[number]}`), `RUNBOOK.md has no "## ${number}. ${RUNBOOK_SECTIONS[number]}"`);
  }
  assert.ok(runbook.includes('**The formal check'), 'formal.md names "The formal check" in section 17');
});

// Wrong (0.1.3): a PR body shows the agent's machine paths or raw logs.
test('SKILLS15: every verify step keeps verify.md to commands and results, with no local paths or raw logs', () => {
  for (const name of Object.keys(AREAS))
    assert.ok(read(`${name}/steps/verify.md`).includes('- verify.md shows commands and results only: no local absolute paths (like /Users/… or /home/…) and no raw logs.'), name);
});

// Wrong (runner real run, 0.1.3): the check step wrote its evidence into verify.md and PR 2 grew to 881 lines;
// or the agent asks the person mid-step and pdd still reports "the agent works".
test('SKILLS16: check notes go to <run folder>/check.md, and every workflow runs pdd workflow ask before a mid-step question', () => {
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const check = read(`${name}/steps/check.md`);
    assert.match(check, /Write your notes to `<run folder>\/check\.md`, never to verify\.md\./, name);
    assert.match(check, /put only pdd check's `Runtime check:` line and the report link in your `done` summary/, name);
  }
  assert.match(read('pdd-small-change/steps/change.md'), /`pdd check`[^\n]*Keep its notes out of verify\.md\./);
  // A question dialog (request_user_input) blocks the chat, and Herdr then refuses pdd's text, so `changes` fails.
  for (const name of Object.keys(AREAS))
    assert.ok(read(`${name}/SKILL.md`).includes('- When you need the person\'s answer in the middle of a step, run `<pdd> workflow ask "<question>"` first. Then ask it in a plain chat message (never a question dialog such as request_user_input) and end your turn. The person answers in the chat or with `pdd workflow changes N "answer"`.'), name);
});

// Wrong (0.1.4 #12, #17, before link): Stories read like code, one rule gets two owner prompts (a CLI's rule copied into
// the whole-CLI prompt and a module prompt), or bug PR 1 loses the report of the check on the current prompt.
test('SKILLS17: Stories in the person\'s words, one owner prompt per rule, and the bug "before" report link', () => {
  const prompting = read('pdd-prompting/SKILL.md');
  assert.match(prompting, /Story in the person's words[^\n]*no function calls or type names/);
  assert.match(prompting, /Give each rule one owner prompt\./);
  assert.match(prompting, /For a CLI, say if a rule belongs to the whole-CLI prompt or to one module's prompt\./);
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const step = read(`${name}/steps/prompt-story.md`);
    assert.match(step, /Story in the person's words[^\n]*no function calls or type names/, name);
    assert.match(step, /Change one prompt when you can\./, name);
    assert.match(step, /one owner prompt[^\n]*whole-CLI prompt[^\n]*module's prompt/, name);
  }
  assert.match(read('pdd-bug/steps/reproduce.md'), /`done` summary as the "before" report/);
});
