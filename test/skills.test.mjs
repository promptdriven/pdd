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
// 0.1.7: the size that counts is what one agent loads. The main chat loads SKILL.md; each subagent loads one step file
// and the RUNBOOK sections it points to. prompt-story alone also loads the 16 KB guide, and it carries the most real-run rules.
const SKILL_LIMIT = 3072, STEP_LIMIT = 1228, STEP_LIMITS = { 'prompt-story': 1536 };
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
test('SKILLS4: workflow skills have version 2 areas, one step file per step, and stay small', t => {
  for (const [name, areas] of Object.entries(AREAS)) {
    const definition = JSON.parse(read(`${name}/workflow.json`));
    assert.deepEqual(definition, { version: 2, areas: areas.map(([area, steps, optional, gate, then, before]) => ({ name: area, steps, optional, gate, ...(before ? { before } : {}), ...(then ? { then } : {}) })) });
    const steps = [...new Set(areas.flatMap(([, list]) => list))];
    assert.deepEqual(readdirSync(join(skills, name, 'steps')).sort(), steps.map(step => `${step}.md`).sort(), name);
    for (const step of steps) {
      const lines = read(`${name}/steps/${step}.md`).trimEnd().split('\n');
      assert.ok(lines.length <= 15, `${name}/${step} has ${lines.length} lines`);
      const bytes = statSync(join(skills, name, 'steps', `${step}.md`)).size;
      assert.ok(bytes <= (STEP_LIMITS[step] ?? STEP_LIMIT), `${name}/steps/${step}.md is ${bytes} bytes`);
    }
    const { body } = frontmatter(read(`${name}/SKILL.md`));
    for (const [area, list, optional, gate, , before] of areas) {
      const shown = list.map(step => optional.includes(step) ? `${step}?` : step).join(', ');
      assert.ok(body.includes(`${area}: ${shown} → ${before ? `${before}, then ` : ''}gate: ${gate}`), `${name} lists ${area}`);
    }
    const skillBytes = statSync(join(skills, name, 'SKILL.md')).size;
    assert.ok(skillBytes <= SKILL_LIMIT, `${name}/SKILL.md is ${skillBytes} bytes`);
    // The total is for information only: no one agent loads every file.
    t.diagnostic(`${name}: ${filesUnder(join(skills, name)).reduce((sum, file) => sum + statSync(file).size, 0)} bytes in all`);
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
    // pdd-feature shows one line per Story (0.1.6); pdd-bug has one Story.
    assert.match(text, name === 'pdd-feature' ? /Before PR 1, show one `Runtime check` line per Story with its report link, and the Try links/
      : /Before PR 1, show the `Runtime check:` line with its report link and the Try link/);
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
  // Codex calls a skill with $name, Claude Code with /name.
  for (const word of ['Skills: pdd-prompting (the Prompting guide), pdd-feature, pdd-bug, pdd-small-change. Call one with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code, or just ask for it by name.', 'pdd workflow run NAME ISSUE', 'RUNBOOK.md'])
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
const RUNBOOK_SECTIONS = { 2: 'The files', 3: 'Schema rules', 4: 'Expected values', 6: 'Command-line programs (`cli`)',
  7: 'A prompt that calls another prompt', 8: 'Check paths', 9: 'Money and dates', 10: 'AI calls', 13: 'Give your app a screen (app map)',
  14: 'Bug workflow', 17: 'The code PR (PR 2): test vectors and the formal check', 18: 'Patterns: a pure function and a state sequence' };
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
  // 0.1.7: the rule has one home, the step that writes PR 1; SKILL.md names PR 1's parts in its area list.
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const step = read(`${name}/steps/prompt-story.md`);
    assert.match(step, /PR 1 holds only the prompt, the Story and `tests\/\*\.json`/, name);
    assert.match(step, /fail on today's code[^\n]*PR 2/, name);
    assert.match(step, /so merging PR 1 never turns main red\./, name);
    assert.equal(read(`${name}/SKILL.md`).includes('PR 1 holds only'), false, `${name}/SKILL.md repeats the PR 1 rule`);
  }
});

// Wrong (real-user web FLOW B6-B7): a one-line bug in a repo with no prompts got two full module prompts and 709 lines in PR 1.
test('SKILLS12: with no prompt yet, prompt-story writes the smallest prompt for the issue only and keeps PR 1 small', () => {
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const step = read(`${name}/steps/prompt-story.md`);
    assert.match(step, /SMALLEST prompt that owns only the issue's behavior \(one function or one endpoint\), not the whole module/, name);
    assert.match(step, /cases only for the issue's criteria/, name);
    assert.match(step, /PR 1 holds only[^\n]*under about 200 lines/, name);
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
  // "RUNBOOK.md §2–§4" and "(§2–§10)": both ends of each range must exist with their titles.
  for (const name of readdirSync(skills)) for (const file of filesUnder(join(skills, name)).filter(file => file.endsWith('.md') && !/\/(RUNBOOK|guide)\.md$/.test(file)))
    for (const [, first, last] of readFileSync(file, 'utf8').matchAll(/§(\d+)(?:–§(\d+))?/g)) { named.add(Number(first)); if (last) named.add(Number(last)); }
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
    assert.match(check, name === 'pdd-feature' ? /In your `done` summary put only every `Runtime check \(<story>\): …` line/ : /put only pdd check's `Runtime check:` line and the report link in your `done` summary/, name);
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
  // 0.1.7: prompt-story reads RUNBOOK §2 first, and §2 states both rules, so the step does not repeat them.
  const runbook = RUNBOOK();
  assert.ok(runbook.includes('**One rule, one prompt.**') && runbook.includes('A command-line program has one program prompt (section 6).'));
  assert.ok(runbook.includes('Do not name code ("`splitBill(2, 4)` returns …"): the person must read and approve it.'));
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const step = read(`${name}/steps/prompt-story.md`);
    assert.match(step.split('\n').find(text => text.startsWith('- ')), /RUNBOOK\.md §2–§4/, name);
    assert.match(step, /Change one prompt when you can\./, name);
    assert.equal(/owner prompt|function calls/.test(step), false, `${name}/prompt-story repeats RUNBOOK §2`);
  }
  assert.match(read('pdd-bug/steps/reproduce.md'), /`done` summary as the "before" report/);
});

// Wrong (0.1.4): the skills and pdd's help say /pdd-… only, but Codex calls a skill with $pdd-….
test('SKILLS18: no skill text tells a Codex user to type /pdd-…', () => {
  for (const name of readdirSync(skills)) for (const file of filesUnder(join(skills, name)).filter(file => file.endsWith('.md') && !/\/(RUNBOOK|guide)\.md$/.test(file))) {
    const text = readFileSync(file, 'utf8');
    for (const [match] of text.matchAll(/\/pdd-[a-z-]+/g)) assert.match(text, new RegExp(`\\$${match.slice(1)}`), `${file} names ${match} without $${match.slice(1)}`);
  }
});

// Wrong (0.1.6, plan first): one big Story for a request with many behaviors, one test file for all of them,
// one check line for everything, or a change request that redoes every Story.
test('SKILLS19: feature plans many Stories, each with its own test file and check line; changes name one Story', () => {
  assert.match(read('pdd-prompting/SKILL.md'), /A Story is one behavior that a person can check in about a minute: one "I can…" sentence\./);
  const understand = read('pdd-feature/steps/understand.md'), story = read('pdd-feature/steps/prompt-story.md'), check = read('pdd-feature/steps/check.md');
  assert.match(understand, /Count the separate behaviors/);
  assert.match(understand, /`user_stories\/PLAN\.md`: a numbered list, one line per Story, in build order/);
  assert.match(understand, /With 1 behavior, write one Story and no plan\./);
  assert.match(story, /Write every Story in `user_stories\/PLAN\.md`, each with its own `tests\/<story>\.json`/);
  assert.match(story, /Exact data \(seeds, long boards\) goes in the tests; the Story says it in plain words\./);
  // Real 2048 run: one check per Story, then one Story's overall line pasted as the total. The runner sums the lines itself.
  // RUNBOOK §10 says "check the story with the fewest steps first", so the step keeps its own once-for-all rule.
  assert.ok(check.includes('Run `pdd check` ONCE with no Story name, so all Stories are checked together. After fixing, re-check only the failing Stories by name.'));
  assert.equal(check.includes('overall'), false);
  // The format agreed with runner-builder and runtime-client-builder: pdd check's paste lines, joined with "; ".
  assert.ok(check.includes('every `Runtime check (<story>): …` line as pdd check prints it, then `Report (<story>): <url>` for each row of its Reports block, joined with "; "'));
  assert.match(check, /After a re-check, keep the lines of the Stories that passed and replace the re-checked ones\./);
  const skill = read('pdd-feature/SKILL.md');
  assert.match(skill, /At the story gate, give the full paths of the Story files and the plan, and show the plan list\./);
  for (const words of ['"make it one Story"', '"split part 5"', '"change Story 5: …"']) assert.ok(skill.includes(words), words);
  assert.match(skill, /A change request names a Story: redo only that Story and its test file/);
  assert.match(skill, /one `Runtime check` line per Story/);
  assert.match(read('pdd-feature/steps/build.md'), /Build the approved Stories in PLAN\.md order\./);
  assert.match(read('pdd-feature/steps/build.md'), /replay test for each Story/);
  assert.match(read('pdd-feature/steps/verify.md'), /one row group per Story/);
  for (const name of Object.keys(AREAS)) assert.match(read(`${name}/steps/formal.md`), /Cover each Story that has `## Rules to check`\./);
  // pdd-bug and pdd-small-change stay one Story.
  for (const name of ['pdd-bug', 'pdd-small-change'])
    for (const file of [`${name}/SKILL.md`, ...readdirSync(join(skills, name, 'steps')).map(step => `${name}/steps/${step}`)])
      assert.equal(read(file).includes('PLAN.md'), false, file);
});

// Wrong (real-user 2048 run, 0.1.6): the agent wrote its own JSON test format and `board.prompt` files with no Runtime
// interface block, because no step told it the runtime's file format before the check step.
test('SKILLS20: every step that writes prompts or tests reads RUNBOOK §2–§4 first', () => {
  // 0.1.7: prompt-story reads the guide in the same first line; change reads the guide only when it changes a prompt.
  const formats = ' Copy the RUNBOOK examples: `prompts/<name>.prompt.md` with a Runtime interface block, and `tests/<story>.json`.';
  for (const file of ['pdd-feature/steps/prompt-story.md', 'pdd-bug/steps/prompt-story.md'])
    assert.ok(read(file).split('\n').find(text => text.startsWith('- ')).startsWith(`- First read the pdd-prompting skill's guide.md in full and its RUNBOOK.md §2–§4.${formats}`), file);
  assert.equal(read('pdd-small-change/steps/change.md').split('\n').find(text => text.startsWith('- ')),
    `- Before you write a prompt or a test file, read RUNBOOK.md §2–§4 in the pdd-prompting skill.${formats}`);
  const prompting = read('pdd-prompting/SKILL.md');
  assert.ok(prompting.includes('- `RUNBOOK.md`: how to write prompts and tests that the runtime can check (§2–§10), and how to run `pdd check` and `pdd try`.'));
  assert.ok(prompting.includes('Read RUNBOOK.md §2–§4 before you write a prompt or a test file.'));
  const setup = read('pdd-setup/SKILL.md').split('\n');
  const block = setup.slice(setup.indexOf('<!-- pdd:start -->'), setup.indexOf('<!-- pdd:end -->') + 1);
  assert.ok(block.includes('Before you write prompts or tests, read RUNBOOK.md in the pdd-prompting skill.'));
  assert.equal(block.length, 7);
});

// Wrong (Serhan's 2048 session, 0.1.6): the brief's `board.prompt` and node tests beat PDD's formats (about 40 min lost),
// and the person had to ask where the Story was and what to type to approve.
test('SKILLS21: PDD formats win over a brief, PDD tests are runtime tests, and the story gate names paths and the approve sentence', () => {
  assert.ok(read('pdd-feature/steps/understand.md').includes("If the person's brief names other file names or test formats than PDD's (for example `*.prompt` or the repo's own test format), say so in one line and use PDD's, unless the person says otherwise."));
  for (const name of ['pdd-bug', 'pdd-feature']) {
    assert.ok(read(`${name}/steps/prompt-story.md`).includes(" Runtime tests are not the repo's unit tests; the code area adds those."), name);
    const skill = read(`${name}/SKILL.md`);
    assert.match(skill, /[Gg]ive the full paths of the Story files/, name);
    assert.ok(skill.includes(`"Reply 'I approve' to go on, or tell me what to change."`), name);
  }
});

// Wrong (Serhan's 2048 test, 0.1.7): the Try page showed only a form, because no step made an app map.
test('SKILLS22: for a screen, visual writes the app map, prompt-story links the SVG, and the person gets `pdd try <story> --new`', () => {
  const runbook = RUNBOOK();
  assert.ok(runbook.includes('The Try page has a **Screen** tab only when the repo has an app map'));
  assert.ok(runbook.includes('Without `--new`, pdd reuses the open Try and does not send the map.'));
  const visual = read('pdd-feature/steps/visual.md');
  assert.ok(visual.includes('For a screen, also write the app map and its SVG mockups from that design (RUNBOOK §13), so `pdd try` shows the real screen (the Screen tab) and keys or taps work.'));
  assert.match(visual, /app map path in your `done` summary/);
  assert.ok(read('pdd-feature/steps/prompt-story.md').includes("- If visual wrote an app map, write the prompts it names, and put its SVG in the screen prompt's `## Appearance`."));
  const skill = read('pdd-feature/SKILL.md');
  assert.ok(skill.includes('For a screen, recommend visual: it makes the app map.'));
  assert.match(skill.split('\n').find(line => line.startsWith('- At the story gate')), /If visual made an app map, tell the person to run `pdd try <story> --new`/);
  assert.match(read('pdd-feature/steps/try.md'), /`pdd try STORY`[^\n]*with an app map, add `--new`/);
});

// Wrong (2048 test, 0.1.7): 30 tests in a row of one AI call each, and a check refused for its AI-call budget, because
// the steps pointed only to RUNBOOK §2–§4. The writing step says it once; no other file of the skill repeats it.
const POINTERS = '- Also read the RUNBOOK sections that fit: §6 for a CLI, §7 when one prompt calls another, §9 for money and dates, §13 for a screen and its app map. For tests, read §8 (check paths), §10 (AI-call budget: over it, a test is refused at 0 calls) and §18 (ONE call for a whole move list, never 30 in a row).';
test('SKILLS23: the step that writes prompts and tests points to the RUNBOOK sections that fit, once', () => {
  for (const [name, writer] of [['pdd-feature', 'prompt-story'], ['pdd-bug', 'prompt-story'], ['pdd-small-change', 'change']]) {
    assert.equal(read(`${name}/steps/${writer}.md`).split('\n').filter(line => line === POINTERS).length, 1, `${name}/${writer}`);
    for (const file of filesUnder(join(skills, name)).filter(file => !file.endsWith(`/steps/${writer}.md`)))
      assert.equal(/§(10|18)\b/.test(readFileSync(file, 'utf8')), false, `${file} repeats the RUNBOOK pointers`);
  }
});

// Wrong (0.1.7): the person wants to try it before the check and the chat says no; or the chat skips the check.
test('SKILLS24: the story gate may offer a Try before the check; the order stays check, then try', () => {
  for (const name of ['pdd-bug', 'pdd-feature']) {
    const gate = read(`${name}/SKILL.md`).split('\n').find(line => line.startsWith('- At the story gate'));
    assert.ok(gate.includes('You may offer: "You can also open it now with `pdd try <story>` before the check."'), name);
    assert.deepEqual(JSON.parse(read(`${name}/workflow.json`)).areas[1].steps, ['check', 'try'], name);
  }
});

// Wrong (2048 run, 0.1.7): 47 follow-up messages and 15 timed-out waits to the step subagents.
test('SKILLS25: the main chat gives each subagent its full brief at once, then waits once with a long time-out', () => {
  const line = '- Run each step in a new subagent, never reused, so verify never checks its own code. Give it its full brief at once: the step file and file paths, not the chat history. Then wait for it with one long time-out. Do not send small follow-up messages or use short waits.';
  for (const name of Object.keys(AREAS)) assert.ok(read(`${name}/SKILL.md`).split('\n').includes(line), name);
});

// Wrong (0.1.7 trim): a rule grows a second home in the same skill, so the skill grows and the copies drift.
test('SKILLS26: no sentence of a workflow skill is in two of its files', () => {
  const allowed = new Set(['Never change a test to make it pass.']);
  for (const name of Object.keys(AREAS)) {
    const seen = new Map();
    for (const file of filesUnder(join(skills, name)).filter(file => file.endsWith('.md')))
      for (const sentence of readFileSync(file, 'utf8').replace(/^[-#]+ /gm, '').split(/(?<=\.)\s+|\n/).map(text => text.trim()).filter(text => text.length >= 30 && !allowed.has(text))) {
        const where = file.slice(skills.length + 1);
        assert.ok(!seen.has(sentence) || seen.get(sentence) === where, `"${sentence}" is in ${seen.get(sentence)} and ${where}`);
        seen.set(sentence, where);
      }
  }
});
