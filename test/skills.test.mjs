import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs';
import { dirname, join, normalize } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));
const skills = join(root, 'skills');
const read = rel => readFileSync(join(skills, rel), 'utf8');

const RETIRED_SKILLS = ['pdd-setup', 'pdd-bug', 'pdd-feature', 'pdd-graph', 'pdd-product', 'pdd-prompting', 'pdd-small-change'];
const EXPECTED_REFERENCES = [
  'BREAK-IT.md',
  'PROMPT-REVIEW-RULES.md',
  'SOLVE.md',
  'adversarial-audit.md',
  'formal.md',
  'ports-and-cli.md',
  'product.md',
  'prompting.md',
  'stories.md',
  'ui-and-screens.md',
  'verification.md',
];

const filesUnder = dir => readdirSync(dir, { withFileTypes: true })
  .flatMap(entry => entry.isDirectory() ? filesUnder(join(dir, entry.name)) : [join(dir, entry.name)]);

const slugify = heading => heading
  .toLowerCase()
  .replace(/[`()]/g, '')
  .replace(/[^a-z0-9\s-]/g, '')
  .trim()
  .replace(/\s+/g, '-');

test('SKILLS1: literally one visible /pdd skill, with legacy split skill folders retired', () => {
  assert.deepEqual(readdirSync(skills).sort(), ['pdd']);
  for (const name of RETIRED_SKILLS) {
    assert.equal(existsSync(join(skills, name)), false, `${name} is retired`);
  }

  const pddSkill = read('pdd/SKILL.md');
  assert.match(pddSkill, /^---\n[\s\S]*?name: pdd\n[\s\S]*?\n---\n/);
  assert.doesNotMatch(pddSkill, /^disable-model-invocation:\s*true$/m);
  const pddLines = pddSkill.trimEnd().split('\n').length;
  assert.ok(pddLines <= 140, `skills/pdd/SKILL.md should stay concise (${pddLines} lines)`);
});

test('SKILLS2: skills/pdd co-located references exist, stay bounded, and contain zero dead commands', () => {
  assert.deepEqual(readdirSync(join(skills, 'pdd/references')).sort(), EXPECTED_REFERENCES);
  const pddSkill = read('pdd/SKILL.md');
  for (const ref of EXPECTED_REFERENCES) {
    assert.ok(pddSkill.includes(`references/${ref}`), `skills/pdd/SKILL.md links references/${ref}`);
    const bytes = statSync(join(skills, 'pdd/references', ref)).size;
    assert.ok(bytes > 200 && bytes <= 32768, `references/${ref} size (${bytes} bytes) within bounds`);
  }

  for (const file of filesUnder(join(skills, 'pdd'))) {
    const text = readFileSync(file, 'utf8');
    assert.doesNotMatch(text, /\bpdd (?:check|try|session)\b/, `dead command in ${file}`);
  }
});

test('SKILLS3: zero broken local markdown links or heading anchors inside skills/', () => {
  const mdFiles = filesUnder(skills).filter(f => f.endsWith('.md'));
  const slugsByFile = new Map();
  const slugsFor = absPath => {
    if (!slugsByFile.has(absPath)) {
      const content = readFileSync(absPath, 'utf8');
      slugsByFile.set(absPath, new Set(
        [...content.matchAll(/^#{1,6}\s+(.+)$/gm)].map(([, h]) => slugify(h)),
      ));
    }
    return slugsByFile.get(absPath);
  };

  for (const absFile of mdFiles) {
    const rel = absFile.slice(root.length + (root.endsWith('/') ? 0 : 1));
    const text = readFileSync(absFile, 'utf8')
      .replace(/```[\s\S]*?```/g, '')
      .replace(/`[^`\n]+`/g, '');
    for (const [, rawTarget] of text.matchAll(/\[[^\]]+\]\(([^)\s]+)\)/g)) {
      if (/^(?:https?:|mailto:|#)/i.test(rawTarget)) continue;
      const [filePart, anchor] = rawTarget.split('#');
      if (!filePart) continue;
      const resolved = normalize(join(dirname(absFile), filePart));
      assert.ok(existsSync(resolved), `${rel}: broken link target ${rawTarget}`);
      if (anchor && resolved.endsWith('.md')) {
        assert.ok(slugsFor(resolved).has(anchor), `${rel}: broken heading anchor #${anchor} in ${filePart}`);
      }
    }
  }
});

test('SKILLS4: root guide mirrors stay removed and autopilot job rules live in src/autopilot/job-rules.md', () => {
  assert.equal(existsSync(join(root, 'src/autopilot/job-rules.md')), true);
  assert.equal(existsSync(join(skills, 'pdd/references/autopilot-job-rules.md')), false, 'autopilot-job-rules moved out of user-facing skills/');
  assert.equal(existsSync(join(root, 'RUNBOOK.md')), false, 'root RUNBOOK.md mirror removed');
  assert.equal(existsSync(join(root, 'docs/prompting-guide.md')), false, 'docs/prompting-guide.md mirror removed');
  assert.equal(existsSync(join(root, 'docs/story-guide.md')), false, 'docs/story-guide.md mirror removed');
});
