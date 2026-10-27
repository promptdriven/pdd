import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('..', import.meta.url));
const skills = join(root, 'skills');
const read = path => readFileSync(join(skills, path), 'utf8');
const AREAS = {
  'pdd-small-change': [['plan', ['scope'], [], 'approve'], ['build', ['change', 'verify'], [], 'pr']],
  'pdd-bug': [['solution', ['reproduce', 'prompt-story', 'check', 'try'], ['try'], 'approve'], ['build', ['build', 'verify'], [], 'pr']],
  'pdd-feature': [['solution', ['understand', 'visual'], ['visual'], 'approve'],
    ['story', ['prompt-story', 'check', 'try'], ['try'], 'approve'], ['build', ['build', 'verify'], [], 'pr']],
};
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
  for (const name of ['pdd-prompting', ...Object.keys(AREAS)]) {
    const { fields } = frontmatter(read(`${name}/SKILL.md`));
    assert.equal(fields.name, name);
    assert.ok(fields.description && fields.description.length <= 1024, name);
  }
});

// Wrong: the skill copy of the guide drifts from docs/prompting-guide.md.
test('SKILLS2: pdd-prompting guide.md equals the canonical guide byte for byte', () => {
  assert.deepEqual(readFileSync(join(skills, 'pdd-prompting/guide.md')), readFileSync(join(root, 'docs/prompting-guide.md')));
  assert.deepEqual(readdirSync(join(skills, 'pdd-prompting')).sort(), ['SKILL.md', 'guide.md', 'review.md']);
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
    assert.deepEqual(definition, { version: 2, areas: areas.map(([area, steps, optional, gate]) => ({ name: area, steps, optional, gate })) });
    const steps = [...new Set(areas.flatMap(([, list]) => list))];
    assert.deepEqual(readdirSync(join(skills, name, 'steps')).sort(), steps.map(step => `${step}.md`).sort(), name);
    for (const step of steps) {
      const lines = read(`${name}/steps/${step}.md`).trimEnd().split('\n');
      assert.ok(lines.length <= 15, `${name}/${step} has ${lines.length} lines`);
    }
    const { body } = frontmatter(read(`${name}/SKILL.md`));
    for (const [area, list, optional, gate] of areas) {
      const shown = list.map(step => optional.includes(step) ? `${step}?` : step).join(', ');
      assert.ok(body.includes(`${area}: ${shown} → gate: ${gate}`), `${name} lists ${area}`);
    }
    const bytes = filesUnder(join(skills, name)).reduce((sum, file) => sum + statSync(file).size, 0);
    assert.ok(bytes <= 3072, `${name} is ${bytes} bytes`);
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
        assert.match(text, /RUNBOOK\.md/); assert.match(text, /pdd check/); assert.match(text, /<pdd> --runbook/); }
    }
    assert.equal(/guide\.md/.test(read(`${name}/SKILL.md`)), false, `${name}/SKILL.md must not send every step to the guide`);
  }
});
