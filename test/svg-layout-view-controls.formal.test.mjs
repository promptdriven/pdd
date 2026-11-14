import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { temp } from './helpers/runtime-fake.mjs';
import { lintSvgLayouts } from '../src/svg-layout.mjs';

// The oracle is the Story's scope rule: shared controls apply to every view;
// each view's control applies only to that view. Test every presence mask.
test('bounded view control scope and omissions', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const labels = ['Approve', 'Connect', 'Pause'];
  for (const count of [2, 3]) for (const pattern of ['heading', 'list', 'block']) {
    const views = labels.slice(0, count);
    const link = i => `![View](views/view${i}__stacked.ui.svg)`;
    const sections = views.map((label, i) => pattern === 'heading'
      ? `### View ${i}\n${link(i)}\nButton "${label}".\n`
      : pattern === 'list'
        ? `- **View ${i}:** ${link(i)}\n  Button "${label}".\n`
        : `**View ${i}:**\nButton "${label}".\n${link(i)}\n`);
    writeFileSync(join(root, 'screen.prompt.md'), `# Screen\nButton "Help".\n## Appearance\n${sections.join('\n')}\n## Footer\nButton "Escape".\n`);
    const paths = views.map((_, i) => `views/view${i}__stacked.ui.svg`);
    // All 2^(3*count) combinations of two shared and one own control per view.
    for (let mask = 0; mask < 2 ** (3 * count); mask++) {
      const expected = [];
      for (let i = 0; i < count; i++) {
        const required = ['Help', 'Escape', views[i]];
        const present = required.filter((label, bit) => mask & (1 << (3 * i + bit)));
        writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
        for (const label of required) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
      }
      const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
        .filter(w => w.includes('prompt control absent from drawing'))
        .map(w => {
          const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
          assert.ok(match, w);
          return `${match[1]}|${match[2]}`;
        });
      assert.deepEqual(actual.sort(), expected.sort(), `count=${count} pattern=${pattern} mask=${mask}`);
    }
  }
});

test('bounded nested association override and scope end', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const paths = ['views/parent__stacked.ui.svg', 'views/child__stacked.ui.svg'];
  const prose = `# Screen
Button "Help".
## Parent
![Parent](${paths[0]})
Button "Approve".
### Child
![Child](${paths[1]})
Button "Connect".
## Footer
Button "Escape".
`;
  writeFileSync(join(root, 'screen.prompt.md'), prose);
  const requirements = [['Help', 'Approve', 'Escape'], ['Help', 'Connect', 'Escape']];
  for (let mask = 0; mask < 64; mask++) {
    const expected = [];
    for (let i = 0; i < 2; i++) {
      const present = requirements[i].filter((_, bit) => mask & (1 << (3 * i + bit)));
      writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
      for (const label of requirements[i]) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
    }
    const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
      .filter(w => w.includes('prompt control absent from drawing'))
      .map(w => {
        const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
        assert.ok(match, w);
        return `${match[1]}|${match[2]}`;
      });
    assert.deepEqual(actual.sort(), expected.sort(), `nested mask=${mask}`);
  }
});

test('bounded filename state and complete stem associations', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const paths = ['views/now--busy__split-pane.ui.svg', 'views/agents__stacked.ui.svg'];
  for (const headings of [['Now', 'Agents'], ['now--busy__split-pane', 'agents__stacked']]) {
    const prose = `# Screen\nButton "Help".\n## ${headings[0]}\nButton "Approve".\n## ${headings[1]}\nButton "Connect".\n## Drawings\n![Now](${paths[0]})\n![Agents](${paths[1]})\n`;
    writeFileSync(join(root, 'screen.prompt.md'), prose);
    const requirements = [['Help', 'Approve'], ['Help', 'Connect']];
    for (let mask = 0; mask < 16; mask++) {
      const expected = [];
      for (let i = 0; i < 2; i++) {
        const present = requirements[i].filter((_, bit) => mask & (1 << (2 * i + bit)));
        writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
        for (const label of requirements[i]) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
      }
      const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
        .filter(w => w.includes('prompt control absent from drawing'))
        .map(w => {
          const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
          assert.ok(match, w);
          return `${match[1]}|${match[2]}`;
        });
      assert.deepEqual(actual.sort(), expected.sort(), `headings=${headings} mask=${mask}`);
    }
  }
});

test('bounded unassociated parent controls reach drawings outside its subtree', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const paths = ['views/now__stacked.ui.svg', 'views/agents__stacked.ui.svg', 'views/machines__stacked.ui.svg'];
  const own = ['Approve', 'Connect', 'Restart'];
  writeFileSync(join(root, 'screen.prompt.md'), `# Screen
## Appearance
Button "Help".
### Now
![Now](${paths[0]})
Button "Approve".
### Agents
![Agents](${paths[1]})
Button "Connect".
## Machines
![Machines](${paths[2]})
Button "Restart".
`);
  // Every presence assignment for the shared control and each view's own control.
  for (let mask = 0; mask < 64; mask++) {
    const expected = [];
    for (let i = 0; i < paths.length; i++) {
      const required = ['Help', own[i]];
      const present = required.filter((_, bit) => mask & (1 << (2 * i + bit)));
      writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
      for (const label of required) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
    }
    const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
      .filter(w => w.includes('prompt control absent from drawing'))
      .map(w => {
        const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
        assert.ok(match, w);
        return `${match[1]}|${match[2]}`;
      });
    assert.deepEqual(actual.sort(), expected.sort(), `shared parent mask=${mask}`);
  }
});

test('bounded nested drawing metadata associates each generic parent view', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const paths = ['views/alpha__stacked.ui.svg', 'views/beta__stacked.ui.svg'];
  const own = ['Approve', 'Connect'];
  const forms = [
    path => `  - Drawing: ![Image](${path})`,
    path => `  1. ![Image](${path})`,
    path => `  - Preview: ![Image](${path})`,
  ];
  for (const [form, metadata] of forms.entries()) {
    writeFileSync(join(root, 'screen.prompt.md'), `# Screen\nButton "Help".\n- First view\n  Button "Approve".\n${metadata(paths[0])}\n- Second view\n  Button "Connect".\n${metadata(paths[1])}\n`);
    for (let mask = 0; mask < 16; mask++) {
      const expected = [];
      for (let i = 0; i < paths.length; i++) {
        const required = ['Help', own[i]];
        const present = required.filter((_, bit) => mask & (1 << (2 * i + bit)));
        writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
        for (const label of required) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
      }
      const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
        .filter(w => w.includes('prompt control absent from drawing'))
        .map(w => {
          const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
          assert.ok(match, w);
          return `${match[1]}|${match[2]}`;
        });
      assert.deepEqual(actual.sort(), expected.sort(), `metadata form=${form} mask=${mask}`);
    }
  }
});

test('bounded child views do not narrow unassociated parent controls', t => {
  const root = temp(t);
  mkdirSync(join(root, 'views'));
  const paths = ['views/alpha__stacked.ui.svg', 'views/beta__stacked.ui.svg', 'views/gamma__stacked.ui.svg'];
  const own = ['Approve', 'Connect', 'Restart'];
  for (const child of ['named', 'control-owning']) {
    const childTitle = child === 'named' ? 'First view' : 'Drawing';
    writeFileSync(join(root, 'screen.prompt.md'), `# Screen\n## Group\nButton "Help".\n### ${childTitle}\n![Image](${paths[0]})\nButton "Approve".\n### Second view\n![Image](${paths[1]})\nButton "Connect".\n## Outside\n![Image](${paths[2]})\nButton "Restart".\n`);
    for (let mask = 0; mask < 64; mask++) {
      const expected = [];
      for (let i = 0; i < paths.length; i++) {
        const required = ['Help', own[i]];
        const present = required.filter((_, bit) => mask & (1 << (2 * i + bit)));
        writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
        for (const label of required) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
      }
      const actual = lintSvgLayouts({ root, files: ['screen.prompt.md', ...paths] })
        .filter(w => w.includes('prompt control absent from drawing'))
        .map(w => {
          const match = w.match(/ -> (views\/[^:]+): control "([^"]+)": prompt control absent from drawing/);
          assert.ok(match, w);
          return `${match[1]}|${match[2]}`;
        });
      assert.deepEqual(actual.sort(), expected.sort(), `child=${child} mask=${mask}`);
    }
  }
});

test('bounded drawing identity resolves relative to the prompt directory', t => {
  const root = temp(t);
  mkdirSync(join(root, 'prompts'));
  const paths = ['now.ui.svg', 'prompts/now.ui.svg'];
  writeFileSync(join(root, 'prompts/screen.prompt.md'), `# Screen
Button "Help".
## First view
![Image](../now.ui.svg)
Button "Approve".
## Second view
![Image](now.ui.svg)
Button "Connect".
`);
  for (let mask = 0; mask < 16; mask++) {
    const expected = [];
    for (let i = 0; i < paths.length; i++) {
      const required = ['Help', ['Approve', 'Connect'][i]];
      const present = required.filter((_, bit) => mask & (1 << (2 * i + bit)));
      writeFileSync(join(root, paths[i]), `<svg>${present.map(label => `<text>${label}</text>`).join('')}</svg>`);
      for (const label of required) if (!present.includes(label)) expected.push(`${paths[i]}|${label}`);
    }
    const actual = lintSvgLayouts({ root, files: ['prompts/screen.prompt.md', ...paths] })
      .filter(w => w.includes('prompt control absent from drawing'))
      .map(w => {
        const match = w.match(/ -> ([^:]+\.ui\.svg): control "([^"]+)": prompt control absent from drawing/);
        assert.ok(match, w);
        return `${match[1]}|${match[2]}`;
      });
    assert.deepEqual(actual.sort(), expected.sort(), `relative identity mask=${mask}`);
  }
});
