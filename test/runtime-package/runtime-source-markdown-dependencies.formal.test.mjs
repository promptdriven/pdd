import assert from 'node:assert/strict';
import test from 'node:test';
import { markdownDefinitions, markdownLinks, markdownSectionText } from '../../src/runtime/runtime-markdown.mjs';

// Independent oracle: approved markdown-code-dependencies Story AC1–AC4 and
// runtime-markdown.prompt.md. These finite grammars are deliberate subsets of
// Markdown, not a claim about all Markdown documents or caller path policy.
// Every word over {space, tab} of length 0..5 is tested: 63 words. Tabs advance
// to the next absolute four-column stop, after the explicit container prefix.
const whitespace = [''];
for (let length = 1; length <= 5; length++) {
  for (let bits = 0; bits < 2 ** length; bits++) {
    whitespace.push(Array.from({ length }, (_, i) => bits & (1 << i) ? '\t' : ' ').join(''));
  }
}
const containers = [
  { name: 'root', prefix: '', boundary: '# Example\n\n', paragraph: 'Paragraph\n' },
  { name: 'quote', prefix: '> ', boundary: '> Quote\n>\n', paragraph: '> Paragraph\n' },
  { name: 'list', prefix: '  ', boundary: '- Item\n\n', paragraph: '- Paragraph\n' },
  { name: 'quote-list', prefix: '>   ', boundary: '> - Item\n>\n', paragraph: '> - Paragraph\n' },
];
const payloads = ['![hidden](hidden.svg)', '![target]', '[target]: hidden.svg'];
const endOfLines = ['\n', '\r\n'];
const blank = text => text.replace(/[^\r\n]/g, ' ');
const columns = (text, initial = 0) => {
  let column = initial;
  for (const character of text) column += character === '\t' ? 4 - column % 4 : 1;
  return column - initial;
};

// Continue after semantic failures so the old-code control exercises the whole
// finite domain. Retain the first six counterexamples and the exact failure count.
function checkDomain(name, visit) {
  let count = 0, failures = 0;
  const examples = [];
  const check = (input, assertion) => {
    count++;
    try { assertion(); }
    catch (error) {
      if (!(error instanceof assert.AssertionError)) throw error;
      failures++;
      if (examples.length < 6) examples.push({ input, message: error.message });
    }
  };
  visit(check);
  assert.equal(failures, 0, `${name}: ${failures}/${count} semantic failures; counterexamples=${JSON.stringify(examples)}`);
}

test('bounded indentation: all 3,024 documents preserve prose and exclude only code', () => {
  // 63 whitespace words × 4 containers × 2 paragraph states × 3 payloads ×
  // 2 line endings = 3,024 documents. Each document checks the complete view,
  // exact offsets/newlines, and both imagesOnly values at the public scanners.
  assert.equal(whitespace.length, 63);
  checkDomain('indented-code exclusion', check => {
    for (const container of containers) for (const indent of whitespace) {
      for (const paragraph of [false, true]) for (const payload of payloads) {
        for (const eol of endOfLines) {
          const header = (paragraph ? container.paragraph : container.boundary).replaceAll('\n', eol);
          const row = container.prefix + indent + payload;
          const after = container.prefix + '![after](after.svg)' + eol;
          const source = header + row + eol + after;
          const code = !paragraph && columns(indent, container.prefix.length) >= 4;
          const expected = header + (code ? blank(row) : row) + eol + after;
          check({ container: container.name, indent, paragraph, payload, eol }, () => {
            const actual = markdownSectionText(source);
            assert.equal(actual, expected, 'prose view must mask exactly the code line');
            assert.equal(actual.length, source.length, 'offsets must survive masking');
            assert.deepEqual([...actual.matchAll(/[\r\n]/g)].map(match => match.index),
              [...source.matchAll(/[\r\n]/g)].map(match => match.index), 'line endings must keep their offsets');
            for (const imagesOnly of [false, true]) {
              const expectedLinks = code || payload.startsWith('[target]:') ? ['after.svg']
                : payload === '![target]' ? ['after.svg', 'hidden.svg'] : ['hidden.svg', 'after.svg'];
              assert.deepEqual(markdownLinks(actual, new Map([['target', 'hidden.svg']]), imagesOnly), expectedLinks);
            }
          });
        }
      }
    }
  });
});

test('bounded marker parity: all 240 marker/form/filter combinations', () => {
  // Ordinary markers: 5 slash runs. Image markers: 5 before ! × 5 before [.
  // Each of these 30 prefixes is checked with 4 forms × 2 imagesOnly values.
  // The full-reference suffix remains a genuine shortcut when its first [ is
  // escaped. A skipped opening must not consume this independently valid use.
  const prefixes = [];
  for (let brackets = 0; brackets <= 4; brackets++) prefixes.push({ brackets, image: false, bangs: 0 });
  for (let bangs = 0; bangs <= 4; bangs++) for (let brackets = 0; brackets <= 4; brackets++) {
    prefixes.push({ brackets, image: true, bangs });
  }
  const forms = [
    { name: 'inline', suffix: '[label](real.svg)', target: 'real.svg' },
    { name: 'full', suffix: '[label][target]', target: 'target.svg' },
    { name: 'collapsed', suffix: '[label][]', target: 'label.svg' },
    { name: 'shortcut', suffix: '[label]', target: 'label.svg' },
  ];
  checkDomain('marker backslash parity', check => {
    for (const prefix of prefixes) for (const form of forms) for (const imagesOnly of [false, true]) {
      const marker = (prefix.image ? '\\'.repeat(prefix.bangs) + '!' : '') + '\\'.repeat(prefix.brackets);
      const source = marker + form.suffix;
      const bracketActive = prefix.brackets % 2 === 0;
      const imageActive = prefix.image && prefix.bangs % 2 === 0 && prefix.brackets === 0;
      const residualReference = !bracketActive && form.name === 'full' && !imagesOnly;
      const expected = (bracketActive && (!imagesOnly || imageActive)) || residualReference ? [form.target] : [];
      check({ source, imagesOnly }, () => {
        assert.deepEqual(markdownLinks(source, new Map([['label', 'label.svg'], ['target', 'target.svg']]), imagesOnly), expected);
      });
    }
  });
});

test('preservation witnesses: code scope, definitions, destination spelling and existing masks', () => {
  // Six explicit grammar witnesses supplement the complete domains above.
  // Every mask is authored from block boundaries, never from parser output.
  const witnesses = [
    { source: '# Example\n\n    ![code](hidden.svg)\n\n    ![code2](hidden2.svg)\n![real](real.svg)\n',
      hidden: ['    ![code](hidden.svg)', '    ![code2](hidden2.svg)'], links: ['real.svg'] },
    { source: '> Quote\n>\n>     ![code](hidden.svg)\n![outside](outside.svg)\n',
      hidden: ['>     ![code](hidden.svg)'], links: ['outside.svg'] },
    { source: '- Item\n\n      ![code](hidden.svg)\n![outside](outside.svg)\n',
      hidden: ['      ![code](hidden.svg)'], links: ['outside.svg'] },
    { source: '# Definitions\r\n\r\n \t[target]: hidden.svg\r\n\r\n[ Target ]: <real.svg>\r\n[TARGET]: later.svg\r\n![ref][ target ]\r\n',
      hidden: [' \t[target]: hidden.svg'], links: ['real.svg'], definitions: [['target', 'real.svg']] },
    { source: '# Examples\n\n```md\n![code](hidden.svg)\n```\n\n~~~\n![tilde](tilde.svg)\n~~~\n\nLead `![span](span.svg)` <!-- ![comment](comment.svg) --> ![real](real.svg)\n',
      hidden: ['```md', '![code](hidden.svg)', '```', '~~~', '![tilde](tilde.svg)', '~~~', '`![span](span.svg)`', '<!-- ![comment](comment.svg) -->'], links: ['real.svg'] },
    { source: '# Real\n\n![nested](folder/a(b).svg "Title") [angle](<space name.md>) [escaped](a\\(b\\).md) [again](<space name.md>) ![ref][target]\n[target]: target.svg\n',
      hidden: [], links: ['folder/a(b).svg', 'space name.md', 'a(b).md', 'space name.md', 'target.svg'], images: ['folder/a(b).svg', 'target.svg'] },
  ];
  checkDomain('preservation witnesses', check => {
    for (const witness of witnesses) check({ source: witness.source }, () => {
      let expected = witness.source, cursor = 0;
      for (const hidden of witness.hidden) {
        const index = expected.indexOf(hidden, cursor);
        assert.notEqual(index, -1, 'witness must identify an authored example');
        expected = expected.slice(0, index) + blank(hidden) + expected.slice(index + hidden.length);
        cursor = index + hidden.length;
      }
      const actual = markdownSectionText(witness.source);
      assert.equal(actual, expected);
      const definitions = markdownDefinitions(actual);
      if (witness.definitions) assert.deepEqual([...definitions], witness.definitions);
      assert.deepEqual(markdownLinks(actual, definitions), witness.links);
      assert.deepEqual(markdownLinks(actual, definitions, true), witness.images ?? witness.links);
    });
  });
});
