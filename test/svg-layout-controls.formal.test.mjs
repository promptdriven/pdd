import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { lintSvgLayouts } from '../src/svg-layout.mjs';
import { temp } from './helpers/runtime-fake.mjs';

// Independent formal oracle derived strictly from user_stories/svg-layout-controls.md
// ("Rules to check") and prompts/cli/svg-layout.prompt.md ("Parts and advice").
// Bounded exhaustive check over 2,304 generated (prompt, .ui.svg) pairs:
//   1. Rule 1: 9 non-control HTML elements × 10 non-control attributes × 2 quote styles
//      × 2 Markdown wrappers × 2 button-adjacency modes = 720 combinations.
//   2. Rules 2 & 3: 2 quote styles × 3 internal sentence-punctuation marks × 3 non-control
//      lead-ins × 3 inter-quote connectors × 4 negated control clauses × 2 SVG help-text
//      presence states × 2 affirmative "Start" presence states = 864 combinations.
//   3. Rule 4: 10 affirmative HTML/prose control declarations × 4 SVG presence modes
//      × 3 HTML container/hidden-input noise variants × 2 multi-sentence/negated prose
//      noise variants × 3 Markdown/section wrappers (direct, code-span/list, fenced/section)
//      = 720 combinations.

const PROMPT_FILE = 'screen.prompt.md';
const DRAWING_FILE = 'screen.ui.svg';
const PREFIX = `Warning: SVG layout ${PROMPT_FILE} -> ${DRAWING_FILE}: `;
const controlWarning = value => `${PREFIX}control "${value}": prompt control absent from drawing.`;

function xmlEscape(text) {
  return text
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;');
}

function quoteAttr(quote, value) {
  return `${quote}${value}${quote}`;
}

const NON_CONTROL_ELEMENTS = [
  { name: 'div', render: (q, attr) => `<div id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</div>`, text: 'Panel ready' },
  { name: 'main', render: (q, attr) => `<main id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</main>`, text: 'Panel ready' },
  { name: 'section', render: (q, attr) => `<section id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</section>`, text: 'Panel ready' },
  { name: 'p', render: (q, attr) => `<p id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</p>`, text: 'Panel ready' },
  { name: 'span', render: (q, attr) => `<span id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</span>`, text: 'Panel ready' },
  { name: 'h2', render: (q, attr) => `<h2 id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</h2>`, text: 'Panel ready' },
  { name: 'ul', render: (q, attr) => `<ul id=${quoteAttr(q, 'box-shell')} ${attr}><li>Panel ready</li></ul>`, text: 'Panel ready' },
  { name: 'form', render: (q, attr) => `<form id=${quoteAttr(q, 'box-shell')} ${attr}>Panel ready</form>`, text: 'Panel ready' },
  { name: 'input-hidden', render: (q, attr) => `<input type=${quoteAttr(q, 'hidden')} id=${quoteAttr(q, 'box-shell')} name=${quoteAttr(q, 'hidden-name')} value=${quoteAttr(q, 'hidden-val')} ${attr}/>`, text: null },
];

const NON_CONTROL_ATTRS = [
  ['class', 'body pushed no-dock'],
  ['role', 'status'],
  ['aria-busy', 'true'],
  ['aria-label', 'Status region'],
  ['data-state', 'waiting-approval'],
  ['style', 'display:flex'],
  ['type', 'presentation'],
  ['placeholder', 'Filter placeholder'],
  ['title', 'Container tooltip'],
  ['href', '#panel-anchor'],
];

test('FORMAL Rule 1: non-control HTML elements and non-control attributes never declare missing controls (720 inputs)', t => {
  const root = temp(t);
  let checked = 0;

  for (const element of NON_CONTROL_ELEMENTS) {
    for (const [attrName, attrValue] of NON_CONTROL_ATTRS) {
      for (const quote of ['"', "'"]) {
        for (const wrapper of ['raw', 'fenced']) {
          for (const besideButton of [false, true]) {
            const effectiveAttrName = element.name === 'input-hidden' && attrName === 'type' ? 'data-type-mirror' : attrName;
            const attrToken = `${effectiveAttrName}=${quoteAttr(quote, attrValue)}`;
            const nonControlMarkup = element.render(quote, attrToken);
            const buttonMarkup = besideButton
              ? `<button id=${quoteAttr(quote, 'ok-btn')} name=${quoteAttr(quote, 'ok-btn')}>OK</button>`
              : '';
            const combined = `${nonControlMarkup}${buttonMarkup}`;
            const body = wrapper === 'fenced' ? `\`\`\`html\n${combined}\n\`\`\`` : `Render ${combined} in the active button layout.`;
            const appearanceIds = besideButton ? 'Comparison-reference state (`ok-btn`):\n\n' : '';
            const prompt = `# Screen\n\n## Appearance\n\n${appearanceIds}![Screen](${DRAWING_FILE})\n\n${body}\n`;

            const svgParts = [];
            if (element.text) svgParts.push(`<text x="10" y="20">${xmlEscape(element.text)}</text>`);
            if (besideButton) svgParts.push('<g id="ok-btn"><text x="10" y="50">OK</text></g>');
            const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 240 120">${svgParts.join('')}</svg>`;

            writeFileSync(join(root, PROMPT_FILE), prompt);
            writeFileSync(join(root, DRAWING_FILE), svg);

            const warnings = lintSvgLayouts({ root, files: [PROMPT_FILE, DRAWING_FILE] });
            const context = JSON.stringify({ element: element.name, attr: effectiveAttrName, quote, wrapper, besideButton });

            for (const forbidden of ['box-shell', attrValue, 'hidden', 'hidden-name', 'hidden-val']) {
              assert.ok(!warnings.includes(controlWarning(forbidden)), `${context}: forbidden warning for "${forbidden}": ${warnings.join(' | ')}`);
            }
            assert.deepEqual(warnings, [], context);
            checked++;
          }
        }
      }
    }
  }

  assert.equal(checked, 720);
  console.log(`FORMAL rule-1 non-control-html-and-attributes: ${checked} exhaustive inputs passed`);
});

const QUOTE_STYLES = [
  { id: 'straight', open: '"', close: '"' },
  { id: 'curly', open: '“', close: '”' },
];

const HELP_PUNCTUATIONS = [
  { id: 'period', text: 'Arrow keys steer. Enter starts.' },
  { id: 'bang', text: 'Ready to play! Press start now.' },
  { id: 'question', text: 'Need a hint? Check the sidebar.' },
];

const LEAD_INS = [
  { id: 'backtick-instructions', text: '`instructions` says', forbiddenId: 'instructions' },
  { id: 'backtick-banner', text: '`status-note` displays', forbiddenId: 'status-note' },
  { id: 'plain-status', text: 'Show status text', forbiddenId: null },
];

const CONNECTORS = [
  { id: 'also-explain', text: 'Also explain', bridge: ' Also explain ' },
  { id: 'then-note', text: 'Then note', bridge: ' Then note ' },
  { id: 'while-visible', text: 'While visible, state', bridge: ' While visible, state ' },
];

const NEGATED_CLAUSES = [
  { id: 'no-button', build: (o, c) => `No button shows ${o}Loading...${c} while idle.`, target: 'Loading...' },
  { id: 'no-controls', build: (o, c) => `No controls trigger ${o}Auto-sync${c} in background mode.`, target: 'Auto-sync' },
  { id: 'without-a-button', build: (o, c) => `Without a button for ${o}Force reload${c}, keep polling.`, target: 'Force reload' },
  { id: 'without-controls', build: (o, c) => `Without controls enabled, hide ${o}Quick edit${c} actions.`, target: 'Quick edit' },
];

test('FORMAL Rules 2 & 3: multi-sentence quoted help copy, adjacent quotes and negated control clauses (864 inputs)', t => {
  const root = temp(t);
  let checked = 0;
  const secondHelp = 'Automatic moves wait 1 second plus runtime latency.';

  for (const q of QUOTE_STYLES) {
    for (const punct of HELP_PUNCTUATIONS) {
      for (const lead of LEAD_INS) {
        for (const conn of CONNECTORS) {
          for (const neg of NEGATED_CLAUSES) {
            for (const helpInSvg of [true, false]) {
              for (const startInSvg of [true, false]) {
                const prompt = [
                  '# Screen',
                  '',
                  '## Appearance',
                  '',
                  `![Screen](${DRAWING_FILE})`,
                  '',
                  `Use buttons with label ${q.open}Start${q.close}. ${lead.text} ${q.open}${punct.text}${q.close} ${conn.text} ${q.open}${secondHelp}${q.close} ${neg.build(q.open, q.close)}`,
                  '',
                ].join('\n');

                const svgNodes = [];
                if (startInSvg) svgNodes.push('<text x="8" y="20">Start</text>');
                if (helpInSvg) {
                  svgNodes.push(`<text x="8" y="44">${xmlEscape(punct.text)}</text>`);
                  svgNodes.push(`<text x="8" y="68">${xmlEscape(secondHelp)}</text>`);
                }
                const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 480 100">${svgNodes.join('')}</svg>`;

                writeFileSync(join(root, PROMPT_FILE), prompt);
                writeFileSync(join(root, DRAWING_FILE), svg);

                const warnings = lintSvgLayouts({ root, files: [PROMPT_FILE, DRAWING_FILE] });
                const context = JSON.stringify({ quote: q.id, punct: punct.id, lead: lead.id, conn: conn.id, neg: neg.id, helpInSvg, startInSvg });

                const forbiddenValues = [conn.bridge, conn.text, punct.text, secondHelp, neg.target];
                if (lead.forbiddenId) forbiddenValues.push(lead.forbiddenId);
                for (const forbidden of forbiddenValues) {
                  assert.ok(!warnings.includes(controlWarning(forbidden)), `${context}: forbidden warning for "${forbidden}": ${warnings.join(' | ')}`);
                }

                const expected = startInSvg ? [] : [controlWarning('Start')];
                assert.deepEqual(warnings, expected, context);
                checked++;
              }
            }
          }
        }
      }
    }
  }

  assert.equal(checked, 864);
  console.log(`FORMAL rules-2-3 quotes-and-negation: ${checked} exhaustive inputs passed`);
});

const AFFIRMATIVE_CONTROLS = [
  {
    id: 'button-double-quoted',
    isHtml: true,
    markup: '<button id="save-id" name="save-name" value="save-val" class="btn primary" aria-label="Save item">Save draft</button>',
    targets: [
      { value: 'Save draft', svgKind: 'text' },
      { value: 'save-id', svgKind: 'id' },
      { value: 'save-name', svgKind: 'id' },
      { value: 'save-val', svgKind: 'id' },
    ],
    forbidden: ['btn primary', 'Save item'],
  },
  {
    id: 'button-single-quoted-entity',
    isHtml: true,
    markup: "<button id='retry-id' name='retry-name' type='button' class='chip compact' role='button'>Retry &amp; sync</button>",
    targets: [
      { value: 'Retry & sync', svgKind: 'text' },
      { value: 'retry-id', svgKind: 'id' },
      { value: 'retry-name', svgKind: 'id' },
    ],
    forbidden: ['button', 'chip compact'],
  },
  {
    id: 'input-submit',
    isHtml: true,
    markup: '<input type="submit" id="apply-id" name="apply-name" value="Apply filter" class="btn" data-action="apply"/>',
    targets: [
      { value: 'Apply filter', svgKind: 'text' },
      { value: 'apply-id', svgKind: 'id' },
      { value: 'apply-name', svgKind: 'id' },
    ],
    forbidden: ['submit', 'btn', 'apply'],
  },
  {
    id: 'input-reset-single-quoted',
    isHtml: true,
    markup: "<input type='reset' id='clear-id' name='clear-name' value='Reset fields' title='Clear form'/>",
    targets: [
      { value: 'Reset fields', svgKind: 'text' },
      { value: 'clear-id', svgKind: 'id' },
      { value: 'clear-name', svgKind: 'id' },
    ],
    forbidden: ['reset', 'Clear form'],
  },
  {
    id: 'select-control',
    isHtml: true,
    markup: '<select id="sort-id" name="sort-name" class="menu-select" aria-label="Sort order"></select>',
    targets: [
      { value: 'sort-id', svgKind: 'id' },
      { value: 'sort-name', svgKind: 'id' },
    ],
    forbidden: ['menu-select', 'Sort order'],
  },
  {
    id: 'textarea-control',
    isHtml: true,
    markup: '<textarea id="notes-id" name="notes-name" placeholder="Add notes" style="min-height:48px"></textarea>',
    targets: [
      { value: 'notes-id', svgKind: 'id' },
      { value: 'notes-name', svgKind: 'id' },
    ],
    forbidden: ['Add notes', 'min-height:48px'],
  },
  {
    id: 'input-text-control',
    isHtml: true,
    markup: '<input type="text" id="search-id" name="search-name" placeholder="Search items" data-slot="query"/>',
    targets: [
      { value: 'search-id', svgKind: 'id' },
      { value: 'search-name', svgKind: 'id' },
    ],
    forbidden: ['text', 'Search items', 'query'],
  },
  {
    id: 'prose-button-label-id-name',
    isHtml: false,
    markup: 'Provide Button "Publish now" with id="pub-id", name="pub-name", class="cta-btn" and aria-busy="false".',
    targets: [
      { value: 'Publish now', svgKind: 'text' },
      { value: 'pub-id', svgKind: 'id' },
      { value: 'pub-name', svgKind: 'id' },
    ],
    forbidden: ['cta-btn', 'false'],
  },
  {
    id: 'prose-backticked-control-ids',
    isHtml: false,
    markup: 'Provide zoom buttons with ids `zoom-in` and `zoom-out`.',
    targets: [
      { value: 'zoom-in', svgKind: 'id' },
      { value: 'zoom-out', svgKind: 'id' },
    ],
    forbidden: [],
  },
  {
    id: 'prose-directional-controls',
    isHtml: false,
    markup: 'Provide four direction buttons `move-left`, `move-right`, `move-up` and `move-down`.',
    targets: [
      { value: 'move-down', svgKind: 'id' },
      { value: 'move-left', svgKind: 'id' },
      { value: 'move-right', svgKind: 'id' },
      { value: 'move-up', svgKind: 'id' },
    ],
    forbidden: [],
  },
];

const CONTAINER_NOISE = [
  { id: 'none', snippet: '', svgText: [], forbidden: [] },
  {
    id: 'double-container',
    snippet: '<div id="app-shell" class="app"><p id="status-chip" class="chip st-waiting" role="status" aria-busy="true">Waiting</p></div>',
    svgText: ['Waiting'],
    forbidden: ['app-shell', 'app', 'status-chip', 'chip st-waiting', 'status', 'true'],
  },
  {
    id: 'single-container-and-hidden',
    snippet: "<main id='shell-frame' class='frame compact' data-mode='live'><input type='hidden' id='csrf-id' name='csrf-name' value='csrf-secret'/></main>",
    svgText: [],
    forbidden: ['shell-frame', 'frame compact', 'live', 'csrf-id', 'csrf-name', 'csrf-secret'],
  },
];

const PROSE_NOISE = [
  { id: 'none', snippet: '', forbidden: [] },
  {
    id: 'multi-sentence-and-negated',
    snippet: '`instructions` says "Arrow keys steer. Enter starts!" Also explain "Moves wait 1 second." No button shows "Loading..." while idle.',
    forbidden: ['instructions', 'Arrow keys steer. Enter starts!', ' Also explain ', 'Moves wait 1 second.', 'Loading...'],
  },
];

const PRESENCE_MODES = ['none', 'first-only', 'all-but-first', 'all'];

function selectPresentTargets(targets, mode) {
  if (mode === 'none') return [];
  if (mode === 'first-only') return [targets[0]];
  if (mode === 'all-but-first') return targets.slice(1);
  return targets;
}

test('FORMAL Rule 4: affirmative HTML and prose controls report exact missing targets under coexisting HTML/prose noise (720 inputs)', t => {
  const root = temp(t);
  let checked = 0;

  for (const spec of AFFIRMATIVE_CONTROLS) {
    for (const mode of PRESENCE_MODES) {
      for (const container of CONTAINER_NOISE) {
        for (const proseNoise of PROSE_NOISE) {
          for (const layoutVariant of ['direct', 'code-span', 'fenced']) {
            const presentTargets = selectPresentTargets(spec.targets, mode);
            const presentSet = new Set(presentTargets.map(item => item.value));
            const absentValues = spec.targets
              .filter(item => !presentSet.has(item.value))
              .map(item => item.value);

            const drawnIds = presentTargets.filter(item => item.svgKind === 'id').map(item => item.value);
            const appearanceLine = drawnIds.length
              ? `Comparison-reference state (${drawnIds.map(id => `\`${id}\``).join(', ')}):\n\n`
              : '';

            const controlSection = spec.isHtml
              ? layoutVariant === 'fenced'
                ? `\`\`\`html\n${spec.markup}\n\`\`\``
                : layoutVariant === 'code-span'
                  ? `Render \`${spec.markup}\` in the screen.`
                  : spec.markup
              : layoutVariant === 'fenced'
                ? `## Controls\n\n${spec.markup}`
                : layoutVariant === 'code-span'
                  ? `- ${spec.markup}`
                  : spec.markup;

            const prompt = [
              '# Screen',
              '',
              '## Appearance',
              '',
              `${appearanceLine}![Screen](${DRAWING_FILE})`,
              '',
              container.snippet,
              controlSection,
              proseNoise.snippet,
              '',
            ].filter(line => line !== '').join('\n\n') + '\n';

            const svgElements = [];
            for (const text of container.svgText) {
              svgElements.push(`<text x="10" y="20">${xmlEscape(text)}</text>`);
            }
            for (const target of presentTargets) {
              if (target.svgKind === 'id') {
                svgElements.push(`<g id="${xmlEscape(target.value)}"><rect width="20" height="20"/></g>`);
              } else {
                svgElements.push(`<text x="10" y="50">${xmlEscape(target.value)}</text>`);
              }
            }
            const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 320 160">${svgElements.join('')}</svg>`;

            writeFileSync(join(root, PROMPT_FILE), prompt);
            writeFileSync(join(root, DRAWING_FILE), svg);

            const warnings = lintSvgLayouts({ root, files: [PROMPT_FILE, DRAWING_FILE] });
            const context = JSON.stringify({ control: spec.id, mode, container: container.id, proseNoise: proseNoise.id, layoutVariant });

            for (const forbidden of [...spec.forbidden, ...container.forbidden, ...proseNoise.forbidden]) {
              assert.ok(!warnings.includes(controlWarning(forbidden)), `${context}: forbidden warning for "${forbidden}": ${warnings.join(' | ')}`);
            }
            for (const present of presentTargets) {
              assert.ok(!warnings.includes(controlWarning(present.value)), `${context}: present control "${present.value}" must not warn`);
            }

            const expectedWarnings = absentValues.map(controlWarning).sort();
            assert.deepEqual(warnings, expectedWarnings, context);
            checked++;
          }
        }
      }
    }
  }

  assert.equal(checked, 720);
  console.log(`FORMAL rule-4 affirmative-controls-with-noise: ${checked} exhaustive inputs passed`);
});
