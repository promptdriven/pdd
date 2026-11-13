import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { evaluateScreenLook, lintScreenDesign } from '../src/screen-design-check.mjs';
import { compareScreen } from '../src/screen-compare.mjs';
import { temp } from './helpers/runtime-fake.mjs';

// Story oracle: user_stories/screen-design-check.md, Rules to check.

test('FORMAL rule 1: mockup screens and HTML screens without .ui.svg never emit missing-stylesheet warnings (64 configurations)', () => {
  let checked = 0;
  for (const source of ['mockup', 'operation'])
    for (const format of ['svg', 'html'])
      for (const topSheets of [[], ['styles/app.css']])
        for (const screenSheets of [[], ['styles/screen.css']])
          for (const drawings of [[], ['prompts/views/ledger__stacked.ui.svg']])
            for (const hasClass of [false, true]) {
              const result = lintScreenDesign({
                appMaps: [{
                  path: 'app-map.json',
                  stylesheets: topSheets,
                  screens: [{
                    id: 'screen-one',
                    prompt_path: 'prompts/screen.prompt.md',
                    source,
                    format,
                    stylesheets: screenSheets,
                  }],
                }],
                stylesheets: [
                  { path: 'styles/app.css', content: '.card { background: #1e293b; }', error: null },
                  { path: 'styles/screen.css', content: '.btn { background: #0284c7; }', error: null },
                ],
                prompts: [{
                  path: 'prompts/screen.prompt.md',
                  prose: hasClass ? 'Render `.card` and `.btn`.' : 'Render screen-one.',
                  drawings,
                }],
              });
              const missingStylesheet = result.warnings.some(warning => warning.includes('with no stylesheet in "stylesheets"'));
              const context = JSON.stringify({ source, format, topSheets, screenSheets, drawings, hasClass });
              if (source === 'mockup' || drawings.length === 0) {
                assert.equal(missingStylesheet, false, `forbidden missing-stylesheet warning: ${context}`);
                assert.deepEqual(result.warnings, [], `non-HTML-drawn screen must emit zero stylesheet warnings: ${context}`);
              } else if (source === 'operation' && format === 'html' && topSheets.length === 0 && screenSheets.length === 0) {
                assert.equal(missingStylesheet, true, `HTML screen with .ui.svg and empty stylesheets must warn: ${context}`);
              } else {
                assert.equal(missingStylesheet, false, context);
              }
              checked++;
            }
  assert.equal(checked, 64);
});

test('FORMAL rule 2: without --look, compareScreen never fails on canvas color, paint, size or spacing (64 configurations)', async t => {
  const cwd = temp(t);
  const drawingPath = 'board.ui.svg';
  writeFileSync(join(cwd, drawingPath), '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 400 400"><rect id="card-a" x="20" y="20" width="360" height="80" fill="#1e293b"/><rect id="card-b" x="20" y="120" width="360" height="80" fill="#1e293b"/><text x="40" y="60" fill="#f8fafc">READY</text></svg>');
  const viewport = { width: 400, height: 400 };
  const reference = [
    { kind: 'id', value: 'card-a', node: 1, ancestors: [], visible: true, region: null, box: { x: 20, y: 20, width: 360, height: 80 } },
    { kind: 'id', value: 'card-b', node: 2, ancestors: [], visible: true, region: null, box: { x: 20, y: 120, width: 360, height: 80 } },
    { kind: 'text', value: 'READY', node: 3, ancestors: [1], visible: true, region: 'card-a', box: { x: 40, y: 45, width: 60, height: 20 } },
  ];
  const referenceLook = {
    canvasColor: [15, 23, 42],
    boxes: [
      { id: 'card-a', box: { x: 20, y: 20, width: 360, height: 80 }, fill: [30, 41, 59], stroke: [56, 189, 248] },
      { id: 'card-b', box: { x: 20, y: 120, width: 360, height: 80 }, fill: [30, 41, 59], stroke: [51, 65, 85] },
    ],
  };
  let checked = 0;
  for (const lookOption of [undefined, false])
    for (const canvasColor of [[15, 23, 42], [255, 255, 255]])
      for (const painted of [true, false])
        for (const collapsed of [false, true])
          for (const zeroGap of [false, true])
            for (const labelVisible of [true, false]) {
              const cardA = collapsed
                ? { x: 195, y: 53, width: 10, height: 14 }
                : { x: 20, y: 20, width: 360, height: 80 };
              const cardB = zeroGap
                ? { x: 20, y: 100, width: 360, height: 60 }
                : { x: 20, y: 120, width: 360, height: 80 };
              const actual = [
                { kind: 'id', value: 'card-a', node: 10, ancestors: [], visible: true, region: null, box: cardA },
                { kind: 'id', value: 'card-b', node: 11, ancestors: [], visible: true, region: null, box: cardB },
                { kind: 'text', value: 'READY', node: 12, ancestors: [10], visible: labelVisible, region: null, box: { x: 40, y: 45, width: 60, height: 20 } },
              ];
              const actualLook = {
                canvasColor,
                boxes: [
                  { id: 'card-a', visible: true, painted, box: cardA, fill: painted ? [255, 0, 0] : null, stroke: null },
                  { id: 'card-b', visible: true, painted, box: cardB, fill: painted ? [255, 0, 0] : null, stroke: null },
                ],
              };
              const report = await compareScreen(
                { url: 'https://example.test/screen', drawingPath, cwd, ...(lookOption === undefined ? {} : { look: lookOption }) },
                { browser: async () => structuredClone({ viewport, reference, actual, referenceLook, actualLook }) },
              );
              const context = JSON.stringify({ lookOption, canvasColor, painted, collapsed, zeroGap, labelVisible });
              assert.equal(report.rows.some(row => row.kind === 'look' || row.status === 'look'), false, `forbidden look row without --look: ${context}`);
              assert.equal(report.passed, labelVisible, `without --look only parts/text/regions/order decide pass: ${context}`);
              checked++;
            }
  assert.equal(checked, 64);
});

test('FORMAL rule 3: collapsed boxes against a 320x320 reference always fail --look even when painted and centered (72 configurations)', () => {
  const viewport = { width: 400, height: 400 };
  const reference = {
    canvasColor: [15, 23, 42],
    boxes: [{ id: 'board', box: { x: 40, y: 40, width: 320, height: 320 }, fill: [30, 41, 59], stroke: [56, 189, 248] }],
  };
  let checked = 0;
  for (const width of [320, 147, 64, 14, 1])
    for (const height of [320, 147, 64, 14, 1])
      for (const painted of [true, false]) {
        if (width === 320 && height === 320 && !painted) {
          // Unpainted full-size box must also fail --look.
          const report = evaluateScreenLook({
            viewport,
            reference,
            actual: {
              canvasColor: [15, 23, 42],
              boxes: [{ id: 'board', visible: true, painted: false, box: { x: 40, y: 40, width: 320, height: 320 }, fill: null, stroke: null }],
            },
          });
          assert.equal(report.passed, false);
          checked++;
          continue;
        }
        const x = 200 - width / 2, y = 200 - height / 2;
        const report = evaluateScreenLook({
          viewport,
          reference,
          actual: {
            canvasColor: [15, 23, 42],
            boxes: [{ id: 'board', visible: true, painted, box: { x, y, width, height }, fill: [30, 41, 59], stroke: [56, 189, 248] }],
          },
        });
        const collapsed = width < 148 || height < 148;
        const context = JSON.stringify({ width, height, painted });
        if (collapsed || !painted) {
          assert.equal(report.passed, false, `collapsed or unpainted box must fail --look: ${context}`);
          assert.equal(report.rows.find(row => row.part === '#board look')?.status, 'look', context);
        } else {
          assert.equal(report.passed, true, context);
        }
        checked++;
      }
  for (const extra of [
    { width: 320, height: 14, painted: true },
    { width: 14, height: 320, painted: true },
  ]) {
    for (let offset = -10; offset <= 10; offset += 2) {
      const report = evaluateScreenLook({
        viewport,
        reference,
        actual: {
          canvasColor: [15, 23, 42],
          boxes: [{
            id: 'board',
            visible: true,
            painted: extra.painted,
            box: { x: 200 - extra.width / 2 + offset, y: 200 - extra.height / 2 + offset, width: extra.width, height: extra.height },
            fill: [30, 41, 59],
            stroke: [56, 189, 248],
          }],
        },
      });
      assert.equal(report.passed, false, `320x14 / 14x320 collapsed box must never pass --look (offset=${offset})`);
      assert.match(report.rows.find(row => row.part === '#board look')?.actual || '', /size /);
      checked++;
    }
  }
  assert.equal(checked, 72);
});
