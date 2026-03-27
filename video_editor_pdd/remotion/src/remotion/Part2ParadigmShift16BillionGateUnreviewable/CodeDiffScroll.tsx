// CodeDiffScroll.tsx — Fast-scrolling code diff view
import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const DIFF_BG = '#1E293B';
const ADD_BG = '#5AAA6E';
const DELETE_BG = '#EF4444';
const ADD_BG_OPACITY = 0.15;
const DELETE_BG_OPACITY = 0.15;
const TEXT_COLOR = '#E2E8F0';
const LINE_NUM_COLOR = '#64748B';
const LABEL_FONT = 'Inter, sans-serif';
const CODE_FONT = 'JetBrains Mono, monospace';
const LABEL_COLOR = '#94A3B8';

/** Deterministic pseudo-random for consistent diff generation */
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

interface DiffLine {
  type: 'add' | 'delete' | 'context';
  lineNumber: number;
  code: string;
}

/** Code-like token fragments for realistic diff appearance */
const CODE_FRAGMENTS = [
  'const result = await fetchData(',
  'if (config.enabled && threshold > 0) {',
  '  return transform(input, options);',
  'export function processGates(netlist: Netlist) {',
  '  const gates = netlist.filter(g => g.active);',
  '  yield* iterateConnections(node);',
  '    throw new Error("Gate count exceeds limit");',
  '  for (let i = 0; i < gates.length; i++) {',
  '    const output = computeLogic(gates[i]);',
  '  signal.connect(srcPin, destPin);',
  '  module.addWire({ from: a, to: b, width: 1 });',
  '  const delay = calculatePropagation(path);',
  '    buffer.push(intermediateResult);',
  '  return { valid: true, coverage: 0.97 };',
  '} catch (e) { log.error(e); }',
  '  placement.optimize(constraints);',
  '  router.route(net, layer, vias);',
  '  const timing = analyze(clockTree);',
  '    assert(googMet, "setup/hold violation");',
  '  drc.check(layout, rules);',
  '  export default synthesize;',
  '  const area = estimateArea(cells);',
  '    powerGrid.addStripe(metalLayer);',
  '  floorplan.place(macro, region);',
  '  const slack = timing.worstSlack();',
  '  cts.insertBuffer(clockNet, loc);',
  '  fillCell(emptySpaces, fillerLib);',
  '  if (lvs.compare(schematic, layout)) {',
  '    report.pass("LVS clean");',
  '  antenna.fix(violatingNets);',
];

function generateDiffLines(count: number, seed: number): DiffLine[] {
  const rand = seededRandom(seed);
  const lines: DiffLine[] = [];
  let lineNum = 1;

  for (let i = 0; i < count; i++) {
    const r = rand();
    const type: DiffLine['type'] =
      r < 0.35 ? 'add' : r < 0.65 ? 'delete' : 'context';
    const fragIdx = Math.floor(rand() * CODE_FRAGMENTS.length);
    lines.push({
      type,
      lineNumber: lineNum,
      code: CODE_FRAGMENTS[fragIdx],
    });
    lineNum++;
  }
  return lines;
}

export const CodeDiffScroll: React.FC<{
  startFrame: number;
  durationInFrames: number;
}> = ({ startFrame, durationInFrames }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  // Generate enough lines to fill the scroll
  const diffLines = useMemo(() => generateDiffLines(600, 7777), []);

  const LINE_HEIGHT = 22;
  const VISIBLE_LINES = Math.ceil(1080 / LINE_HEIGHT);
  const TOTAL_SCROLL = diffLines.length * LINE_HEIGHT;

  // Scroll: fast acceleration then deceleration in last 60 frames
  const fastEnd = durationInFrames - 60; // frame 150 in local = 300 global
  const scrollFast = interpolate(
    Math.min(localFrame, fastEnd),
    [0, fastEnd],
    [0, TOTAL_SCROLL * 0.85],
    {
      easing: Easing.in(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );
  const scrollSlow = interpolate(
    Math.max(localFrame - fastEnd, 0),
    [0, 60],
    [0, TOTAL_SCROLL * 0.05],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );
  const scrollY = scrollFast + scrollSlow;

  // Lines changed label — fades in 15 frames after diff starts
  // Minimum 0.78 opacity once visible per overlay readability contract
  const labelOpacity = interpolate(localFrame, [15, 30], [0, 0.88], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Determine which lines are visible
  const firstVisibleLine = Math.floor(scrollY / LINE_HEIGHT);
  const renderLines = diffLines.slice(
    firstVisibleLine,
    firstVisibleLine + VISIBLE_LINES + 2,
  );

  return (
    <div
      style={{
        width: 1920,
        height: 1080,
        overflow: 'hidden',
        position: 'relative',
        backgroundColor: DIFF_BG,
      }}
    >
      {/* Diff lines container */}
      <div
        style={{
          position: 'absolute',
          top: -(scrollY % LINE_HEIGHT),
          left: 0,
          width: '100%',
        }}
      >
        {renderLines.map((line, idx) => {
          const bgColor =
            line.type === 'add'
              ? ADD_BG
              : line.type === 'delete'
                ? DELETE_BG
                : 'transparent';
          const bgOpacity =
            line.type === 'add'
              ? ADD_BG_OPACITY
              : line.type === 'delete'
                ? DELETE_BG_OPACITY
                : 0;
          const prefix =
            line.type === 'add' ? '+' : line.type === 'delete' ? '-' : ' ';

          return (
            <div
              key={`${firstVisibleLine + idx}`}
              style={{
                height: LINE_HEIGHT,
                display: 'flex',
                alignItems: 'center',
                position: 'relative',
              }}
            >
              {/* Background highlight */}
              {line.type !== 'context' && (
                <div
                  style={{
                    position: 'absolute',
                    inset: 0,
                    backgroundColor: bgColor,
                    opacity: bgOpacity,
                  }}
                />
              )}
              {/* Line number */}
              <span
                style={{
                  width: 70,
                  textAlign: 'right',
                  paddingRight: 12,
                  fontFamily: CODE_FONT,
                  fontSize: 12,
                  color: LINE_NUM_COLOR,
                  flexShrink: 0,
                  position: 'relative',
                  zIndex: 1,
                }}
              >
                {line.lineNumber}
              </span>
              {/* Prefix (+/-/space) */}
              <span
                style={{
                  width: 20,
                  fontFamily: CODE_FONT,
                  fontSize: 14,
                  color:
                    line.type === 'add'
                      ? '#5AAA6E'
                      : line.type === 'delete'
                        ? '#EF4444'
                        : TEXT_COLOR,
                  flexShrink: 0,
                  position: 'relative',
                  zIndex: 1,
                }}
              >
                {prefix}
              </span>
              {/* Code text */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: 14,
                  color: TEXT_COLOR,
                  whiteSpace: 'nowrap',
                  position: 'relative',
                  zIndex: 1,
                }}
              >
                {line.code}
              </span>
            </div>
          );
        })}
      </div>

      {/* Motion blur overlay when scrolling fast */}
      {localFrame < durationInFrames - 60 && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            background:
              'linear-gradient(to bottom, transparent 20%, rgba(30,41,59,0.3) 50%, transparent 80%)',
            pointerEvents: 'none',
          }}
        />
      )}

      {/* Lines changed label — lower-right */}
      <div
        style={{
          position: 'absolute',
          right: 80,
          bottom: 60,
          fontFamily: LABEL_FONT,
          fontSize: 18,
          fontWeight: 400,
          color: LABEL_COLOR,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        47,382 lines changed
      </div>
    </div>
  );
};

export default CodeDiffScroll;
