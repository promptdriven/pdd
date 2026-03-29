import React, { useMemo } from 'react';
import { interpolate, Easing } from 'remotion';

/**
 * CodeDiffScroll — renders a scrolling code diff with green additions
 * and red deletions that blur past at high speed, then decelerate.
 */

const DIFF_BG = '#1E293B';
const DIFF_ADD_BG = 'rgba(90, 170, 110, 0.15)';
const DIFF_DEL_BG = 'rgba(239, 68, 68, 0.15)';
const DIFF_TEXT_COLOR = '#E2E8F0';
const LINE_NUM_COLOR = '#64748B';
const CODE_FONT = 'JetBrains Mono, monospace';

// Seeded random for deterministic diff lines
function seededRandom(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 16807 + 0) % 2147483647;
    return (s - 1) / 2147483646;
  };
}

type DiffLineType = 'add' | 'del' | 'ctx';

interface DiffLine {
  type: DiffLineType;
  lineNum: number;
  text: string;
}

const CODE_SNIPPETS = {
  add: [
    '  const result = await processData(input);',
    '  if (config.enableValidation) {',
    '    return validateSchema(data, schema);',
    '  }',
    '  const handler = createEventHandler(opts);',
    '  registry.register(handler.id, handler);',
    '  await pipeline.execute(context);',
    '  const metrics = collectMetrics(span);',
    '  logger.info("Processing complete", { id });',
    '  export function transformPayload(raw: Buffer) {',
    '    const parsed = decoder.decode(raw);',
    '    return normalize(parsed, options);',
    '  }',
    '  cache.set(key, serialized, { ttl: 3600 });',
    '  const conn = pool.acquire();',
    '  try {',
    '    const rows = await conn.query(sql, params);',
    '    return rows.map(mapToEntity);',
    '  } finally {',
    '    pool.release(conn);',
    '  }',
    '  interface TransformConfig {',
    '    readonly mode: "batch" | "stream";',
    '    readonly chunkSize: number;',
    '  }',
  ],
  del: [
    '  // TODO: optimize this later',
    '  const temp = data.slice();',
    '  for (let i = 0; i < temp.length; i++) {',
    '    if (temp[i] === null) continue;',
    '    result.push(transform(temp[i]));',
    '  }',
    '  return result;',
    '  var oldHandler = window.onload;',
    '  function legacy_process(input) {',
    '    return input.split(",").map(Number);',
    '  }',
    '  console.log("debug:", value);',
    '  // HACK: workaround for issue #4521',
    '  setTimeout(callback, 0);',
    '  let mutable = [];',
  ],
  ctx: [
    '',
    '  // Configuration',
    '  const DEFAULT_TIMEOUT = 30000;',
    'import { EventEmitter } from "events";',
    '',
    '  class ServiceController {',
    '    private state: Map<string, unknown>;',
    '',
    '    constructor(config: Config) {',
    '      this.state = new Map();',
    '    }',
    '  }',
    '',
  ],
};

function generateDiffLines(count: number, seed: number): DiffLine[] {
  const rand = seededRandom(seed);
  const lines: DiffLine[] = [];
  let lineNum = 1;

  for (let i = 0; i < count; i++) {
    const r = rand();
    let type: DiffLineType;
    if (r < 0.35) type = 'add';
    else if (r < 0.6) type = 'del';
    else type = 'ctx';

    const snippets = CODE_SNIPPETS[type];
    const text = snippets[Math.floor(rand() * snippets.length)];
    lines.push({ type, lineNum, text });
    lineNum++;
  }

  return lines;
}

const LINE_HEIGHT = 22;
const VISIBLE_LINES = 50; // lines visible on screen at once

export const CodeDiffScroll: React.FC<{
  localFrame: number;
  totalDuration: number;
  decelFrame: number;
}> = ({ localFrame, totalDuration, decelFrame }) => {
  const diffLines = useMemo(() => generateDiffLines(800, 9999), []);

  // Scroll offset: fast at first, decelerate toward end
  // decelFrame is relative to diff start
  const localDecel = decelFrame;
  const maxScroll = (diffLines.length - VISIBLE_LINES) * LINE_HEIGHT;

  // Two-phase scroll: accelerate then decelerate
  const scrollPhase1End = localDecel;
  const scrollPhase2End = totalDuration;

  // Phase 1: fast scroll (easeIn quad)
  const phase1Scroll = interpolate(
    Math.min(localFrame, scrollPhase1End),
    [0, scrollPhase1End],
    [0, maxScroll * 0.85],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Phase 2: decelerate (easeOut cubic)
  const phase2Scroll =
    localFrame > scrollPhase1End
      ? interpolate(
          localFrame,
          [scrollPhase1End, scrollPhase2End],
          [0, maxScroll * 0.15],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        )
      : 0;

  const totalScroll = phase1Scroll + phase2Scroll;

  // Motion blur effect: stronger when scrolling fast
  const scrollSpeed =
    localFrame < scrollPhase1End
      ? interpolate(localFrame, [0, scrollPhase1End], [0, 6], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        })
      : interpolate(localFrame, [scrollPhase1End, scrollPhase2End], [6, 0], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        });

  const blurAmount = Math.min(scrollSpeed * 0.3, 1.5);

  // Determine which lines are visible
  const startLine = Math.floor(totalScroll / LINE_HEIGHT);
  const endLine = Math.min(startLine + VISIBLE_LINES + 2, diffLines.length);
  const visibleSlice = diffLines.slice(startLine, endLine);
  const yOffset = -(totalScroll % LINE_HEIGHT);

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
        backgroundColor: DIFF_BG,
        overflow: 'hidden',
        filter: blurAmount > 0.1 ? `blur(${blurAmount}px)` : undefined,
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: yOffset,
          left: 0,
          width: 1920,
        }}
      >
        {visibleSlice.map((line, i) => {
          const bg =
            line.type === 'add'
              ? DIFF_ADD_BG
              : line.type === 'del'
                ? DIFF_DEL_BG
                : 'transparent';
          const prefix =
            line.type === 'add' ? '+' : line.type === 'del' ? '-' : ' ';

          return (
            <div
              key={`${startLine}-${i}`}
              style={{
                height: LINE_HEIGHT,
                display: 'flex',
                alignItems: 'center',
                backgroundColor: bg,
                borderLeft:
                  line.type === 'add'
                    ? '3px solid rgba(90, 170, 110, 0.5)'
                    : line.type === 'del'
                      ? '3px solid rgba(239, 68, 68, 0.4)'
                      : '3px solid transparent',
              }}
            >
              {/* Line number */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: 12,
                  color: LINE_NUM_COLOR,
                  width: 60,
                  textAlign: 'right',
                  paddingRight: 12,
                  userSelect: 'none',
                  flexShrink: 0,
                }}
              >
                {line.lineNum}
              </span>

              {/* Prefix (+/-/ ) */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: 14,
                  color:
                    line.type === 'add'
                      ? '#5AAA6E'
                      : line.type === 'del'
                        ? '#EF4444'
                        : LINE_NUM_COLOR,
                  width: 18,
                  flexShrink: 0,
                }}
              >
                {prefix}
              </span>

              {/* Code text */}
              <span
                style={{
                  fontFamily: CODE_FONT,
                  fontSize: 14,
                  color: DIFF_TEXT_COLOR,
                  whiteSpace: 'pre',
                  overflow: 'hidden',
                }}
              >
                {line.text}
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default CodeDiffScroll;
