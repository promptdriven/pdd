import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  DIFF_COLORS,
  DIFF_BG_COLOR,
  COUNTER_COLOR,
  PHASE,
  SCROLL_SPEED_INITIAL,
  SCROLL_SPEED_MAX,
  LINES_CHANGED,
  WIDTH,
} from "./constants";

// Seeded random for deterministic diff lines
function seededRandom(seed: number): number {
  const x = Math.sin(seed * 127.1 + seed * 311.7) * 43758.5453;
  return x - Math.floor(x);
}

type DiffLineType = "added" | "deleted" | "unchanged";

interface DiffLine {
  type: DiffLineType;
  content: string;
  lineNumber: number;
}

// Generate realistic-looking code tokens
function generateCodeLine(seed: number): string {
  const keywords = [
    "const", "let", "function", "return", "if", "else", "for",
    "import", "export", "class", "async", "await", "try", "catch",
    "switch", "case", "break", "while", "new", "this", "super",
  ];
  const names = [
    "processData", "handleEvent", "validateInput", "transformOutput",
    "parseConfig", "initModule", "renderComponent", "fetchResults",
    "computeHash", "updateState", "dispatchAction", "resolvePromise",
    "serializeData", "deserializePayload", "encryptBuffer", "decryptStream",
    "allocateMemory", "releaseResources", "scheduleTask", "cancelTimer",
  ];
  const types = [
    "string", "number", "boolean", "void", "Promise", "Array",
    "Record", "Map", "Set", "Buffer", "ReadableStream", "Response",
  ];
  const operators = ["=", "===", "!==", "&&", "||", "??", "=>", "+=", "-="];
  const values = [
    "true", "false", "null", "undefined", "0", "1", "[]", "{}",
    "'error'", "'success'", "'pending'", "0xFF", "1024", "new Map()",
  ];

  const r1 = seededRandom(seed);
  const r2 = seededRandom(seed + 1);
  const r3 = seededRandom(seed + 2);
  const r4 = seededRandom(seed + 3);

  const indent = "  ".repeat(Math.floor(r1 * 4));
  const kw = keywords[Math.floor(r2 * keywords.length)];
  const name = names[Math.floor(r3 * names.length)];

  if (r4 < 0.15) {
    const type = types[Math.floor(seededRandom(seed + 4) * types.length)];
    return `${indent}${kw} ${name}: ${type} ${operators[Math.floor(seededRandom(seed + 5) * operators.length)]} ${values[Math.floor(seededRandom(seed + 6) * values.length)]};`;
  }
  if (r4 < 0.3) {
    return `${indent}${kw} ${name}(${names[Math.floor(seededRandom(seed + 7) * names.length)]}) {`;
  }
  if (r4 < 0.4) {
    return `${indent}}`;
  }
  if (r4 < 0.55) {
    return `${indent}return ${name}(${values[Math.floor(seededRandom(seed + 8) * values.length)]});`;
  }
  if (r4 < 0.7) {
    return `${indent}${kw} (${name} ${operators[Math.floor(seededRandom(seed + 9) * operators.length)]} ${values[Math.floor(seededRandom(seed + 10) * values.length)]}) {`;
  }
  if (r4 < 0.82) {
    return `${indent}// ${name} — ${types[Math.floor(seededRandom(seed + 11) * types.length)]} handler`;
  }
  return `${indent}${name}.${names[Math.floor(seededRandom(seed + 12) * names.length)]}(${values[Math.floor(seededRandom(seed + 13) * values.length)]});`;
}

// Pre-generate enough diff lines
function generateDiffLines(count: number): DiffLine[] {
  const lines: DiffLine[] = [];
  for (let i = 0; i < count; i++) {
    const r = seededRandom(i * 7 + 42);
    let type: DiffLineType;
    if (r < 0.35) type = "added";
    else if (r < 0.55) type = "deleted";
    else type = "unchanged";

    lines.push({
      type,
      content: generateCodeLine(i * 13 + 100),
      lineNumber: i + 1,
    });
  }
  return lines;
}

const LINE_HEIGHT = 20;
const VISIBLE_LINES = Math.ceil(1080 / LINE_HEIGHT) + 4;
const TOTAL_GENERATED_LINES = 600;

export const ScrollingCodeDiff: React.FC = () => {
  const frame = useCurrentFrame();

  const diffLines = useMemo(() => generateDiffLines(TOTAL_GENERATED_LINES), []);

  // Phase 2 starts at frame 240
  const diffFrame = frame - PHASE.diffStart;
  if (diffFrame < 0) return null;

  // Morph-in opacity
  const morphInOpacity = interpolate(
    frame,
    [PHASE.morphStart, PHASE.morphEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Scroll speed ramp: accelerate then decelerate
  // diffFrame 0-120: accelerate from 2 to 30
  // diffFrame 120-180: hold at max speed 30
  // diffFrame 180-240: decelerate from 30 to 0
  const accelEnd = PHASE.diffAccelEnd - PHASE.diffStart; // 120
  const maxEnd = PHASE.diffMaxSpeedEnd - PHASE.diffStart; // 180
  const totalEnd = PHASE.diffEnd - PHASE.diffStart; // 240

  let scrollSpeed: number;
  if (diffFrame <= accelEnd) {
    const t = Easing.in(Easing.quad)(diffFrame / accelEnd);
    scrollSpeed = interpolate(t, [0, 1], [SCROLL_SPEED_INITIAL, SCROLL_SPEED_MAX]);
  } else if (diffFrame <= maxEnd) {
    scrollSpeed = SCROLL_SPEED_MAX;
  } else {
    const decelProgress = (diffFrame - maxEnd) / (totalEnd - maxEnd);
    const t = Easing.out(Easing.cubic)(Math.min(decelProgress, 1));
    scrollSpeed = interpolate(t, [0, 1], [SCROLL_SPEED_MAX, 0]);
  }

  // Compute cumulative scroll offset by integrating speed
  // For simplicity, approximate with current frame position
  let scrollOffset = 0;
  for (let f = 0; f <= diffFrame; f++) {
    let spd: number;
    if (f <= accelEnd) {
      const t = Easing.in(Easing.quad)(f / accelEnd);
      spd = interpolate(t, [0, 1], [SCROLL_SPEED_INITIAL, SCROLL_SPEED_MAX]);
    } else if (f <= maxEnd) {
      spd = SCROLL_SPEED_MAX;
    } else {
      const dp = (f - maxEnd) / (totalEnd - maxEnd);
      const t = Easing.out(Easing.cubic)(Math.min(dp, 1));
      spd = interpolate(t, [0, 1], [SCROLL_SPEED_MAX, 0]);
    }
    scrollOffset += spd;
  }

  // Line counter animation
  const counterProgress = interpolate(
    diffFrame,
    [0, maxEnd],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const easedCounter = Easing.out(Easing.quad)(counterProgress);
  const currentCount = Math.round(easedCounter * LINES_CHANGED);
  const formattedCount = currentCount.toLocaleString();

  // Determine which lines are visible
  const topLineIndex = Math.floor(scrollOffset / LINE_HEIGHT);
  const offsetWithinLine = scrollOffset % LINE_HEIGHT;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: DIFF_BG_COLOR,
        opacity: morphInOpacity,
        overflow: "hidden",
      }}
    >
      {/* Scrolling diff lines */}
      <div
        style={{
          position: "absolute",
          left: 60,
          top: -offsetWithinLine,
          width: WIDTH - 120,
        }}
      >
        {Array.from({ length: VISIBLE_LINES + 2 }).map((_, i) => {
          const lineIdx = (topLineIndex + i) % TOTAL_GENERATED_LINES;
          const line = diffLines[lineIdx];
          const prefix = line.type === "added" ? "+" : line.type === "deleted" ? "-" : " ";
          const bgColor =
            line.type === "added"
              ? DIFF_COLORS.addedBg
              : line.type === "deleted"
              ? DIFF_COLORS.deletedBg
              : "transparent";
          const textColor =
            line.type === "added"
              ? DIFF_COLORS.added
              : line.type === "deleted"
              ? DIFF_COLORS.deleted
              : DIFF_COLORS.unchanged;
          const textOpacity = line.type === "unchanged" ? 0.3 : 1;

          return (
            <div
              key={`${topLineIndex}-${i}`}
              style={{
                height: LINE_HEIGHT,
                lineHeight: `${LINE_HEIGHT}px`,
                fontFamily: "JetBrains Mono, monospace",
                fontSize: 12,
                color: textColor,
                opacity: textOpacity,
                backgroundColor: bgColor,
                paddingLeft: 8,
                whiteSpace: "nowrap",
                overflow: "hidden",
                borderLeft:
                  line.type !== "unchanged"
                    ? `3px solid ${textColor}`
                    : "3px solid transparent",
              }}
            >
              <span style={{ display: "inline-block", width: 50, color: DIFF_COLORS.unchanged, opacity: 0.2 }}>
                {(topLineIndex + i + 1).toString().padStart(4, " ")}
              </span>
              <span
                style={{
                  display: "inline-block",
                  width: 16,
                  color: textColor,
                  fontWeight: "bold",
                }}
              >
                {prefix}
              </span>
              {line.content}
            </div>
          );
        })}
      </div>

      {/* Line counter */}
      <div
        style={{
          position: "absolute",
          right: 170,
          top: 50,
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 16,
          color: COUNTER_COLOR,
          opacity: 0.7,
          whiteSpace: "nowrap",
          textAlign: "right",
        }}
      >
        {formattedCount} lines changed
      </div>

      {/* Scroll speed indicator (subtle) */}
      {scrollSpeed > 10 && (
        <div
          style={{
            position: "absolute",
            right: 170,
            top: 80,
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 11,
            color: DIFF_COLORS.unchanged,
            opacity: interpolate(scrollSpeed, [10, 30], [0, 0.3], {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }),
            whiteSpace: "nowrap",
          }}
        >
          {Math.round(scrollSpeed)}px/frame
        </div>
      )}

      {/* Fade gradient at top and bottom edges */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          right: 0,
          height: 60,
          background: `linear-gradient(to bottom, ${DIFF_BG_COLOR}, transparent)`,
          pointerEvents: "none",
        }}
      />
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 0,
          right: 0,
          height: 60,
          background: `linear-gradient(to top, ${DIFF_BG_COLOR}, transparent)`,
          pointerEvents: "none",
        }}
      />
    </AbsoluteFill>
  );
};

export default ScrollingCodeDiff;
