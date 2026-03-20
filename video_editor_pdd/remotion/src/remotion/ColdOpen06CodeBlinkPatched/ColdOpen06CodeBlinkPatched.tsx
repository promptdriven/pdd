import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  GUTTER_BG,
  LINE_NUMBER_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GUTTER_WIDTH,
  CODE_X_START,
  CODE_Y_START,
  LINE_HEIGHT,
  LINE_NUMBER_FONT_SIZE,
  CODE_LINES,
  PATCH_SCARS,
  HIGHLIGHT_START_FRAME,
  HIGHLIGHT_STAGGER,
  SCAN_LINE_START,
  SCAN_LINE_DURATION,
} from "./constants";
import { CodeLine } from "./CodeLine";
import { BlinkingCursor } from "./BlinkingCursor";
import { ScanLine } from "./ScanLine";

// ── Patch Scar Highlight ────────────────────────────────────────
const PatchScarHighlight: React.FC<{
  lineIndex: number;
  highlightColor: string;
  targetOpacity: number;
  scarIndex: number;
}> = ({ lineIndex, highlightColor, targetOpacity, scarIndex }) => {
  const frame = useCurrentFrame();

  const fadeStart = HIGHLIGHT_START_FRAME + scarIndex * HIGHLIGHT_STAGGER;
  const fadeEnd = fadeStart + 15; // 15 frames fade-in

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, targetOpacity], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: GUTTER_WIDTH,
        top: CODE_Y_START + lineIndex * LINE_HEIGHT,
        width: CANVAS_WIDTH - GUTTER_WIDTH,
        height: LINE_HEIGHT,
        backgroundColor: highlightColor,
        opacity,
        pointerEvents: "none",
      }}
    />
  );
};

// ── Line Numbers ────────────────────────────────────────────────
const LineNumbers: React.FC = () => (
  <>
    {CODE_LINES.map((_, i) => (
      <div
        key={i}
        style={{
          position: "absolute",
          left: 160,
          top: CODE_Y_START + i * LINE_HEIGHT,
          width: 30,
          height: LINE_HEIGHT,
          textAlign: "right",
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontSize: LINE_NUMBER_FONT_SIZE,
          lineHeight: `${LINE_HEIGHT}px`,
          color: LINE_NUMBER_COLOR,
          opacity: 0.5,
          userSelect: "none",
        }}
      >
        {i + 1}
      </div>
    ))}
  </>
);

// ── Code Block ──────────────────────────────────────────────────
const CodeBlock: React.FC = () => (
  <div
    style={{
      position: "absolute",
      left: CODE_X_START,
      top: CODE_Y_START,
      width: CANVAS_WIDTH - CODE_X_START - 200,
    }}
  >
    {CODE_LINES.map((line, i) => {
      const trimmed = line.trimStart();
      const isComment = trimmed.startsWith("//");
      return <CodeLine key={i} text={line} isComment={isComment} />;
    })}
  </div>
);

// ── Main Component ──────────────────────────────────────────────

export const defaultColdOpen06CodeBlinkPatchedProps = {};

export const ColdOpen06CodeBlinkPatched: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Gutter background */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: GUTTER_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: GUTTER_BG,
        }}
      />

      {/* Line numbers — visible from frame 0 */}
      <LineNumbers />

      {/* Code block — visible from frame 0 */}
      <CodeBlock />

      {/* Patch scar highlights — staggered fade-in starting frame 10 */}
      {PATCH_SCARS.map((scar, idx) => (
        <PatchScarHighlight
          key={idx}
          lineIndex={scar.lineIndex}
          highlightColor={scar.highlightColor}
          targetOpacity={scar.opacity}
          scarIndex={idx}
        />
      ))}

      {/* Blinking cursor — always present */}
      <BlinkingCursor />

      {/* Subtle scan line — frames 60-150 */}
      <ScanLine startFrame={SCAN_LINE_START} durationFrames={SCAN_LINE_DURATION} />
    </AbsoluteFill>
  );
};

export default ColdOpen06CodeBlinkPatched;
