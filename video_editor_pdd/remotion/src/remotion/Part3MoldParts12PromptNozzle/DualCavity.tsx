import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  NOZZLE_COLOR,
  LIQUID_START_COLOR,
  LIQUID_END_COLOR,
  WALL_COLOR,
  MOLD_INNER_LEFT,
  MOLD_INNER_TOP,
  MOLD_INNER_W,
  MOLD_INNER_H,
  CODE_VERSION_A,
  CODE_VERSION_B,
  PHASE_LIQUID_FILL_START,
  PHASE_DRAIN_START,
  PHASE_DRAIN_END,
  PHASE_SECOND_FILL_START,
  PHASE_SECOND_FILL_END,
  PHASE_BOTH_VISIBLE_START,
} from "./constants";

/** Syntax-colored code line (simple keyword highlighting) */
const SyntaxLine: React.FC<{ line: string }> = ({ line }) => {
  const keywords = ["def", "for", "in", "if", "not", "try", "except", "return"];
  const builtins = ["None", "int", "str", "ValueError", "UnicodeError"];

  const tokens = line.split(/(\s+|[(),:\[\].])/);
  return (
    <div style={{ whiteSpace: "pre", lineHeight: 1.5 }}>
      {tokens.map((token, i) => {
        let color = "#C9D1D9"; // default text
        if (keywords.includes(token)) color = "#FF7B72";
        else if (builtins.includes(token)) color = "#79C0FF";
        else if (token.startsWith('"') || token.startsWith("'")) color = "#A5D6FF";
        else if (token === "==" || token === "=" || token === "!=") color = "#FF7B72";
        return (
          <span key={i} style={{ color }}>
            {token}
          </span>
        );
      })}
    </div>
  );
};

/** Liquid fill rectangle that animates height */
const LiquidFill: React.FC<{
  fillProgress: number;
  left: number;
  width: number;
}> = ({ fillProgress, left, width }) => {
  const fillHeight = MOLD_INNER_H * fillProgress;
  return (
    <div
      style={{
        position: "absolute",
        left,
        top: MOLD_INNER_TOP + MOLD_INNER_H - fillHeight,
        width,
        height: fillHeight,
        background: `linear-gradient(180deg, ${LIQUID_START_COLOR}33, ${LIQUID_END_COLOR}33)`,
        borderRadius: 2,
      }}
    />
  );
};

export const DualCavity: React.FC = () => {
  const frame = useCurrentFrame();

  const halfW = (MOLD_INNER_W - 20) / 2; // gap for divider
  const leftX = MOLD_INNER_LEFT;
  const rightX = MOLD_INNER_LEFT + halfW + 20;
  const codeTop = MOLD_INNER_TOP + 20;

  // Phase 1: First fill (240-300)
  const fill1 = interpolate(
    frame,
    [PHASE_LIQUID_FILL_START, PHASE_DRAIN_START],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Phase 2: Drain (300-360)
  const drain = interpolate(
    frame,
    [PHASE_DRAIN_START, PHASE_DRAIN_END],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Phase 3: Second fill (360-480)
  const fill2 = interpolate(
    frame,
    [PHASE_SECOND_FILL_START, PHASE_SECOND_FILL_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Which fill level to show
  let liquidLevel = 0;
  if (frame < PHASE_DRAIN_START) {
    liquidLevel = fill1;
  } else if (frame < PHASE_DRAIN_END) {
    liquidLevel = drain;
  } else {
    liquidLevel = fill2;
  }

  // Code A visibility: appears during first fill, stays
  const codeAOpacity = interpolate(
    frame,
    [PHASE_LIQUID_FILL_START + 20, PHASE_LIQUID_FILL_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Code B visibility: appears during second fill
  const codeBOpacity = interpolate(
    frame,
    [PHASE_SECOND_FILL_START + 40, PHASE_SECOND_FILL_START + 60],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Divider visibility: appears when both are visible
  const dividerOpacity = interpolate(
    frame,
    [PHASE_BOTH_VISIBLE_START - 20, PHASE_BOTH_VISIBLE_START],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const codeALines = CODE_VERSION_A.split("\n");
  const codeBLines = CODE_VERSION_B.split("\n");

  return (
    <>
      {/* Liquid fill - left half */}
      {liquidLevel > 0 && frame < PHASE_DRAIN_END && (
        <LiquidFill fillProgress={liquidLevel} left={leftX} width={MOLD_INNER_W} />
      )}
      {/* Liquid fill - right half during second fill */}
      {frame >= PHASE_SECOND_FILL_START && liquidLevel > 0 && (
        <LiquidFill fillProgress={liquidLevel} left={leftX} width={MOLD_INNER_W} />
      )}

      {/* Dashed divider line */}
      <div
        style={{
          position: "absolute",
          left: MOLD_INNER_LEFT + MOLD_INNER_W / 2 - 1,
          top: MOLD_INNER_TOP,
          width: 2,
          height: MOLD_INNER_H,
          opacity: dividerOpacity,
          background: `repeating-linear-gradient(
            180deg,
            ${WALL_COLOR} 0px,
            ${WALL_COLOR} 6px,
            transparent 6px,
            transparent 12px
          )`,
        }}
      />

      {/* Code Version A - left half */}
      <div
        style={{
          position: "absolute",
          left: leftX + 15,
          top: codeTop,
          width: halfW - 30,
          height: MOLD_INNER_H - 40,
          overflow: "hidden",
          opacity: codeAOpacity,
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 9,
        }}
      >
        <div
          style={{
            color: NOZZLE_COLOR,
            fontSize: 10,
            fontWeight: 600,
            marginBottom: 6,
            opacity: 0.78,
          }}
        >
          Version A
        </div>
        {codeALines.map((line, i) => (
          <SyntaxLine key={i} line={line} />
        ))}
      </div>

      {/* Code Version B - right half */}
      <div
        style={{
          position: "absolute",
          left: rightX + 15,
          top: codeTop,
          width: halfW - 30,
          height: MOLD_INNER_H - 40,
          overflow: "hidden",
          opacity: codeBOpacity,
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: 9,
        }}
      >
        <div
          style={{
            color: NOZZLE_COLOR,
            fontSize: 10,
            fontWeight: 600,
            marginBottom: 6,
            opacity: 0.78,
          }}
        >
          Version B
        </div>
        {codeBLines.map((line, i) => (
          <SyntaxLine key={i} line={line} />
        ))}
      </div>
    </>
  );
};
