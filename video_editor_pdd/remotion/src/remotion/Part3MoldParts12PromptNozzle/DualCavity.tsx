import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  AMBER,
  TEAL,
  CAVITY_LEFT,
  CAVITY_TOP,
  CAVITY_WIDTH,
  CAVITY_HEIGHT,
  CODE_VERSION_A,
  CODE_VERSION_B,
  PHASE_LIQUID_FILL_START,
  PHASE_DRAIN_START,
  PHASE_DRAIN_END,
  PHASE_REFILL_START,
  PHASE_REFILL_END,
  PHASE_DUAL_VIEW_START,
} from "./constants";

interface CodeToken {
  text: string;
  color: string;
}

const CodeBlock: React.FC<{
  tokens: CodeToken[];
  x: number;
  y: number;
  opacity: number;
  maxWidth: number;
}> = ({ tokens, x, y, opacity, maxWidth }) => {
  const elements: React.ReactNode[] = [];
  let currentX = x;
  let currentY = y;
  const charWidth = 5.5;
  const lineHeight = 12;

  tokens.forEach((token, tIdx) => {
    const chars = token.text.split("");
    chars.forEach((ch, cIdx) => {
      if (ch === "\n") {
        currentX = x;
        currentY += lineHeight;
        return;
      }
      elements.push(
        <tspan
          key={`${tIdx}-${cIdx}`}
          x={currentX}
          y={currentY}
          fill={token.color}
        >
          {ch}
        </tspan>
      );
      currentX += charWidth;
    });
  });

  return (
    <g opacity={opacity}>
      <text fontFamily="'JetBrains Mono', monospace" fontSize={9}>
        {elements}
      </text>
    </g>
  );
};

export const DualCavity: React.FC = () => {
  const frame = useCurrentFrame();

  const halfWidth = CAVITY_WIDTH / 2 - 10;
  const codeStartY = CAVITY_TOP + 30;

  // Phase 1: First fill (240-300) — liquid fills left side, code A appears
  const fill1Progress = interpolate(
    frame,
    [PHASE_LIQUID_FILL_START, PHASE_DRAIN_START],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Phase 2: Drain (300-360)
  const drainProgress = interpolate(
    frame,
    [PHASE_DRAIN_START, PHASE_DRAIN_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // Phase 3: Second fill (360-480) — liquid fills right side, code B appears
  const fill2Progress = interpolate(
    frame,
    [PHASE_REFILL_START, PHASE_REFILL_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.bezier(0.25, 0.1, 0.25, 1),
    }
  );

  // Phase 4: Dual view (480+) — both visible
  const dualViewOpacity = interpolate(
    frame,
    [PHASE_DUAL_VIEW_START, PHASE_DUAL_VIEW_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Liquid fill height
  const liquidHeight1 =
    frame < PHASE_DRAIN_START
      ? fill1Progress * CAVITY_HEIGHT
      : frame < PHASE_DRAIN_END
        ? (1 - drainProgress) * CAVITY_HEIGHT
        : 0;

  const liquidHeight2 =
    frame >= PHASE_REFILL_START
      ? fill2Progress * CAVITY_HEIGHT
      : 0;

  // Code A visibility
  const codeAOpacity =
    frame >= PHASE_DUAL_VIEW_START
      ? dualViewOpacity
      : frame >= PHASE_LIQUID_FILL_START
        ? interpolate(fill1Progress, [0.4, 1], [0, 0.9], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })
        : 0;

  // Code B visibility
  const codeBOpacity =
    frame >= PHASE_DUAL_VIEW_START
      ? dualViewOpacity
      : frame >= PHASE_REFILL_START
        ? interpolate(fill2Progress, [0.4, 1], [0, 0.9], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })
        : 0;

  if (frame < PHASE_LIQUID_FILL_START) return null;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="liquidGrad" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={AMBER} stopOpacity={0.6} />
          <stop offset="100%" stopColor={TEAL} stopOpacity={0.4} />
        </linearGradient>
        <clipPath id="cavityClipLeft">
          <rect
            x={CAVITY_LEFT}
            y={CAVITY_TOP}
            width={halfWidth}
            height={CAVITY_HEIGHT}
          />
        </clipPath>
        <clipPath id="cavityClipRight">
          <rect
            x={CAVITY_LEFT + halfWidth + 20}
            y={CAVITY_TOP}
            width={halfWidth}
            height={CAVITY_HEIGHT}
          />
        </clipPath>
      </defs>

      {/* Left liquid fill */}
      {liquidHeight1 > 0 && (
        <rect
          x={CAVITY_LEFT}
          y={CAVITY_TOP + CAVITY_HEIGHT - liquidHeight1}
          width={halfWidth}
          height={liquidHeight1}
          fill="url(#liquidGrad)"
          opacity={0.3}
        />
      )}

      {/* Right liquid fill */}
      {liquidHeight2 > 0 && (
        <rect
          x={CAVITY_LEFT + halfWidth + 20}
          y={CAVITY_TOP + CAVITY_HEIGHT - liquidHeight2}
          width={halfWidth}
          height={liquidHeight2}
          fill="url(#liquidGrad)"
          opacity={0.3}
        />
      )}

      {/* Dashed divider line between halves */}
      {frame >= PHASE_DUAL_VIEW_START && (
        <line
          x1={CAVITY_LEFT + halfWidth + 10}
          y1={CAVITY_TOP}
          x2={CAVITY_LEFT + halfWidth + 10}
          y2={CAVITY_TOP + CAVITY_HEIGHT}
          stroke="#ffffff"
          strokeWidth={1}
          strokeDasharray="6,4"
          opacity={0.3 * dualViewOpacity}
        />
      )}

      {/* Code version A — left half */}
      <g clipPath="url(#cavityClipLeft)">
        <CodeBlock
          tokens={CODE_VERSION_A}
          x={CAVITY_LEFT + 8}
          y={codeStartY}
          opacity={codeAOpacity}
          maxWidth={halfWidth - 16}
        />
      </g>

      {/* Code version B — right half */}
      <g clipPath="url(#cavityClipRight)">
        <CodeBlock
          tokens={CODE_VERSION_B}
          x={CAVITY_LEFT + halfWidth + 28}
          y={codeStartY}
          opacity={codeBOpacity}
          maxWidth={halfWidth - 16}
        />
      </g>
    </svg>
  );
};
