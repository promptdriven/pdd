import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
} from "remotion";

// Blueprint grid background component
const BlueprintGrid: React.FC = () => {
  const spacing = 60;
  const lines: React.ReactNode[] = [];
  for (let x = 0; x <= 1920; x += spacing) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={1080}
        stroke="#1E293B"
        strokeOpacity={0.05}
        strokeWidth={1}
      />
    );
  }
  for (let y = 0; y <= 1080; y += spacing) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={1920}
        y2={y}
        stroke="#1E293B"
        strokeOpacity={0.05}
        strokeWidth={1}
      />
    );
  }
  return (
    <svg
      style={{ position: "absolute", top: 0, left: 0, width: 1920, height: 1080 }}
      viewBox="0 0 1920 1080"
    >
      {lines}
    </svg>
  );
};

// Dot matrix ghost shape (coordinate grid)
const DotMatrix: React.FC<{
  cx: number;
  cy: number;
  rows: number;
  cols: number;
  dotSize: number;
  spacing: number;
  opacity: number;
  frame: number;
  startFrame: number;
  pulseActive: boolean;
}> = ({ cx, cy, rows, cols, dotSize, spacing, opacity, frame, startFrame, pulseActive }) => {
  const totalWidth = (cols - 1) * spacing;
  const totalHeight = (rows - 1) * spacing;
  const originX = cx - totalWidth / 2;
  const originY = cy - totalHeight / 2;

  const dots: React.ReactNode[] = [];
  let dotIndex = 0;
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const dotFrame = startFrame + dotIndex;
      const dotOpacity = interpolate(frame, [dotFrame, dotFrame + 1], [0, 1], {
        extrapolateRight: "clamp",
        extrapolateLeft: "clamp",
      });

      // Pulse effect during hold phase
      const pulseOpacity = pulseActive
        ? interpolate(
            Math.sin(((frame - 90) / 30) * Math.PI * 2),
            [-1, 1],
            [opacity * 0.5, opacity * 1.5],
          )
        : opacity;

      dots.push(
        <circle
          key={`dot-${r}-${c}`}
          cx={originX + c * spacing}
          cy={originY + r * spacing}
          r={dotSize / 2}
          fill="#94A3B8"
          fillOpacity={dotOpacity * pulseOpacity}
        />
      );
      dotIndex++;
    }
  }

  // Label below
  const labelOpacity = interpolate(frame, [startFrame + rows * cols, startFrame + rows * cols + 10], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  return (
    <>
      <filter id="dot-glow">
        <feGaussianBlur stdDeviation="8" result="blur" />
        <feMerge>
          <feMergeNode in="blur" />
          <feMergeNode in="SourceGraphic" />
        </feMerge>
      </filter>
      {dots}
      <text
        x={cx}
        y={originY + totalHeight + 20}
        textAnchor="middle"
        fontFamily="'Inter', sans-serif"
        fontSize={8}
        fill="#94A3B8"
        fillOpacity={labelOpacity * 0.03}
      >
        EVERY POINT
      </text>
    </>
  );
};

// Mold outline ghost shape
const MoldOutline: React.FC<{
  cx: number;
  cy: number;
  opacity: number;
  frame: number;
  startFrame: number;
  glowActive: boolean;
}> = ({ cx, cy, opacity, frame, startFrame, glowActive }) => {
  const rectWidth = 80;
  const rectHeight = 80;
  const x = cx - rectWidth / 2;
  const y = cy - rectHeight / 2;

  // Draw progress over 40 frames
  const drawProgress = interpolate(frame, [startFrame, startFrame + 40], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  const perimeter = 2 * (rectWidth + rectHeight);
  const dashLength = perimeter * drawProgress;

  const glowOpacity = glowActive
    ? interpolate(
        Math.sin(((frame - 90) / 30) * Math.PI * 2),
        [-1, 1],
        [0.02, 0.04],
      )
    : 0.02;

  const labelOpacity = interpolate(frame, [startFrame + 40, startFrame + 50], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  return (
    <>
      <filter id="mold-glow">
        <feGaussianBlur stdDeviation="8" result="blur" />
        <feMerge>
          <feMergeNode in="blur" />
          <feMergeNode in="SourceGraphic" />
        </feMerge>
      </filter>
      {/* Glow layer */}
      <rect
        x={x}
        y={y}
        width={rectWidth}
        height={rectHeight}
        fill="none"
        stroke="#D9944A"
        strokeWidth={3}
        strokeOpacity={glowOpacity}
        strokeDasharray={`${dashLength} ${perimeter}`}
        filter="url(#mold-glow)"
      />
      {/* Main stroke */}
      <rect
        x={x}
        y={y}
        width={rectWidth}
        height={rectHeight}
        fill="none"
        stroke="#D9944A"
        strokeWidth={3}
        strokeOpacity={opacity * drawProgress}
        strokeDasharray={`${dashLength} ${perimeter}`}
      />
      <text
        x={cx}
        y={y + rectHeight + 20}
        textAnchor="middle"
        fontFamily="'Inter', sans-serif"
        fontSize={8}
        fill="#D9944A"
        fillOpacity={labelOpacity * 0.03}
      >
        WALLS ONLY
      </text>
    </>
  );
};

export const Part4PrecisionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();
  const { durationInFrames } = useVideoConfig();

  // Background fade-in: frames 0-15
  const bgOpacity = interpolate(frame, [0, 15], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
  });

  // "PART 4" label fade-in: frames 15-35
  const partLabelOpacity = interpolate(frame, [15, 35], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // "THE PRECISION" typewriter: frames 40-79 (13 chars × 3 frames each = 39 frames)
  const precisionText = "THE PRECISION";
  const charsVisible = Math.floor(
    interpolate(frame, [40, 40 + precisionText.length * 3], [0, precisionText.length], {
      extrapolateRight: "clamp",
      extrapolateLeft: "clamp",
    })
  );
  const precisionDisplayed = precisionText.slice(0, charsVisible);

  // Horizontal rule draw from center: frames 60-70
  const ruleProgress = interpolate(frame, [60, 70], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.inOut(Easing.quad),
  });
  const ruleHalfWidth = 100; // 200px total / 2
  const ruleWidth = ruleHalfWidth * ruleProgress;

  // "TRADEOFF" fade-in + slide-up: frames 70-90
  const tradeoffOpacity = interpolate(frame, [70, 90], [0, 1], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.quad),
  });
  const tradeoffSlideY = interpolate(frame, [70, 90], [10, 0], {
    extrapolateRight: "clamp",
    extrapolateLeft: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Hold phase pulse detection (frames 90-120)
  const isHoldPhase = frame >= 90;

  // Fade-out over last 20 frames (if needed for transitions)
  const fadeOut = interpolate(
    frame,
    [durationInFrames - 20, durationInFrames],
    [1, 0],
    { extrapolateRight: "clamp", extrapolateLeft: "clamp" }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#000000" }}>
      <AbsoluteFill style={{ backgroundColor: "#0A0F1A", opacity: bgOpacity * fadeOut }}>
        {/* Blueprint grid */}
        <BlueprintGrid />

        {/* Ghost shapes SVG layer */}
        <svg
          style={{ position: "absolute", top: 0, left: 0, width: 1920, height: 1080 }}
          viewBox="0 0 1920 1080"
        >
          {/* Dot matrix ghost (left) — starts at frame 15 */}
          {frame >= 15 && (
            <DotMatrix
              cx={560}
              cy={480}
              rows={8}
              cols={8}
              dotSize={4}
              spacing={12}
              opacity={0.03}
              frame={frame}
              startFrame={15}
              pulseActive={isHoldPhase}
            />
          )}
          {/* Mold outline ghost (right) — starts at frame 15 */}
          {frame >= 15 && (
            <MoldOutline
              cx={1360}
              cy={480}
              opacity={0.04}
              frame={frame}
              startFrame={15}
              glowActive={isHoldPhase}
            />
          )}
        </svg>

        {/* "PART 4" section label */}
        <div
          style={{
            position: "absolute",
            top: 400,
            left: 0,
            width: "100%",
            textAlign: "center",
            opacity: partLabelOpacity,
            fontFamily: "'Inter', sans-serif",
            fontWeight: 600,
            fontSize: 14,
            color: "#64748B",
            letterSpacing: 4,
          }}
        >
          PART 4
        </div>

        {/* "THE PRECISION" title */}
        <div
          style={{
            position: "absolute",
            top: 460,
            left: 0,
            width: "100%",
            textAlign: "center",
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 72,
            color: "#E2E8F0",
            whiteSpace: "pre",
          }}
        >
          {precisionDisplayed}
        </div>

        {/* Horizontal rule between title words */}
        {frame >= 60 && (
          <div
            style={{
              position: "absolute",
              top: 505,
              left: 960 - ruleWidth,
              width: ruleWidth * 2,
              height: 2,
              backgroundColor: "#334155",
              opacity: 0.5,
            }}
          />
        )}

        {/* "TRADEOFF" title — offset 15px right of center */}
        <div
          style={{
            position: "absolute",
            top: 545 + tradeoffSlideY,
            left: 15,
            width: "100%",
            textAlign: "center",
            opacity: tradeoffOpacity,
            fontFamily: "'Inter', sans-serif",
            fontWeight: 700,
            fontSize: 72,
            color: "#E2E8F0",
          }}
        >
          TRADEOFF
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTitleCard;
