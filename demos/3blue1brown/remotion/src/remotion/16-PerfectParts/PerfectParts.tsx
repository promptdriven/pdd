import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { SparkleEffect } from "./SparkleEffect";
import { Checkmark } from "./Checkmark";
import { DefectivePartDiscard } from "./DefectivePartDiscard";
import {
  COLORS,
  BEATS,
  MOLD,
  PART_SHAPE,
  getPartsCount,
  formatCount,
  PerfectPartsPropsType,
} from "./constants";

/**
 * Mold cross-section with "Mold Updated" label.
 * Reuses the same metallic gradient style as 14-PartsEject.
 */
const MoldCrossSection: React.FC = () => {
  const frame = useCurrentFrame();

  // Mold opens to eject parts, then closes
  // During FIRST_PERFECT phase: one cycle open-close
  const cyclePhase = (() => {
    if (frame < BEATS.FIRST_PERFECT_START) return 0;
    if (frame < BEATS.FIRST_PERFECT_START + 15) {
      // Open
      return interpolate(
        frame,
        [BEATS.FIRST_PERFECT_START, BEATS.FIRST_PERFECT_START + 15],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
      );
    }
    if (frame < BEATS.FIRST_PERFECT_START + 30) {
      // Stay open
      return 1;
    }
    if (frame < BEATS.FIRST_PERFECT_START + 45) {
      // Close
      return interpolate(
        frame,
        [BEATS.FIRST_PERFECT_START + 30, BEATS.FIRST_PERFECT_START + 45],
        [1, 0],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
      );
    }
    // During MORE_PARTS and beyond: rapid cycling
    if (frame >= BEATS.MORE_PARTS_START && frame < BEATS.STREAMING_START) {
      const cycleLen = 15;
      const localPhase = ((frame - BEATS.MORE_PARTS_START) % cycleLen) / cycleLen;
      if (localPhase < 0.3) return localPhase / 0.3;
      if (localPhase < 0.5) return 1;
      if (localPhase < 0.8) return 1 - (localPhase - 0.5) / 0.3;
      return 0;
    }
    return 0;
  })();

  const gapPx = cyclePhase * MOLD.gapMax;

  // Vibration during rapid production
  const speedFactor =
    frame > BEATS.MORE_PARTS_START
      ? Math.min((frame - BEATS.MORE_PARTS_START) / 60, 0.5)
      : 0;
  const vibX = speedFactor * Math.sin(frame * 3) * 2;
  const vibY = speedFactor * Math.cos(frame * 4.7) * 1.5;

  // Mold half positions
  const topY = MOLD.centerY - MOLD.halfHeight - gapPx / 2;
  const bottomY = MOLD.centerY + gapPx / 2;
  const moldLeft = MOLD.centerX - MOLD.halfWidth;

  // "Mold Updated" label opacity
  const labelOpacity = interpolate(
    frame,
    [10, 25, BEATS.MOLD_FIXED_END - 10, BEATS.MOLD_FIXED_END + 20],
    [0, 1, 1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  return (
    <g transform={`translate(${vibX}, ${vibY})`}>
      {/* --- Top mold half --- */}
      <rect
        x={moldLeft}
        y={topY}
        width={MOLD.halfWidth * 2}
        height={MOLD.halfHeight}
        rx={4}
        fill="url(#moldGrad)"
        stroke={COLORS.MOLD_EDGE}
        strokeWidth={2}
        filter="url(#moldShadow)"
      />
      {/* Top cavity */}
      <rect
        x={MOLD.centerX - MOLD.cavityWidth / 2}
        y={topY + MOLD.halfHeight - MOLD.cavityHeight}
        width={MOLD.cavityWidth}
        height={MOLD.cavityHeight}
        rx={4}
        fill={COLORS.MOLD_CAVITY}
      />

      {/* --- Bottom mold half --- */}
      <rect
        x={moldLeft}
        y={bottomY}
        width={MOLD.halfWidth * 2}
        height={MOLD.halfHeight}
        rx={4}
        fill="url(#moldGrad)"
        stroke={COLORS.MOLD_EDGE}
        strokeWidth={2}
        filter="url(#moldShadow)"
      />
      {/* Bottom cavity */}
      <rect
        x={MOLD.centerX - MOLD.cavityWidth / 2}
        y={bottomY}
        width={MOLD.cavityWidth}
        height={MOLD.cavityHeight}
        rx={4}
        fill={COLORS.MOLD_CAVITY}
      />

      {/* Sparkle effect on the fix point */}
      <SparkleEffect />

      {/* "Mold Updated" label */}
      {labelOpacity > 0 && (
        <text
          x={MOLD.centerX}
          y={MOLD.centerY - MOLD.halfHeight - 30}
          textAnchor="middle"
          fontSize={20}
          fontFamily="sans-serif"
          fontWeight={600}
          fill={COLORS.MOLD_UPDATED_LABEL}
          opacity={labelOpacity}
        >
          Mold Updated
        </text>
      )}
    </g>
  );
};

/**
 * Ejected parts with green glow and checkmarks.
 */
const EjectedParts: React.FC = () => {
  const frame = useCurrentFrame();

  const moldBottom = MOLD.centerY + MOLD.halfHeight;

  // --- First perfect part (frame 60-120) ---
  const firstPartProgress =
    frame >= BEATS.FIRST_PERFECT_START && frame < BEATS.FIRST_PERFECT_END
      ? interpolate(
          frame,
          [BEATS.FIRST_PERFECT_START + 15, BEATS.FIRST_PERFECT_START + 40],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          },
        )
      : frame >= BEATS.FIRST_PERFECT_END
        ? 1
        : 0;

  const firstPartY = MOLD.centerY + firstPartProgress * (moldBottom - MOLD.centerY + 60);
  const firstPartOpacity =
    frame >= BEATS.MORE_PARTS_START
      ? interpolate(frame, [BEATS.MORE_PARTS_START, BEATS.MORE_PARTS_START + 20], [1, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : firstPartProgress > 0
        ? 1
        : 0;

  // --- Subsequent perfect parts (frame 120-240) ---
  const subsequentParts: {
    x: number;
    y: number;
    opacity: number;
    checkFrame: number;
  }[] = [];

  if (frame >= BEATS.MORE_PARTS_START && frame < BEATS.STREAMING_START) {
    const cycleLen = 15;
    const elapsed = frame - BEATS.MORE_PARTS_START;
    const totalCycles = Math.floor(elapsed / cycleLen);
    const visibleCount = Math.min(totalCycles, 6);

    for (let i = 0; i < visibleCount; i++) {
      const spawnF = BEATS.MORE_PARTS_START + (totalCycles - visibleCount + i) * cycleLen;
      const age = frame - spawnF;
      if (age < 0) continue;

      const fallProgress = interpolate(age, [0, 25], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      });

      const y = moldBottom + 20 + fallProgress * 180;
      const opacity = interpolate(age, [0, 10, 35, 50], [0.3, 1, 0.7, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });

      // Slight horizontal scatter
      const scatter = ((i * 23) % 9 - 4) * 1.2;

      subsequentParts.push({
        x: MOLD.centerX + scatter,
        y,
        opacity,
        checkFrame: spawnF + 8,
      });
    }
  }

  // --- Stream effect (frame 240+) ---
  const streamOpacity = interpolate(
    frame,
    [BEATS.STREAMING_START, BEATS.STREAMING_START + 20],
    [0, 0.85],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" },
  );

  // Stream particles
  const particles: { x: number; y: number; r: number; opacity: number }[] = [];
  if (frame >= BEATS.STREAMING_START) {
    for (let i = 0; i < 14; i++) {
      const seed = i * 37 + 13;
      const period = 18 + (seed % 12);
      const phase = ((frame * 1.5 + seed) % period) / period;
      const px = MOLD.centerX + ((seed % 24) - 12);
      const py = moldBottom + 15 + phase * 320;
      const pr = 3 + (seed % 4);
      const pop = (1 - phase) * streamOpacity * 0.7;
      particles.push({ x: px, y: py, r: pr, opacity: pop });
    }
  }

  return (
    <g>
      {/* First perfect part */}
      {firstPartOpacity > 0 && firstPartProgress > 0 && (
        <g>
          {/* Green glow behind part */}
          <rect
            x={MOLD.centerX - PART_SHAPE.width / 2 - 4}
            y={firstPartY - PART_SHAPE.height / 2 - 4}
            width={PART_SHAPE.width + 8}
            height={PART_SHAPE.height + 8}
            rx={PART_SHAPE.rx + 4}
            fill={COLORS.PERFECT_GREEN_GLOW}
            opacity={firstPartOpacity * 0.5}
          />
          {/* The part itself */}
          <rect
            x={MOLD.centerX - PART_SHAPE.width / 2}
            y={firstPartY - PART_SHAPE.height / 2}
            width={PART_SHAPE.width}
            height={PART_SHAPE.height}
            rx={PART_SHAPE.rx}
            fill={COLORS.PART_AMBER}
            opacity={firstPartOpacity}
          />
          {/* Checkmark next to first part */}
          <Checkmark
            cx={MOLD.centerX + PART_SHAPE.width / 2 + 22}
            cy={firstPartY}
            size={28}
            color={COLORS.PERFECT_GREEN}
            appearFrame={BEATS.FIRST_PERFECT_START + 25}
          />
        </g>
      )}

      {/* Subsequent perfect parts */}
      {subsequentParts.map((p, i) => (
        <g key={`part-${i}`}>
          {/* Green glow */}
          <rect
            x={p.x - PART_SHAPE.width / 2 - 3}
            y={p.y - PART_SHAPE.height / 2 - 3}
            width={PART_SHAPE.width + 6}
            height={PART_SHAPE.height + 6}
            rx={PART_SHAPE.rx + 3}
            fill={COLORS.PERFECT_GREEN_GLOW}
            opacity={p.opacity * 0.35}
          />
          {/* The part */}
          <rect
            x={p.x - PART_SHAPE.width / 2}
            y={p.y - PART_SHAPE.height / 2}
            width={PART_SHAPE.width}
            height={PART_SHAPE.height}
            rx={PART_SHAPE.rx}
            fill={COLORS.PART_AMBER}
            opacity={p.opacity}
          />
          {/* Checkmark */}
          <Checkmark
            cx={p.x + PART_SHAPE.width / 2 + 18}
            cy={p.y}
            size={22}
            color={COLORS.PERFECT_GREEN}
            appearFrame={p.checkFrame}
          />
        </g>
      ))}

      {/* Stream effect */}
      {streamOpacity > 0 && (
        <>
          <rect
            x={MOLD.centerX - 20}
            y={moldBottom + 5}
            width={40}
            height={320}
            rx={12}
            fill="url(#streamGrad)"
            opacity={streamOpacity}
          />
          {/* Green tint on stream */}
          <rect
            x={MOLD.centerX - 20}
            y={moldBottom + 5}
            width={40}
            height={320}
            rx={12}
            fill={COLORS.PERFECT_GREEN}
            opacity={streamOpacity * 0.12}
          />
          {/* Floating particles */}
          {particles.map((p, i) => (
            <circle
              key={`sp-${i}`}
              cx={p.x}
              cy={p.y}
              r={p.r}
              fill={COLORS.PART_AMBER_LIGHT}
              opacity={p.opacity}
            />
          ))}
        </>
      )}
    </g>
  );
};

/**
 * Counter display, continuing from 10,001.
 */
const PartsCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const count = getPartsCount(frame);
  const displayCount = formatCount(count);

  // Glow based on count change rate
  const prevCount = getPartsCount(Math.max(0, frame - 5));
  const delta = count - prevCount;
  const glowIntensity = Math.min(delta / 5, 1);
  const glowRadius = 8 + glowIntensity * 20;

  // Fade in
  const counterOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        top: 280,
        left: 1150,
        width: 400,
        textAlign: "center",
        opacity: counterOpacity,
      }}
    >
      {/* Label */}
      <div
        style={{
          fontSize: 18,
          fontFamily: "sans-serif",
          fontWeight: 600,
          textTransform: "uppercase" as const,
          letterSpacing: 2,
          color: COLORS.LABEL_GRAY,
          marginBottom: 16,
        }}
      >
        Parts Produced
      </div>

      {/* Counter number */}
      <div
        style={{
          fontSize: 72,
          fontFamily: "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
          fontWeight: 700,
          color: COLORS.COUNTER_WHITE,
          textShadow: `0 0 ${glowRadius}px ${COLORS.COUNTER_GLOW}, 0 0 ${glowRadius * 2}px ${COLORS.COUNTER_GLOW}`,
          lineHeight: 1,
        }}
      >
        {displayCount}
      </div>
    </div>
  );
};

/**
 * 16-PerfectParts: Main composition.
 *
 * Shows the mold after being fixed (sparkle effect), then ejects
 * perfect parts with green checkmarks, discards the old defective
 * part, and ends with steady perfect-part production streaming.
 */
export const PerfectParts: React.FC<PerfectPartsPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // Narration fade-in during streaming phase
  const narrationOpacity = showNarration
    ? interpolate(frame, [BEATS.NARRATION_START, BEATS.NARRATION_START + 30], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      })
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* SVG layer: mold, parts, sparkle, checkmarks, defect */}
      <svg
        width="1920"
        height="1080"
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          {/* Metallic gradient for mold body */}
          <linearGradient id="moldGrad" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor="#7a8a9a" />
            <stop offset="50%" stopColor={COLORS.MOLD_BODY} />
            <stop offset="100%" stopColor="#4a5a6a" />
          </linearGradient>
          {/* Amber stream gradient */}
          <linearGradient id="streamGrad" x1="0" y1="0" x2="0" y2="1">
            <stop offset="0%" stopColor={COLORS.PART_AMBER} stopOpacity="0.9" />
            <stop offset="100%" stopColor={COLORS.PART_AMBER} stopOpacity="0" />
          </linearGradient>
          {/* Drop shadow filter */}
          <filter id="moldShadow" x="-10%" y="-10%" width="120%" height="120%">
            <feDropShadow
              dx="3"
              dy="3"
              stdDeviation="4"
              floodColor="#000"
              floodOpacity="0.5"
            />
          </filter>
        </defs>

        {/* Mold cross-section with sparkle and label */}
        <MoldCrossSection />

        {/* Ejected perfect parts with checkmarks */}
        <EjectedParts />

        {/* Defective part discard in bottom-left */}
        <DefectivePartDiscard />
      </svg>

      {/* Counter display (HTML overlay) */}
      <PartsCounter />

      {/* Narration overlay */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 32,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            ...And that fix applies to every part you'll ever make again.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
