import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  COLORS,
  MOLD,
  PART_SHAPE,
  BEATS,
  getMoldOpening,
  getAccumulatedCycles,
  getSpawnFrame,
} from "./constants";

/**
 * Renders the mold cross-section, ejected parts, and high-speed stream effect.
 */
export const MoldAndParts: React.FC = () => {
  const frame = useCurrentFrame();

  const opening = getMoldOpening(frame);
  const gapPx = opening * MOLD.gapMax;

  // Vibration at high speed
  const speedFactor =
    frame > BEATS.RAPID_START
      ? Math.min((frame - BEATS.RAPID_START) / 200, 1)
      : 0;
  const vibX = speedFactor * Math.sin(frame * 3) * 2;
  const vibY = speedFactor * Math.cos(frame * 4.7) * 1.5;

  // Mold half positions
  const topY = MOLD.centerY - MOLD.halfHeight - gapPx / 2;
  const bottomY = MOLD.centerY + gapPx / 2;
  const moldLeft = MOLD.centerX - MOLD.halfWidth;
  const moldBottom = bottomY + MOLD.halfHeight;

  // --- Compute ejected parts ---
  const accCycles = getAccumulatedCycles(frame);
  const totalCycles = Math.floor(accCycles);

  // First part: explicit slow animation (frame 0-60)
  const firstPartProgress =
    frame < BEATS.FIRST_EJECT_END
      ? interpolate(frame, [20, BEATS.FIRST_EJECT_END], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 1;

  // Subsequent parts: track recent cycle completions
  const recentParts: { x: number; y: number; opacity: number }[] = [];
  if (frame >= BEATS.RAMP_START && frame < BEATS.BLUR_START) {
    const startCycle = Math.max(1, totalCycles - 7);
    for (let c = startCycle; c <= totalCycles; c++) {
      const spawnF = getSpawnFrame(c);
      const age = frame - spawnF;
      if (age < 0 || age > 40) continue;
      const fallSpeed = 4 + speedFactor * 6;
      const y = moldBottom + 10 + age * fallSpeed;
      const opacity = interpolate(age, [0, 30, 40], [1, 0.6, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });
      // Slight horizontal scatter
      const scatter = ((c * 17) % 11 - 5) * 0.8;
      recentParts.push({ x: MOLD.centerX + scatter, y, opacity });
    }
  }

  // Stream effect (frame 180+)
  const streamOpacity =
    frame >= 180
      ? interpolate(frame, [180, BEATS.BLUR_START, BEATS.HOLD_START], [0, 0.7, 0.9], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;

  // Particles in stream
  const particles: { x: number; y: number; r: number; opacity: number }[] = [];
  if (frame >= 180 && frame < BEATS.HOLD_START) {
    for (let i = 0; i < 12; i++) {
      const seed = i * 37 + 13;
      const period = 20 + (seed % 15);
      const phase = ((frame * 1.5 + seed) % period) / period;
      const px = MOLD.centerX + ((seed % 30) - 15);
      const py = moldBottom + 20 + phase * 300;
      const pr = 3 + (seed % 4);
      const pop = (1 - phase) * streamOpacity * 0.7;
      particles.push({ x: px, y: py, r: pr, opacity: pop });
    }
  }

  // During hold, keep mold static and stream visible
  const holdStreamOpacity = frame >= BEATS.HOLD_START ? 0.9 : 0;

  return (
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
          <feDropShadow dx="3" dy="3" stdDeviation="4" floodColor="#000" floodOpacity="0.5" />
        </filter>
      </defs>

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
        {/* Top cavity (indent on bottom face) */}
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
        {/* Bottom cavity (indent on top face) */}
        <rect
          x={MOLD.centerX - MOLD.cavityWidth / 2}
          y={bottomY}
          width={MOLD.cavityWidth}
          height={MOLD.cavityHeight}
          rx={4}
          fill={COLORS.MOLD_CAVITY}
        />

        {/* --- First part ejection (frame 0-60) --- */}
        {frame < BEATS.RAMP_START && firstPartProgress > 0 && (
          <rect
            x={MOLD.centerX - PART_SHAPE.width / 2}
            y={
              MOLD.centerY -
              PART_SHAPE.height / 2 +
              firstPartProgress * (moldBottom - MOLD.centerY + 40)
            }
            width={PART_SHAPE.width}
            height={PART_SHAPE.height}
            rx={PART_SHAPE.rx}
            fill={COLORS.PART_AMBER}
            opacity={1 - firstPartProgress * 0.3}
          />
        )}

        {/* --- Subsequent ejected parts --- */}
        {recentParts.map((p, i) => (
          <rect
            key={i}
            x={p.x - PART_SHAPE.width / 2}
            y={p.y - PART_SHAPE.height / 2}
            width={PART_SHAPE.width}
            height={PART_SHAPE.height}
            rx={PART_SHAPE.rx}
            fill={COLORS.PART_AMBER}
            opacity={p.opacity}
          />
        ))}

        {/* --- Stream effect (high speed) --- */}
        {(streamOpacity > 0 || holdStreamOpacity > 0) && (
          <>
            <rect
              x={MOLD.centerX - 20}
              y={moldBottom + 5}
              width={40}
              height={320}
              rx={12}
              fill="url(#streamGrad)"
              opacity={Math.max(streamOpacity, holdStreamOpacity)}
            />
            {/* Floating particles */}
            {particles.map((p, i) => (
              <circle
                key={`p-${i}`}
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
    </svg>
  );
};
