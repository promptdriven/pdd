import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  COLORS,
  MOLD,
  PART_SHAPE,
  BEATS,
  getMoldOpening,
  getCompletedCycles,
} from "./constants";

/**
 * Good parts that have been ejected and fall downward.
 * During production phase (frames 0-60), parts eject at a steady pace.
 * After defect eject phase begins, one final good part is in-flight, then production stops.
 */
interface EjectedPart {
  x: number;
  y: number;
  opacity: number;
}

/**
 * Renders the mold cross-section, ejected good parts, and the defective part.
 * The defective part ejects during frames 60-120 and comes to rest below the mold.
 */
export const MoldScene: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine if the mold should be frozen (paused production)
  const frozen = frame >= BEATS.DEFECT_EJECT_END;

  const opening = getMoldOpening(frame, frozen);
  const gapPx = opening * MOLD.gapMax;

  // Subtle vibration during production
  const isProducing = frame < BEATS.DEFECT_EJECT_END;
  const vibX = isProducing ? Math.sin(frame * 3) * 1.5 : 0;
  const vibY = isProducing ? Math.cos(frame * 4.7) * 1 : 0;

  // Mold half positions
  const topY = MOLD.centerY - MOLD.halfHeight - gapPx / 2;
  const bottomY = MOLD.centerY + gapPx / 2;
  const moldLeft = MOLD.centerX - MOLD.halfWidth;
  const moldBottom = bottomY + MOLD.halfHeight;

  // --- Good ejected parts (production phase: frames 0-60) ---
  const goodParts: EjectedPart[] = [];
  if (frame < BEATS.DEFECT_EJECT_START + 40) {
    // Produce good parts every cycle during production phase
    const cyclesDone = getCompletedCycles(
      Math.min(frame, BEATS.DEFECT_EJECT_START)
    );
    for (let c = 0; c < cyclesDone; c++) {
      const spawnFrame = (c + 1) * 30; // each cycle is 30 frames
      const age = frame - spawnFrame;
      if (age < 0 || age > 50) continue;
      const fallY = moldBottom + 20 + age * 5;
      const op = interpolate(age, [0, 35, 50], [1, 0.5, 0], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      });
      // Slight horizontal scatter
      const scatter = ((c * 17) % 11 - 5) * 1.2;
      goodParts.push({ x: MOLD.centerX + scatter, y: fallY, opacity: op });
    }
  }

  // Fade out good parts after pause begins
  const goodPartsFade =
    frame >= BEATS.PAUSE_HIGHLIGHT_START
      ? interpolate(
          frame,
          [BEATS.PAUSE_HIGHLIGHT_START, BEATS.ZOOM_START],
          [1, 0.15],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        )
      : 1;

  // --- Defective part ejection (frames 60-120) ---
  // The defective part emerges from the mold during cycles 60-90
  // and settles into its resting position by frame 120.
  const defectProgress =
    frame >= BEATS.DEFECT_EJECT_START
      ? interpolate(
          frame,
          [BEATS.DEFECT_EJECT_START, BEATS.DEFECT_EJECT_START + 40],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        )
      : 0;

  // Defective part resting position (below the mold, centered)
  const defectRestX = MOLD.centerX;
  const defectRestY = moldBottom + 80;
  const defectStartY = MOLD.centerY;
  const defectCurrentY =
    defectStartY + (defectRestY - defectStartY) * defectProgress;

  const showDefect = frame >= BEATS.DEFECT_EJECT_START;

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        {/* Metallic gradient for mold body */}
        <linearGradient id="moldGradDefect" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor="#7a8a9a" />
          <stop offset="50%" stopColor={COLORS.MOLD_BODY} />
          <stop offset="100%" stopColor="#4a5a6a" />
        </linearGradient>
        {/* Drop shadow filter */}
        <filter
          id="moldShadowDefect"
          x="-10%"
          y="-10%"
          width="120%"
          height="120%"
        >
          <feDropShadow
            dx="3"
            dy="3"
            stdDeviation="4"
            floodColor="#000"
            floodOpacity="0.5"
          />
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
          fill="url(#moldGradDefect)"
          stroke={COLORS.MOLD_EDGE}
          strokeWidth={2}
          filter="url(#moldShadowDefect)"
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
          fill="url(#moldGradDefect)"
          stroke={COLORS.MOLD_EDGE}
          strokeWidth={2}
          filter="url(#moldShadowDefect)"
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

        {/* --- Good ejected parts --- */}
        {goodParts.map((p, i) => (
          <rect
            key={`good-${i}`}
            x={p.x - PART_SHAPE.width / 2}
            y={p.y - PART_SHAPE.height / 2}
            width={PART_SHAPE.width}
            height={PART_SHAPE.height}
            rx={PART_SHAPE.rx}
            fill={COLORS.PART_AMBER}
            opacity={p.opacity * goodPartsFade}
          />
        ))}

        {/* --- Defective part --- */}
        {showDefect && (
          <g opacity={defectProgress}>
            {/* Main body of the defective part (red-tinted) */}
            <rect
              x={defectRestX - PART_SHAPE.width / 2}
              y={defectCurrentY - PART_SHAPE.height / 2}
              width={PART_SHAPE.width}
              height={PART_SHAPE.height}
              rx={PART_SHAPE.rx}
              fill={COLORS.DEFECT_RED}
            />
            {/* Crack line across the part */}
            <line
              x1={defectRestX - PART_SHAPE.width / 2 + 8}
              y1={defectCurrentY - PART_SHAPE.height / 2 + 6}
              x2={defectRestX + PART_SHAPE.width / 2 - 14}
              y2={defectCurrentY + PART_SHAPE.height / 2 - 4}
              stroke="#1a1a2e"
              strokeWidth={2.5}
              strokeLinecap="round"
            />
            {/* Secondary crack branch */}
            <line
              x1={defectRestX - 4}
              y1={defectCurrentY - 2}
              x2={defectRestX + PART_SHAPE.width / 2 - 6}
              y2={defectCurrentY - PART_SHAPE.height / 2 + 5}
              stroke="#1a1a2e"
              strokeWidth={1.8}
              strokeLinecap="round"
            />
            {/* Missing corner chunk (triangle cut-out effect) */}
            <polygon
              points={`
                ${defectRestX + PART_SHAPE.width / 2 - 12},${defectCurrentY - PART_SHAPE.height / 2}
                ${defectRestX + PART_SHAPE.width / 2},${defectCurrentY - PART_SHAPE.height / 2}
                ${defectRestX + PART_SHAPE.width / 2},${defectCurrentY - PART_SHAPE.height / 2 + 10}
              `}
              fill={COLORS.BACKGROUND}
            />
          </g>
        )}
      </g>
    </svg>
  );
};
