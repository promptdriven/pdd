import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_W,
  CANVAS_H,
  CENTER_X,
  CENTER_Y,
  OUTER_W,
  OUTER_H,
  INNER_W,
  INNER_H,
  MOLD_STROKE_COLOR,
  MOLD_STROKE_WIDTH,
  MOLD_CORNER_RADIUS,
  NOZZLE_TOP_W,
  NOZZLE_BOTTOM_W,
  NOZZLE_H,
  MOLD_DRAW_FRAMES,
  REGIONS,
  REGION_GLOW_FRAMES,
  PULSE_CYCLE_FRAMES,
  PULSE_START_FRAME,
} from "./constants";

// ── Geometry helpers ───────────────────────────────────────────────

/** Outer rectangle (rounded) as SVG path */
const outerPath = (): string => {
  const x = CENTER_X - OUTER_W / 2;
  const y = CENTER_Y - OUTER_H / 2;
  const r = MOLD_CORNER_RADIUS;
  return [
    `M ${x + r} ${y}`,
    `H ${x + OUTER_W - r}`,
    `Q ${x + OUTER_W} ${y} ${x + OUTER_W} ${y + r}`,
    `V ${y + OUTER_H - r}`,
    `Q ${x + OUTER_W} ${y + OUTER_H} ${x + OUTER_W - r} ${y + OUTER_H}`,
    `H ${x + r}`,
    `Q ${x} ${y + OUTER_H} ${x} ${y + OUTER_H - r}`,
    `V ${y + r}`,
    `Q ${x} ${y} ${x + r} ${y}`,
    "Z",
  ].join(" ");
};

/** Inner cavity rectangle path */
const innerPath = (): string => {
  const x = CENTER_X - INNER_W / 2;
  // Offset inner cavity slightly downward (20px)
  const y = CENTER_Y - INNER_H / 2 + 20;
  return `M ${x} ${y} H ${x + INNER_W} V ${y + INNER_H} H ${x} Z`;
};

/** Nozzle (funnel) path at top of mold */
const nozzlePath = (): string => {
  const moldTop = CENTER_Y - OUTER_H / 2;
  const topLeft = CENTER_X - NOZZLE_TOP_W / 2;
  const topRight = CENTER_X + NOZZLE_TOP_W / 2;
  const bottomLeft = CENTER_X - NOZZLE_BOTTOM_W / 2;
  const bottomRight = CENTER_X + NOZZLE_BOTTOM_W / 2;
  const funnelTop = moldTop - NOZZLE_H;
  return [
    `M ${topLeft} ${funnelTop}`,
    `L ${bottomLeft} ${moldTop}`,
    `H ${bottomRight}`,
    `L ${topRight} ${funnelTop}`,
    "Z",
  ].join(" ");
};

/** Left wall path (between outer left edge and inner left edge) */
const leftWallPath = (): string => {
  const outerX = CENTER_X - OUTER_W / 2;
  const innerX = CENTER_X - INNER_W / 2;
  const outerTop = CENTER_Y - OUTER_H / 2;
  const outerBottom = CENTER_Y + OUTER_H / 2;
  return `M ${outerX} ${outerTop} H ${innerX} V ${outerBottom} H ${outerX} Z`;
};

/** Right wall path */
const rightWallPath = (): string => {
  const outerX = CENTER_X + OUTER_W / 2;
  const innerX = CENTER_X + INNER_W / 2;
  const outerTop = CENTER_Y - OUTER_H / 2;
  const outerBottom = CENTER_Y + OUTER_H / 2;
  return `M ${innerX} ${outerTop} H ${outerX} V ${outerBottom} H ${innerX} Z`;
};

/** Top wall path (between outer top and inner top, between inner sides) */
const topWallPath = (): string => {
  const innerLeft = CENTER_X - INNER_W / 2;
  const innerRight = CENTER_X + INNER_W / 2;
  const outerTop = CENTER_Y - OUTER_H / 2;
  const innerTop = CENTER_Y - INNER_H / 2 + 20;
  return `M ${innerLeft} ${outerTop} H ${innerRight} V ${innerTop} H ${innerLeft} Z`;
};

/** Bottom wall path */
const bottomWallPath = (): string => {
  const innerLeft = CENTER_X - INNER_W / 2;
  const innerRight = CENTER_X + INNER_W / 2;
  const outerBottom = CENTER_Y + OUTER_H / 2;
  const innerBottom = CENTER_Y + INNER_H / 2 + 20;
  return `M ${innerLeft} ${innerBottom} H ${innerRight} V ${outerBottom} H ${innerLeft} Z`;
};

// ── Approximate total path length for stroke-dashoffset animation ──
const estimateMoldPathLength = (): number => {
  // Outer perimeter + inner perimeter + nozzle perimeter
  const outerPerimeter = 2 * (OUTER_W + OUTER_H);
  const innerPerimeter = 2 * (INNER_W + INNER_H);
  const nozzlePerimeter =
    NOZZLE_TOP_W +
    2 * Math.sqrt(((NOZZLE_TOP_W - NOZZLE_BOTTOM_W) / 2) ** 2 + NOZZLE_H ** 2) +
    NOZZLE_BOTTOM_W;
  return outerPerimeter + innerPerimeter + nozzlePerimeter;
};

export const MoldDiagram: React.FC = () => {
  const frame = useCurrentFrame();
  const totalPathLen = estimateMoldPathLength();

  // ── Stroke-draw animation (frame 0-30) ──
  const drawProgress = interpolate(frame, [0, MOLD_DRAW_FRAMES], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });
  const dashOffset = totalPathLen * (1 - drawProgress);

  // ── Region glow opacities ──
  const regionOpacities = REGIONS.map((region) => {
    const startFrame = region.highlightFrame;
    const baseOpacity = interpolate(
      frame,
      [startFrame, startFrame + REGION_GLOW_FRAMES],
      [0, region.glowOpacity],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
    );

    // Pulse after PULSE_START_FRAME
    let pulseMultiplier = 1;
    if (frame >= PULSE_START_FRAME) {
      const pulseFrame = frame - PULSE_START_FRAME;
      const sineVal = Math.sin(
        (2 * Math.PI * pulseFrame) / PULSE_CYCLE_FRAMES
      );
      pulseMultiplier = interpolate(sineVal, [-1, 1], [0.6, 1]);
    }

    return baseOpacity * pulseMultiplier;
  });

  const wallsOpacity = regionOpacities[0];
  const nozzleOpacity = regionOpacities[1];
  const cavityOpacity = regionOpacities[2];

  return (
    <svg
      width={CANVAS_W}
      height={CANVAS_H}
      viewBox={`0 0 ${CANVAS_W} ${CANVAS_H}`}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <defs>
        {/* Glow filters */}
        <filter id="glow-walls" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="12" />
        </filter>
        <filter id="glow-nozzle" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="12" />
        </filter>
        <filter id="glow-cavity" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="8" />
        </filter>
      </defs>

      {/* ── Region glows (behind outline) ── */}

      {/* Walls glow */}
      <g opacity={wallsOpacity}>
        <path d={leftWallPath()} fill={REGIONS[0].color} filter="url(#glow-walls)" />
        <path d={rightWallPath()} fill={REGIONS[0].color} filter="url(#glow-walls)" />
        <path d={topWallPath()} fill={REGIONS[0].color} filter="url(#glow-walls)" />
        <path d={bottomWallPath()} fill={REGIONS[0].color} filter="url(#glow-walls)" />
      </g>
      {/* Walls solid fill (lower opacity) */}
      <g opacity={wallsOpacity * 0.5}>
        <path d={leftWallPath()} fill={REGIONS[0].color} />
        <path d={rightWallPath()} fill={REGIONS[0].color} />
        <path d={topWallPath()} fill={REGIONS[0].color} />
        <path d={bottomWallPath()} fill={REGIONS[0].color} />
      </g>

      {/* Nozzle glow */}
      <g opacity={nozzleOpacity}>
        <path d={nozzlePath()} fill={REGIONS[1].color} filter="url(#glow-nozzle)" />
      </g>
      <g opacity={nozzleOpacity * 0.5}>
        <path d={nozzlePath()} fill={REGIONS[1].color} />
      </g>

      {/* Cavity glow */}
      <g opacity={cavityOpacity}>
        <path d={innerPath()} fill={REGIONS[2].color} filter="url(#glow-cavity)" />
      </g>
      <g opacity={cavityOpacity * 0.4}>
        <path d={innerPath()} fill={REGIONS[2].color} />
      </g>

      {/* ── Mold outline (drawn with stroke-dashoffset) ── */}
      <g
        fill="none"
        stroke={MOLD_STROKE_COLOR}
        strokeWidth={MOLD_STROKE_WIDTH}
        strokeDasharray={totalPathLen}
        strokeDashoffset={dashOffset}
      >
        <path d={outerPath()} />
        <path d={innerPath()} />
        <path d={nozzlePath()} />
      </g>
    </svg>
  );
};
