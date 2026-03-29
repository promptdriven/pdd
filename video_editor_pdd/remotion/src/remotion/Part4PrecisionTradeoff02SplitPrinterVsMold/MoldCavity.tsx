import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  MOLD_WALL_COLOR,
  MOLD_WALL_OPACITY,
  MOLD_WALL_STROKE,
  WALL_GLOW_COLOR,
  WALL_GLOW_RADIUS,
  MOLD_OUTER_X,
  MOLD_OUTER_Y,
  MOLD_OUTER_W,
  MOLD_OUTER_H,
  MOLD_CORNER_RADIUS,
  MOLD_CHANNELS,
  MOLD_INJECTION_X,
  MOLD_INJECTION_Y,
  BG_CAVITY,
  PHASE_ANIMATE_MID,
  PHASE_FILL_END,
} from './constants';

interface MoldCavityProps {
  panelOpacity: number;
}

// Wall segments to glow when liquid contacts them
const WALL_GLOW_SEGMENTS = [
  { frame: 150, cx: 470, cy: 140 },   // Top entry
  { frame: 170, cx: 470, cy: 300 },   // Junction
  { frame: 190, cx: 250, cy: 300 },   // Left junction
  { frame: 195, cx: 690, cy: 300 },   // Right junction
  { frame: 220, cx: 250, cy: 500 },   // Left mid
  { frame: 225, cx: 690, cy: 500 },   // Right mid
  { frame: 250, cx: 470, cy: 500 },   // Center mid
  { frame: 270, cx: 250, cy: 750 },   // Left bottom
  { frame: 275, cx: 690, cy: 750 },   // Right bottom
  { frame: 280, cx: 470, cy: 750 },   // Center bottom
  { frame: 290, cx: 120, cy: 540 },   // Outer wall left
  { frame: 295, cx: 820, cy: 540 },   // Outer wall right
  { frame: 300, cx: 470, cy: 940 },   // Outer wall bottom
];

export const MoldCavity: React.FC<MoldCavityProps> = ({ panelOpacity }) => {
  const frame = useCurrentFrame();

  // Generate wall glow effects
  const glowEffects: React.ReactNode[] = [];
  for (const seg of WALL_GLOW_SEGMENTS) {
    if (frame >= seg.frame) {
      const glowOpacity = interpolate(
        frame,
        [seg.frame, seg.frame + 10],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
      );

      glowEffects.push(
        <circle
          key={`glow-${seg.cx}-${seg.cy}`}
          cx={seg.cx}
          cy={seg.cy}
          r={WALL_GLOW_RADIUS * 2}
          fill="none"
          stroke={WALL_GLOW_COLOR}
          strokeWidth={3}
          strokeOpacity={glowOpacity * 0.8}
          filter="url(#wallGlow)"
        />
      );
    }
  }

  // Full cavity fill progress (from frame 150 to 300)
  const fillProgress = interpolate(
    frame,
    [PHASE_ANIMATE_MID, PHASE_FILL_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <svg
      width={PANEL_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0, opacity: panelOpacity }}
    >
      <defs>
        <filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation={WALL_GLOW_RADIUS / 2} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Cavity interior (dark void) */}
      <rect
        x={MOLD_OUTER_X}
        y={MOLD_OUTER_Y}
        width={MOLD_OUTER_W}
        height={MOLD_OUTER_H}
        rx={MOLD_CORNER_RADIUS}
        ry={MOLD_CORNER_RADIUS}
        fill={BG_CAVITY}
      />

      {/* Filled liquid area - grows as fillProgress increases */}
      {fillProgress > 0 && (
        <rect
          x={MOLD_OUTER_X + MOLD_WALL_STROKE}
          y={MOLD_OUTER_Y + MOLD_OUTER_H * (1 - fillProgress)}
          width={MOLD_OUTER_W - MOLD_WALL_STROKE * 2}
          height={MOLD_OUTER_H * fillProgress - MOLD_WALL_STROKE}
          rx={fillProgress > 0.9 ? MOLD_CORNER_RADIUS - MOLD_WALL_STROKE : 4}
          fill="#4A90D9"
          fillOpacity={0.2}
        />
      )}

      {/* Outer mold wall */}
      <rect
        x={MOLD_OUTER_X}
        y={MOLD_OUTER_Y}
        width={MOLD_OUTER_W}
        height={MOLD_OUTER_H}
        rx={MOLD_CORNER_RADIUS}
        ry={MOLD_CORNER_RADIUS}
        fill="none"
        stroke={MOLD_WALL_COLOR}
        strokeWidth={MOLD_WALL_STROKE}
        strokeOpacity={MOLD_WALL_OPACITY}
      />

      {/* Internal channels */}
      {MOLD_CHANNELS.map((ch, i) => (
        <line
          key={`ch-${i}`}
          x1={ch.x1}
          y1={ch.y1}
          x2={ch.x2}
          y2={ch.y2}
          stroke={MOLD_WALL_COLOR}
          strokeWidth={MOLD_WALL_STROKE / 2}
          strokeOpacity={MOLD_WALL_OPACITY * 0.6}
        />
      ))}

      {/* Injection point marker */}
      <circle
        cx={MOLD_INJECTION_X}
        cy={MOLD_INJECTION_Y}
        r={8}
        fill={MOLD_WALL_COLOR}
        fillOpacity={0.5}
      />
      <line
        x1={MOLD_INJECTION_X}
        y1={MOLD_INJECTION_Y + 8}
        x2={MOLD_INJECTION_X}
        y2={MOLD_OUTER_Y}
        stroke={MOLD_WALL_COLOR}
        strokeWidth={2}
        strokeOpacity={0.5}
        strokeDasharray="4 4"
      />

      {/* Wall glow effects */}
      {glowEffects}
    </svg>
  );
};

export default MoldCavity;
