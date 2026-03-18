// Part2ParadigmShift09AbstractionStaircase.tsx
// Animated ascending staircase showing chip design abstraction levels through decades.
// ~16s (480 frames @ 30fps)
import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  Easing,
  interpolate,
} from 'remotion';
import {
  COLORS,
  OPACITIES,
  STEPS,
  STEP_START_FRAMES,
  ARROW_START_FRAMES,
} from './constants';
import StaircaseStep from './StaircaseStep';
import ScaleArrow from './ScaleArrow';
import AbstractionIcon from './AbstractionIcon';
import PulsingGlow from './PulsingGlow';

export const defaultPart2ParadigmShift09AbstractionStaircaseProps = {};

export const Part2ParadigmShift09AbstractionStaircase: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Grid fade-in (frames 0-30)
  const gridOpacity = interpolate(frame, [0, 30], [0, OPACITIES.grid], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Y-axis label fade-in (frames 0-20)
  const axisOpacity = interpolate(frame, [0, 20], [0, OPACITIES.axisLabel], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        overflow: 'hidden',
      }}
    >
      {/* Perspective grid lines converging upper-right */}
      <PerspectiveGrid opacity={gridOpacity} />

      {/* Y-axis label */}
      <div
        style={{
          position: 'absolute',
          left: 35,
          top: 400,
          opacity: axisOpacity,
          transform: 'rotate(-90deg)',
          transformOrigin: 'center center',
          whiteSpace: 'nowrap',
        }}
      >
        <svg width={200} height={30}>
          {/* Upward arrow */}
          <line
            x1={10}
            y1={20}
            x2={10}
            y2={6}
            stroke={COLORS.axisLabel}
            strokeWidth={1}
            opacity={OPACITIES.axisLabel}
          />
          <polygon
            points="10,4 7,9 13,9"
            fill={COLORS.axisLabel}
            opacity={OPACITIES.axisLabel}
          />
          <text
            x={20}
            y={18}
            fill={COLORS.axisLabel}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            opacity={OPACITIES.axisLabel}
          >
            Abstraction level
          </text>
        </svg>
      </div>

      {/* Staircase steps */}
      {STEPS.map((step, i) => (
        <React.Fragment key={step.level}>
          <StaircaseStep
            x={step.x}
            y={step.y}
            startFrame={STEP_START_FRAMES[i]}
            drawDuration={20}
          />
          <AbstractionIcon
            step={step}
            startFrame={STEP_START_FRAMES[i]}
            fps={fps}
          />
        </React.Fragment>
      ))}

      {/* "Couldn't scale" arrows between steps */}
      {STEPS.slice(1).map((step, i) => (
        <ScaleArrow
          key={`arrow-${i}`}
          fromX={STEPS[i].x}
          fromY={STEPS[i].y}
          toX={step.x}
          toY={step.y}
          startFrame={ARROW_START_FRAMES[i]}
          dramatic={i === 3}
        />
      ))}

      {/* Pulsing glow + particles on step 5 */}
      <PulsingGlow
        x={STEPS[4].x}
        y={STEPS[4].y}
        startFrame={240}
      />
    </AbsoluteFill>
  );
};

// Perspective grid: faint lines converging toward upper-right
const PerspectiveGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  // Vanish point upper-right
  const vpX = 1600;
  const vpY = 100;

  // Horizontal grid lines
  const hLines = Array.from({ length: 12 }).map((_, i) => {
    const y = 200 + i * 80;
    return (
      <line
        key={`h-${i}`}
        x1={0}
        y1={y}
        x2={1920}
        y2={y}
        stroke={COLORS.gridLine}
        strokeWidth={0.5}
        opacity={opacity}
      />
    );
  });

  // Converging lines toward vanish point
  const cLines = Array.from({ length: 10 }).map((_, i) => {
    const startX = i * 200;
    const startY = 1080;
    return (
      <line
        key={`c-${i}`}
        x1={startX}
        y1={startY}
        x2={vpX}
        y2={vpY}
        stroke={COLORS.gridLine}
        strokeWidth={0.5}
        opacity={opacity * 0.5}
      />
    );
  });

  return (
    <svg
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      {hLines}
      {cLines}
    </svg>
  );
};

export default Part2ParadigmShift09AbstractionStaircase;
