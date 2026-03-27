import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  LIQUID_LEADING_EDGE,
  LIQUID_GRADIENT_FROM,
  LIQUID_GRADIENT_TO,
  LIQUID_LEADING_OPACITY,
  LIQUID_LEADING_BLUR,
  RIPPLE_COLOR,
  RIPPLE_OPACITY,
  RIPPLE_DURATION,
  WALLS,
  CAVITY_TOP,
  CAVITY_BOTTOM,
  CAVITY_LEFT,
  NOZZLE_X,
  NOZZLE_WIDTH,
  NOZZLE_Y,
  WallDef,
} from './constants';

/** Ripple arcs that appear when liquid hits a wall */
const WallRipple: React.FC<{ wall: WallDef; frame: number }> = ({ wall, frame }) => {
  const elapsed = frame - wall.hitFrame;
  if (elapsed < 0 || elapsed > RIPPLE_DURATION) return null;

  const rippleProgress = interpolate(elapsed, [0, RIPPLE_DURATION], [0, 1], {
    easing: Easing.out(Easing.quad),
  });

  const midY = wall.y + wall.height / 2;

  return (
    <g>
      {[0, 1, 2].map((i) => {
        const delay = i * 0.15;
        const adjustedProgress = Math.max(0, Math.min(1, (rippleProgress - delay) / (1 - delay)));
        const radius = 8 + adjustedProgress * 30;
        const opacity = RIPPLE_OPACITY * (1 - adjustedProgress);

        return (
          <ellipse
            key={i}
            cx={wall.x - 15}
            cy={midY}
            rx={radius}
            ry={radius * 0.6}
            fill="none"
            stroke={RIPPLE_COLOR}
            strokeWidth={2}
            opacity={opacity}
          />
        );
      })}
    </g>
  );
};

export const LiquidFlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Liquid fills from left to right across the cavity
  // It enters from the nozzle entry point and flows right
  const entryX = NOZZLE_X + NOZZLE_WIDTH / 2;
  const entryY = NOZZLE_Y + 15; // tip of nozzle

  // Calculate how far the liquid has progressed
  // Liquid moves through cavity sections, stopping at each wall
  const getLeadingEdgeX = (): number => {
    // Before any wall, liquid flows freely
    // Between walls, liquid resumes after a brief pause
    let currentX = CAVITY_LEFT;

    for (let i = 0; i < WALLS.length; i++) {
      const wall = WALLS[i];
      const prevWallHit = i > 0 ? WALLS[i - 1].hitFrame : 0;
      const flowStart = i === 0 ? 0 : prevWallHit + 10; // 10 frame pause after hitting wall
      const flowEnd = wall.hitFrame;

      if (frame < flowStart) return currentX;

      if (frame >= flowStart && frame < flowEnd) {
        const progress = interpolate(frame, [flowStart, flowEnd], [0, 1], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.bezier(0.25, 0.1, 0.25, 1),
        });
        const prevX = i === 0 ? CAVITY_LEFT : WALLS[i - 1].x + 8;
        return prevX + (wall.x - 8 - prevX) * progress;
      }

      currentX = wall.x - 8; // stops just before the wall
    }

    // After all walls hit, fill remaining cavity
    const lastWall = WALLS[WALLS.length - 1];
    if (frame > lastWall.hitFrame + 10) {
      const progress = interpolate(
        frame,
        [lastWall.hitFrame + 10, lastWall.hitFrame + 60],
        [0, 1],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.bezier(0.25, 0.1, 0.25, 1) }
      );
      return lastWall.x + 8 + (920 - lastWall.x - 8) * progress;
    }

    return currentX;
  };

  const leadingEdgeX = getLeadingEdgeX();

  // Vertical drop from nozzle into cavity
  const dropProgress = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.bezier(0.25, 0.1, 0.25, 1),
  });

  const dropY = entryY + (CAVITY_TOP - entryY) * dropProgress;

  // Liquid body fills from cavity left to leading edge
  const fillWidth = Math.max(0, leadingEdgeX - CAVITY_LEFT);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
      viewBox="0 0 1920 1080"
    >
      <defs>
        <linearGradient id="liquid-gradient" x1="0%" y1="0%" x2="100%" y2="0%">
          <stop offset="0%" stopColor={LIQUID_GRADIENT_FROM} />
          <stop offset="100%" stopColor={LIQUID_GRADIENT_TO} />
        </linearGradient>
        <filter id="leading-edge-glow">
          <feGaussianBlur stdDeviation={LIQUID_LEADING_BLUR} />
        </filter>
        <linearGradient id="liquid-vertical-gradient" x1="0%" y1="0%" x2="0%" y2="100%">
          <stop offset="0%" stopColor={LIQUID_GRADIENT_FROM} />
          <stop offset="100%" stopColor={LIQUID_GRADIENT_TO} />
        </linearGradient>
      </defs>

      {/* Vertical drop stream from nozzle */}
      {dropProgress > 0 && (
        <rect
          x={entryX - 6}
          y={entryY}
          width={12}
          height={Math.max(0, dropY - entryY)}
          fill="url(#liquid-vertical-gradient)"
          opacity={0.8}
          rx={6}
        />
      )}

      {/* Main liquid body in cavity */}
      {frame >= 20 && fillWidth > 0 && (
        <>
          {/* Liquid body */}
          <rect
            x={CAVITY_LEFT}
            y={CAVITY_TOP + 4}
            width={fillWidth}
            height={CAVITY_BOTTOM - CAVITY_TOP - 8}
            fill="url(#liquid-gradient)"
            opacity={0.7}
            rx={2}
          />

          {/* Leading edge highlight */}
          <rect
            x={leadingEdgeX - 4}
            y={CAVITY_TOP + 2}
            width={8}
            height={CAVITY_BOTTOM - CAVITY_TOP - 4}
            fill={LIQUID_LEADING_EDGE}
            opacity={LIQUID_LEADING_OPACITY}
            filter="url(#leading-edge-glow)"
            rx={4}
          />

          {/* Surface shimmer */}
          <rect
            x={CAVITY_LEFT}
            y={CAVITY_TOP + 4}
            width={fillWidth}
            height={3}
            fill={LIQUID_LEADING_EDGE}
            opacity={0.3}
          />
        </>
      )}

      {/* Liquid fills around walls — show liquid on both sides when wall is passed */}
      {WALLS.map((wall) => {
        if (frame < wall.hitFrame + 10) return null;
        // Show liquid seeping around the wall (top and bottom gaps)
        const fillPast = interpolate(
          frame,
          [wall.hitFrame + 10, wall.hitFrame + 40],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );
        return (
          <g key={`fill-${wall.id}`} opacity={0.5 * fillPast}>
            <rect
              x={wall.x - 4}
              y={CAVITY_TOP + 4}
              width={8}
              height={wall.y - CAVITY_TOP - 4}
              fill="url(#liquid-gradient)"
              rx={1}
            />
            <rect
              x={wall.x - 4}
              y={wall.y + wall.height}
              width={8}
              height={CAVITY_BOTTOM - 4 - wall.y - wall.height}
              fill="url(#liquid-gradient)"
              rx={1}
            />
          </g>
        );
      })}

      {/* Ripples when liquid hits walls */}
      {WALLS.map((wall) => (
        <WallRipple key={`ripple-${wall.id}`} wall={wall} frame={frame} />
      ))}
    </svg>
  );
};
