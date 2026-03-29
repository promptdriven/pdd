import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  GREEN_LINE_COLOR,
  REGENERATION_Y,
  CYCLE_TICKS,
  X_MAX,
  ARROWS_START,
  ARROW_STAGGER,
} from './constants';

const ARROW_LENGTH = 22;

export const ResetArrows: React.FC = () => {
  const frame = useCurrentFrame();
  const lineY = CHART_BOTTOM - REGENERATION_Y * CHART_HEIGHT;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {CYCLE_TICKS.map((tick, i) => {
        const xPos = CHART_LEFT + (tick / X_MAX) * CHART_WIDTH;
        const arrowStart = ARROWS_START + i * ARROW_STAGGER;

        const progress = interpolate(
          frame,
          [arrowStart, arrowStart + 15],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        // Scale with slight overshoot effect (easeOutBack approximation)
        const scale = interpolate(
          frame,
          [arrowStart, arrowStart + 12, arrowStart + 15],
          [1.1, 0.98, 1.0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );

        const opacity = progress * 0.5;

        return (
          <g
            key={`arrow-${tick}`}
            transform={`translate(${xPos}, ${lineY}) scale(${scale})`}
            opacity={opacity}
          >
            {/* Downward arrow */}
            <line
              x1={0}
              y1={4}
              x2={0}
              y2={4 + ARROW_LENGTH}
              stroke={GREEN_LINE_COLOR}
              strokeWidth={2}
              strokeLinecap="round"
            />
            {/* Arrow head */}
            <polyline
              points={`-5,${4 + ARROW_LENGTH - 7} 0,${4 + ARROW_LENGTH} 5,${4 + ARROW_LENGTH - 7}`}
              fill="none"
              stroke={GREEN_LINE_COLOR}
              strokeWidth={2}
              strokeLinecap="round"
              strokeLinejoin="round"
            />
          </g>
        );
      })}
    </svg>
  );
};
