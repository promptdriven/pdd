import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  GRID_STAGES,
  MORPH_DURATION,
  COUNTER_X,
  COUNTER_Y,
  TEXT_MUTED,
} from './constants';

function hexToRgb(hex: string): [number, number, number] {
  const h = hex.replace('#', '');
  return [
    parseInt(h.substring(0, 2), 16),
    parseInt(h.substring(2, 4), 16),
    parseInt(h.substring(4, 6), 16),
  ];
}

function rgbToHex(r: number, g: number, b: number): string {
  return `#${Math.round(r).toString(16).padStart(2, '0')}${Math.round(g).toString(16).padStart(2, '0')}${Math.round(b).toString(16).padStart(2, '0')}`;
}

function lerpColor(c1: string, c2: string, t: number): string {
  const [r1, g1, b1] = hexToRgb(c1);
  const [r2, g2, b2] = hexToRgb(c2);
  return rgbToHex(
    r1 + (r2 - r1) * t,
    g1 + (g2 - g1) * t,
    b1 + (b2 - b1) * t
  );
}

export const CoverageCounter: React.FC = () => {
  const frame = useCurrentFrame();

  const { displayValue, displayColor } = useMemo(() => {
    let value = GRID_STAGES[0].coverage;
    let color = GRID_STAGES[0].coverageColor;

    for (let i = 1; i < GRID_STAGES.length; i++) {
      const stage = GRID_STAGES[i];
      const prevStage = GRID_STAGES[i - 1];
      const transitionStart = stage.startFrame - 15;
      const transitionEnd = stage.startFrame;

      if (frame >= transitionEnd) {
        value = stage.coverage;
        color = stage.coverageColor;
      } else if (frame >= transitionStart) {
        const progress = interpolate(
          frame,
          [transitionStart, transitionEnd],
          [0, 1],
          { easing: Easing.out(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );
        value = prevStage.coverage + (stage.coverage - prevStage.coverage) * progress;

        const colorProgress = interpolate(
          frame,
          [transitionStart, transitionStart + 20],
          [0, 1],
          { easing: Easing.inOut(Easing.quad), extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
        );
        color = lerpColor(prevStage.coverageColor, stage.coverageColor, colorProgress);
      }
    }

    return { displayValue: Math.round(value), displayColor: color };
  }, [frame]);

  // Fade in
  const opacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: COUNTER_X,
        top: COUNTER_Y,
        opacity,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'flex-end',
      }}
    >
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 12,
          color: TEXT_MUTED,
          opacity: 0.5,
          marginBottom: 4,
        }}
      >
        Context coverage:
      </div>
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 28,
          fontWeight: 'bold',
          color: displayColor,
        }}
      >
        {displayValue}%
      </div>
    </div>
  );
};

export default CoverageCounter;
