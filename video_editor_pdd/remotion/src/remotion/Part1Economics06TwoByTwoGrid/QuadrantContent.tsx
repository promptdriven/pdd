import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { GRID_X, GRID_Y, GRID_W, GRID_H, SUBTEXT_COLOR } from './constants';

interface StudyQuadrantProps {
  quadrant: 'top-left' | 'top-right' | 'bottom-left' | 'bottom-right';
  color: string;
  bgOpacity: number;
  startFrame: number;
  scaleDuration: number;
  studyName?: string;
  stat?: string;
  subtext?: string;
  mixedLabel?: string;
}

/**
 * Renders the content for a single quadrant of the 2×2 grid.
 * Study quadrants show name, stat, and subtext with scale-up animation.
 * Mixed quadrants show a simple label with fade-in.
 */
export const QuadrantContent: React.FC<StudyQuadrantProps> = ({
  quadrant,
  color,
  bgOpacity,
  startFrame,
  scaleDuration,
  studyName,
  stat,
  subtext,
  mixedLabel,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Calculate quadrant position
  const halfW = GRID_W / 2;
  const halfH = GRID_H / 2;
  let qLeft: number, qTop: number;

  switch (quadrant) {
    case 'top-left':
      qLeft = GRID_X;
      qTop = GRID_Y;
      break;
    case 'top-right':
      qLeft = GRID_X + halfW;
      qTop = GRID_Y;
      break;
    case 'bottom-left':
      qLeft = GRID_X;
      qTop = GRID_Y + halfH;
      break;
    case 'bottom-right':
      qLeft = GRID_X + halfW;
      qTop = GRID_Y + halfH;
      break;
  }

  // Background glow fade-in
  const glowAlpha = interpolate(localFrame, [0, scaleDuration], [0, bgOpacity], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  if (mixedLabel) {
    // Simple mixed result quadrant
    const labelAlpha = interpolate(localFrame, [0, scaleDuration], [0, 0.4], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    });

    return (
      <>
        {/* Amber background tint */}
        <div
          style={{
            position: 'absolute',
            left: qLeft + 1,
            top: qTop + 1,
            width: halfW - 2,
            height: halfH - 2,
            backgroundColor: color,
            opacity: glowAlpha,
          }}
        />
        {/* Label overlay */}
        <div
          style={{
            position: 'absolute',
            left: qLeft,
            top: qTop,
            width: halfW,
            height: halfH,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
          }}
        >
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 11,
              color: color,
              opacity: labelAlpha,
            }}
          >
            {mixedLabel}
          </div>
        </div>
      </>
    );
  }

  // Study quadrant with scale-up stat
  // Easing.out(Easing.back(1.4)) gives a slight overshoot
  const statScale = interpolate(localFrame, [0, scaleDuration], [0.3, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(1.4)),
  });

  const contentAlpha = interpolate(localFrame, [0, scaleDuration * 0.6], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Background glow */}
      <div
        style={{
          position: 'absolute',
          left: qLeft + 1,
          top: qTop + 1,
          width: halfW - 2,
          height: halfH - 2,
          backgroundColor: color,
          opacity: glowAlpha,
        }}
      />
      {/* Content */}
      <div
        style={{
          position: 'absolute',
          left: qLeft,
          top: qTop,
          width: halfW,
          height: halfH,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          justifyContent: 'center',
          gap: 8,
        }}
      >
        {/* Study name */}
        {studyName && (
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 13,
              fontWeight: 700,
              color,
              opacity: 0.7 * contentAlpha,
            }}
          >
            {studyName}
          </div>
        )}
        {/* Stat with scale-up */}
        {stat && (
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 32,
              fontWeight: 700,
              color,
              opacity: 0.85 * contentAlpha,
              transform: `scale(${statScale})`,
            }}
          >
            {stat}
          </div>
        )}
        {/* Subtext */}
        {subtext && (
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 9,
              color: SUBTEXT_COLOR,
              opacity: 0.35 * contentAlpha,
            }}
          >
            {subtext}
          </div>
        )}
      </div>
    </>
  );
};

export default QuadrantContent;
