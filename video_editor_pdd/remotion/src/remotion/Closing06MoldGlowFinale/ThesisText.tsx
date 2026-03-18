import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  THESIS_TEXT,
  THESIS_FONT,
  THESIS_SIZE,
  THESIS_COLOR,
  THESIS_OPACITY,
  THESIS_Y,
  THESIS_START,
  THESIS_FADE_DURATION,
  HR_WIDTH,
  HR_Y,
  HR_COLOR,
  HR_OPACITY,
  HR_DRAW_DURATION,
  WIDTH,
} from './constants';

export const ThesisText: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = Math.max(0, frame - THESIS_START);

  // Horizontal rule draws from center outward
  const hrProgress = interpolate(
    localFrame,
    [0, HR_DRAW_DURATION],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  const hrHalfWidth = (HR_WIDTH / 2) * hrProgress;
  const centerX = WIDTH / 2;

  // Text fades in after 8 frames from thesis start
  const textLocalFrame = Math.max(0, localFrame - 8);
  const textOpacity = interpolate(
    textLocalFrame,
    [0, THESIS_FADE_DURATION],
    [0, THESIS_OPACITY],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  if (frame < THESIS_START) return null;

  return (
    <>
      {/* Horizontal rule */}
      <div
        style={{
          position: 'absolute',
          left: centerX - hrHalfWidth,
          top: HR_Y,
          width: hrHalfWidth * 2,
          height: 1,
          backgroundColor: HR_COLOR,
          opacity: HR_OPACITY,
        }}
      />

      {/* Thesis text */}
      <div
        style={{
          position: 'absolute',
          top: THESIS_Y,
          left: 0,
          width: WIDTH,
          textAlign: 'center',
          fontFamily: THESIS_FONT,
          fontSize: THESIS_SIZE,
          fontWeight: 400,
          color: THESIS_COLOR,
          opacity: textOpacity,
        }}
      >
        {THESIS_TEXT}
      </div>
    </>
  );
};
