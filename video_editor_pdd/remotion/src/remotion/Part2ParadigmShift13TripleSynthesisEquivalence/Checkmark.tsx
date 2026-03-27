import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  EQUIV_COLOR,
  CHECKMARK_SIZE,
  CHECKMARK_Y,
  EQUIV_LABEL_Y,
  COLUMN_WIDTH,
  CHECKMARK_START,
  CHECKMARK_DURATION,
  LABEL_FADE_DURATION,
} from './constants';

interface CheckmarkProps {
  colX: number;
  index: number;
}

const Checkmark: React.FC<CheckmarkProps> = ({ colX, index }) => {
  const frame = useCurrentFrame();
  const localFrame = frame - CHECKMARK_START;

  if (localFrame < 0) return null;

  // Bounce-in scale with overshoot (emulating easeOut(back) with overshoot 1.2)
  const rawScale = interpolate(localFrame, [0, CHECKMARK_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(1.2)),
  });

  // Label fade
  const labelOpacity = interpolate(
    localFrame,
    [CHECKMARK_DURATION * 0.5, CHECKMARK_DURATION * 0.5 + LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <>
      {/* Checkmark icon */}
      <div
        style={{
          position: 'absolute',
          left: colX - COLUMN_WIDTH / 2,
          top: CHECKMARK_Y,
          width: COLUMN_WIDTH,
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
        }}
      >
        <svg
          width={CHECKMARK_SIZE}
          height={CHECKMARK_SIZE}
          viewBox="0 0 48 48"
          style={{
            transform: `scale(${rawScale})`,
          }}
        >
          {/* Circle background */}
          <circle cx={24} cy={24} r={22} fill={EQUIV_COLOR} opacity={0.15} />
          <circle
            cx={24}
            cy={24}
            r={22}
            fill="none"
            stroke={EQUIV_COLOR}
            strokeWidth={2.5}
          />
          {/* Checkmark path */}
          <polyline
            points="14,24 21,32 34,17"
            fill="none"
            stroke={EQUIV_COLOR}
            strokeWidth={3.5}
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
      </div>

      {/* "Functionally equivalent" label */}
      <div
        style={{
          position: 'absolute',
          left: colX - COLUMN_WIDTH / 2,
          top: EQUIV_LABEL_Y,
          width: COLUMN_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          fontWeight: 600,
          color: EQUIV_COLOR,
          opacity: labelOpacity,
        }}
      >
        Functionally equivalent
      </div>
    </>
  );
};

export default Checkmark;
