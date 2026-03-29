import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  NOTCH_WIDTH,
  NOTCH_HEIGHT,
  NOTCH_COLOR,
  NOTCH_OPACITY,
  NOTCH_LABEL_COLOR,
  NOTCH_LABEL_OPACITY,
  FONT_FAMILY,
  PHASE_NOTCH_POP_DURATION,
} from './constants';

interface NotchMarkProps {
  /** 0–1 fraction along the bar */
  fraction: number;
  /** Label text below the notch */
  label: string;
  /** Absolute frame at which this notch starts its pop-in */
  appearFrame: number;
}

/**
 * A single notch mark on the spectrum — a small vertical tick
 * with a tiny label, representing a "dip into code".
 */
export const NotchMark: React.FC<NotchMarkProps> = ({
  fraction,
  label,
  appearFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - appearFrame;

  if (localFrame < 0) return null;

  // Pop-in with easeOut(back) — overshoot scale
  const scale = interpolate(
    localFrame,
    [0, PHASE_NOTCH_POP_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );

  const notchX = BAR_X + BAR_WIDTH * fraction;
  const notchTop = BAR_Y + BAR_HEIGHT / 2 - NOTCH_HEIGHT / 2;

  return (
    <>
      {/* Vertical tick */}
      <div
        style={{
          position: 'absolute',
          left: notchX - NOTCH_WIDTH / 2,
          top: notchTop,
          width: NOTCH_WIDTH,
          height: NOTCH_HEIGHT,
          backgroundColor: NOTCH_COLOR,
          opacity: NOTCH_OPACITY,
          borderRadius: 2,
          transform: `scaleY(${scale})`,
          transformOrigin: 'center center',
        }}
      />

      {/* Label below bar */}
      <div
        style={{
          position: 'absolute',
          left: notchX,
          top: BAR_Y + BAR_HEIGHT + 8,
          transform: `translateX(-50%) scale(${scale})`,
          transformOrigin: 'center top',
          fontFamily: FONT_FAMILY,
          fontSize: 9,
          fontWeight: 400,
          color: NOTCH_LABEL_COLOR,
          opacity: NOTCH_LABEL_OPACITY * scale,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>
    </>
  );
};
