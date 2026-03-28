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
  NOTCH_FONT_SIZE,
  LABEL_FONT_FAMILY,
  NOTCH_POP_DURATION,
} from './constants';

interface NotchMarkProps {
  fraction: number;
  label: string;
  /** The absolute frame at which this notch starts appearing */
  appearFrame: number;
}

export const NotchMark: React.FC<NotchMarkProps> = ({
  fraction,
  label,
  appearFrame,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - appearFrame;

  if (localFrame < 0) return null;

  // ── Pop-in scale with easeOut(back) ──
  const popScale = interpolate(
    localFrame,
    [0, NOTCH_POP_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.back(1.7)) }
  );

  const popOpacity = interpolate(
    localFrame,
    [0, NOTCH_POP_DURATION * 0.5],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const notchX = BAR_X + BAR_WIDTH * fraction;
  // Center the notch vertically on the bar
  const notchTop = BAR_Y + (BAR_HEIGHT - NOTCH_HEIGHT) / 2;

  return (
    <>
      {/* Notch tick */}
      <div
        style={{
          position: 'absolute',
          left: notchX - NOTCH_WIDTH / 2,
          top: notchTop,
          width: NOTCH_WIDTH,
          height: NOTCH_HEIGHT,
          backgroundColor: NOTCH_COLOR,
          opacity: NOTCH_OPACITY * popOpacity,
          borderRadius: 1,
          transform: `scaleY(${popScale})`,
          transformOrigin: 'center center',
        }}
      />

      {/* Notch label */}
      <div
        style={{
          position: 'absolute',
          left: notchX,
          top: BAR_Y + BAR_HEIGHT + 8,
          transform: `translateX(-50%) scale(${popScale})`,
          transformOrigin: 'center top',
          fontFamily: LABEL_FONT_FAMILY,
          fontSize: NOTCH_FONT_SIZE,
          fontWeight: 400,
          color: NOTCH_LABEL_COLOR,
          opacity: NOTCH_LABEL_OPACITY * popOpacity,
          whiteSpace: 'nowrap',
          textAlign: 'center',
        }}
      >
        {label}
      </div>
    </>
  );
};

export default NotchMark;
