import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BAR_X,
  BAR_Y,
  BAR_WIDTH,
  BAR_HEIGHT,
  BAR_BORDER_RADIUS,
  BAR_BORDER_COLOR,
  LEFT_COLOR,
  MID_COLOR,
  RIGHT_COLOR,
  FONT_FAMILY,
  PHASE_BAR_START,
  PHASE_BAR_DRAW_DURATION,
  PHASE_LABELS_START,
  PHASE_LABELS_FADE_DURATION,
} from './constants';

const GRADIENT_ID = 'spectrumGradient';

/**
 * The horizontal spectrum bar that draws outward from center,
 * plus the "Pure natural language" / "Pure code" endpoint labels.
 */
export const SpectrumBar: React.FC = () => {
  const frame = useCurrentFrame();

  // Bar "draws from center" by animating clipPath width
  const barProgress = interpolate(
    frame,
    [PHASE_BAR_START, PHASE_BAR_START + PHASE_BAR_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Endpoint labels fade in slightly after bar starts
  const labelOpacity = interpolate(
    frame,
    [PHASE_LABELS_START, PHASE_LABELS_START + PHASE_LABELS_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Clip from center outward
  const halfWidth = (BAR_WIDTH * barProgress) / 2;
  const centerX = BAR_X + BAR_WIDTH / 2;
  const clipLeft = centerX - halfWidth;
  const clipRight = centerX + halfWidth;

  return (
    <>
      {/* SVG for the gradient bar */}
      <svg
        width={BAR_WIDTH + 4}
        height={BAR_HEIGHT + 4}
        style={{
          position: 'absolute',
          left: BAR_X - 2,
          top: BAR_Y - 2,
          overflow: 'visible',
        }}
      >
        <defs>
          <linearGradient id={GRADIENT_ID} x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={LEFT_COLOR} />
            <stop offset="50%" stopColor={MID_COLOR} />
            <stop offset="100%" stopColor={RIGHT_COLOR} />
          </linearGradient>
          <clipPath id="barClip">
            <rect
              x={clipLeft - BAR_X + 2}
              y={0}
              width={clipRight - clipLeft}
              height={BAR_HEIGHT + 4}
            />
          </clipPath>
        </defs>
        <rect
          x={2}
          y={2}
          width={BAR_WIDTH}
          height={BAR_HEIGHT}
          rx={BAR_BORDER_RADIUS}
          ry={BAR_BORDER_RADIUS}
          fill={`url(#${GRADIENT_ID})`}
          stroke={BAR_BORDER_COLOR}
          strokeWidth={1}
          clipPath="url(#barClip)"
        />
      </svg>

      {/* Left label: "Pure natural language" */}
      <div
        style={{
          position: 'absolute',
          left: BAR_X,
          top: BAR_Y - 32,
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 600,
          color: LEFT_COLOR,
          opacity: labelOpacity,
          whiteSpace: 'nowrap',
        }}
      >
        Pure natural language
      </div>

      {/* Right label: "Pure code" */}
      <div
        style={{
          position: 'absolute',
          right: 1920 - (BAR_X + BAR_WIDTH),
          top: BAR_Y - 32,
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 600,
          color: RIGHT_COLOR,
          opacity: labelOpacity,
          textAlign: 'right',
          whiteSpace: 'nowrap',
        }}
      >
        Pure code
      </div>
    </>
  );
};
