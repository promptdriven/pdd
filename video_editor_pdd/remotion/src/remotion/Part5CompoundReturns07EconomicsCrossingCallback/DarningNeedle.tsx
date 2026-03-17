// DarningNeedle.tsx — Darning needle icon with animated strikethrough
import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, OPACITIES, NEEDLE_POS, FRAMES } from './constants';

interface DarningNeedleProps {
  /** Opacity (controlled by parent for fade-in) */
  opacity: number;
}

/**
 * Renders a darning needle icon with eye loop at NEEDLE_POS,
 * followed by a red strikethrough line that draws on after a delay.
 */
export const DarningNeedle: React.FC<DarningNeedleProps> = ({ opacity }) => {
  const frame = useCurrentFrame();
  const { x, y } = NEEDLE_POS;

  // Scale-in with back easing: 0→1 over 15 frames
  const scaleIn = interpolate(frame, [0, FRAMES.needleScaleDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.back(1.3)),
  });

  // Strikethrough draw progress: starts after 10 frames, draws over 10 frames
  const strikeProgress = interpolate(
    frame,
    [
      FRAMES.strikethroughDelay,
      FRAMES.strikethroughDelay + FRAMES.strikethroughDuration,
    ],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Needle dimensions
  const needleLength = 50;
  const eyeRadius = 6;

  // Needle is drawn at a 45-degree angle (upper-left to lower-right)
  // Tip at bottom-right, eye at top-left
  const tipX = x + needleLength / 2;
  const tipY = y + needleLength / 2;
  const eyeX = x - needleLength / 2;
  const eyeY = y - needleLength / 2;

  // Strikethrough line: perpendicular slash
  const strikeFromX = x - 20;
  const strikeFromY = y + 20;
  const strikeToX = x + 20;
  const strikeToY = y - 20;

  // Interpolated end point of the strikethrough
  const strikeEndX = strikeFromX + (strikeToX - strikeFromX) * strikeProgress;
  const strikeEndY = strikeFromY + (strikeToY - strikeFromY) * strikeProgress;

  return (
    <div
      style={{
        position: 'absolute',
        inset: 0,
        opacity,
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <g
          transform={`translate(${x}, ${y}) scale(${scaleIn}) translate(${-x}, ${-y})`}
        >
          {/* Needle shaft */}
          <line
            x1={eyeX + eyeRadius * 0.7}
            y1={eyeY + eyeRadius * 0.7}
            x2={tipX}
            y2={tipY}
            stroke={COLORS.needle}
            strokeWidth={2}
            strokeOpacity={OPACITIES.needle}
            strokeLinecap="round"
          />
          {/* Needle eye (loop) */}
          <ellipse
            cx={eyeX}
            cy={eyeY}
            rx={eyeRadius}
            ry={eyeRadius * 0.6}
            fill="none"
            stroke={COLORS.needle}
            strokeWidth={1.5}
            strokeOpacity={OPACITIES.needle}
            transform={`rotate(45, ${eyeX}, ${eyeY})`}
          />
          {/* Needle point (sharper tip) */}
          <line
            x1={tipX - 3}
            y1={tipY - 3}
            x2={tipX + 1}
            y2={tipY + 1}
            stroke={COLORS.needle}
            strokeWidth={1.5}
            strokeOpacity={OPACITIES.needle + 0.1}
            strokeLinecap="round"
          />
        </g>

        {/* Strikethrough — drawn on with progress */}
        {strikeProgress > 0 && (
          <line
            x1={strikeFromX}
            y1={strikeFromY}
            x2={strikeEndX}
            y2={strikeEndY}
            stroke={COLORS.strikethrough}
            strokeWidth={2.5}
            strokeOpacity={OPACITIES.strikethrough}
            strokeLinecap="round"
          />
        )}
      </svg>
    </div>
  );
};

export default DarningNeedle;
