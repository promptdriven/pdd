import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CHART_BG,
  MUTED,
  FADE_DURATION,
  SLIDE_DISTANCE,
  CONNECTION_LINE_DURATION,
} from './constants';

interface AnnotationCalloutProps {
  startFrame: number;
  title: string | string[];
  titleColor: string;
  subtitle: string;
  borderColor: string;
  x: number;
  y: number;
  /** Connection line target point {x, y} in absolute coords */
  targetX: number;
  targetY: number;
  extra?: string;
  extraColor?: string;
}

const AnnotationCallout: React.FC<AnnotationCalloutProps> = ({
  startFrame,
  title,
  titleColor,
  subtitle,
  borderColor,
  x,
  y,
  targetX,
  targetY,
  extra,
  extraColor,
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - startFrame;

  if (localFrame < 0) return null;

  // Fade + slide in
  const fadeProgress = interpolate(localFrame, [0, FADE_DURATION], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const slideOffset = interpolate(
    localFrame,
    [0, FADE_DURATION],
    [SLIDE_DISTANCE, 0],
    {
      easing: Easing.out(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Connection line draw progress (starts after fade begins)
  const lineProgress = interpolate(
    localFrame,
    [5, 5 + CONNECTION_LINE_DURATION],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const titles = Array.isArray(title) ? title : [title];

  // Calculate connection line start point (left edge of callout box)
  const boxLeft = x;
  const boxCenterY = y + 20;

  // Interpolated line endpoint
  const lineEndX = boxLeft + (targetX - boxLeft) * lineProgress;
  const lineEndY = boxCenterY + (targetY - boxCenterY) * lineProgress;

  return (
    <>
      {/* Connection line */}
      <svg
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: '100%',
          height: '100%',
          pointerEvents: 'none',
          opacity: fadeProgress,
        }}
      >
        <line
          x1={boxLeft}
          y1={boxCenterY}
          x2={lineEndX}
          y2={lineEndY}
          stroke={borderColor}
          strokeWidth={1}
          opacity={0.25}
        />
        {/* Small dot at target end */}
        {lineProgress > 0.9 && (
          <circle
            cx={targetX}
            cy={targetY}
            r={3}
            fill={borderColor}
            opacity={0.4 * fadeProgress}
          />
        )}
      </svg>

      {/* Callout box */}
      <div
        style={{
          position: 'absolute',
          left: x + slideOffset,
          top: y,
          width: 420,
          opacity: fadeProgress,
          backgroundColor: CHART_BG,
          border: `1px solid ${borderColor}`,
          borderRadius: 6,
          padding: '12px 16px',
          boxSizing: 'border-box',
        }}
      >
        {titles.map((t, i) => (
          <div
            key={i}
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: titles.length > 1 ? 13 : 14,
              fontWeight: 700,
              color: titleColor,
              opacity: 0.8,
              lineHeight: 1.4,
              marginBottom: i < titles.length - 1 ? 2 : 0,
            }}
          >
            {t}
          </div>
        ))}

        <div
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 9,
            color: MUTED,
            opacity: 0.35,
            marginTop: 6,
            lineHeight: 1.3,
          }}
        >
          {subtitle}
        </div>

        {extra && (
          <div
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 10,
              color: extraColor || '#E74C3C',
              opacity: 0.6,
              marginTop: 4,
              lineHeight: 1.3,
            }}
          >
            {extra}
          </div>
        )}
      </div>
    </>
  );
};

export default AnnotationCallout;
