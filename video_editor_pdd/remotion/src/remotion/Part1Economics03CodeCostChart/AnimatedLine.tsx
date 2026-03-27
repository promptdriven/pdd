import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  type DataPoint,
  dataToSvgPath,
  getPathLength,
  dataToPixelX,
  CHART_TOP,
  CHART_BOTTOM,
} from './constants';

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  drawStart: number;
  drawEnd: number;
  /** If set, renders a dashed line using a clip-rect reveal instead of strokeDashoffset */
  dashPattern?: string;
  glowActive?: boolean;
  glowStart?: number;
  glowEnd?: number;
  /** unique id for SVG defs (avoid collisions when multiple instances) */
  lineId: string;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  drawStart,
  drawEnd,
  dashPattern,
  glowActive = false,
  glowStart = 0,
  glowEnd = 0,
  lineId,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => dataToSvgPath(data), [data]);
  const totalLength = useMemo(() => getPathLength(data), [data]);

  const drawProgress = interpolate(frame, [drawStart, drawEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // For dashed lines we use a clip-rect approach.
  // For solid lines we use strokeDashoffset.
  const isDashed = !!dashPattern;

  const hiddenLength = totalLength * (1 - drawProgress);

  // Clip rect: reveal from left to right based on data x range
  const firstX = dataToPixelX(data[0].x);
  const lastX = dataToPixelX(data[data.length - 1].x);
  const clipWidth = (lastX - firstX) * drawProgress;

  // Glow effect for pulse animation
  let glowOpacity = 0;
  if (glowActive && frame >= glowStart && frame <= glowEnd) {
    const cycleFrame = (frame - glowStart) % 30;
    glowOpacity = interpolate(cycleFrame, [0, 15, 30], [0, 0.6, 0], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    });
  }

  const filterId = `glow-${lineId}`;
  const clipId = `clip-${lineId}`;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id={filterId} x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="8" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
        {isDashed && (
          <clipPath id={clipId}>
            <rect
              x={firstX - 5}
              y={CHART_TOP - 20}
              width={clipWidth + 10}
              height={CHART_BOTTOM - CHART_TOP + 40}
            />
          </clipPath>
        )}
      </defs>

      {/* Glow layer */}
      {glowActive && glowOpacity > 0 && (
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth + 6}
          opacity={glowOpacity}
          filter={`url(#${filterId})`}
          {...(isDashed
            ? { clipPath: `url(#${clipId})`, strokeDasharray: dashPattern }
            : {
                style: {
                  strokeDasharray: `${totalLength}`,
                  strokeDashoffset: hiddenLength,
                },
              })}
        />
      )}

      {/* Main line */}
      {isDashed ? (
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeDasharray={dashPattern}
          clipPath={`url(#${clipId})`}
        />
      ) : (
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          style={{
            strokeDasharray: `${totalLength}`,
            strokeDashoffset: hiddenLength,
          }}
        />
      )}
    </svg>
  );
};

export default AnimatedLine;
