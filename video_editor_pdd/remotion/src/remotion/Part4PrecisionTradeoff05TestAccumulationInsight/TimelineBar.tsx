import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMELINE_X_START, TIMELINE_X_END, TIMELINE_HEIGHT, COLUMN_X, STAGE_COLORS } from './constants';

interface TimelineBarProps {
  y: number;
  drawStartFrame: number;
  drawDuration: number;
  fillStartFrame: number;
  fillDuration: number;
}

/**
 * A horizontal timeline bar with three markers and a gradient fill.
 */
const TimelineBar: React.FC<TimelineBarProps> = ({
  y,
  drawStartFrame,
  drawDuration,
  fillStartFrame,
  fillDuration,
}) => {
  const frame = useCurrentFrame();

  // Track draw-in
  const trackDraw = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Gradient fill progress
  const fillProgress = interpolate(
    frame,
    [fillStartFrame, fillStartFrame + fillDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  const totalWidth = TIMELINE_X_END - TIMELINE_X_START;
  const trackWidth = totalWidth * trackDraw;
  const fillWidth = totalWidth * fillProgress;

  const markers = [
    { label: 'Day 1', x: COLUMN_X[0], color: STAGE_COLORS.day1 },
    { label: 'Month 1', x: COLUMN_X[1], color: STAGE_COLORS.month1 },
    { label: 'Month 6', x: COLUMN_X[2], color: STAGE_COLORS.month6 },
  ];

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: 1920,
        height: 1080,
        pointerEvents: 'none',
      }}
    >
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="timelineGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={STAGE_COLORS.day1} />
            <stop offset="50%" stopColor={STAGE_COLORS.month1} />
            <stop offset="100%" stopColor={STAGE_COLORS.month6} />
          </linearGradient>
          <clipPath id="fillClip">
            <rect x={TIMELINE_X_START} y={y} width={fillWidth} height={TIMELINE_HEIGHT} />
          </clipPath>
        </defs>

        {/* Track background */}
        <rect
          x={TIMELINE_X_START}
          y={y}
          width={trackWidth}
          height={TIMELINE_HEIGHT}
          rx={TIMELINE_HEIGHT / 2}
          fill="#1E293B"
          opacity={0.6}
        />

        {/* Gradient fill */}
        <rect
          x={TIMELINE_X_START}
          y={y}
          width={totalWidth}
          height={TIMELINE_HEIGHT}
          rx={TIMELINE_HEIGHT / 2}
          fill="url(#timelineGrad)"
          opacity={0.8}
          clipPath="url(#fillClip)"
        />

        {/* Marker dots and labels */}
        {markers.map((marker, i) => {
          const markerOpacity = interpolate(
            frame,
            [drawStartFrame + i * 10, drawStartFrame + i * 10 + 15],
            [0, 1],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
          );
          return (
            <g key={i} opacity={markerOpacity}>
              <circle
                cx={marker.x}
                cy={y + TIMELINE_HEIGHT / 2}
                r={5}
                fill={marker.color}
                opacity={0.7}
              />
              <text
                x={marker.x}
                y={y + TIMELINE_HEIGHT + 18}
                textAnchor="middle"
                fontFamily="Inter, sans-serif"
                fontSize={10}
                fill={marker.color}
                opacity={0.5}
              >
                {marker.label}
              </text>
            </g>
          );
        })}
      </svg>

      {/* "→ safer over time" label */}
      <div
        style={{
          position: 'absolute',
          left: TIMELINE_X_END + 10,
          top: y - 2,
          fontFamily: 'Inter, sans-serif',
          fontSize: 10,
          color: STAGE_COLORS.month6,
          opacity: 0.4 * fillProgress,
          whiteSpace: 'nowrap',
        }}
      >
        → safer over time
      </div>
    </div>
  );
};

export default TimelineBar;
