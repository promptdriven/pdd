import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  TABLE_X,
  TABLE_Y,
  TABLE_WIDTH,
  TABLE_ROW_HEIGHT,
  COL_WIDTHS,
  TABLE_BORDER_RADIUS,
  TABLE_BG,
  TABLE_HEADER_BG,
  DIVIDER_COLOR,
  TEXT_SECONDARY,
  TEXT_PRIMARY,
  TABLE_ROWS,
  TIMING,
  AMBER,
} from './constants';

const HEADER_HEIGHT = 50;

export const SummaryTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Table background fade-in (starts at frame 60, relative to sequence)
  const tableBgOpacity = interpolate(
    frame,
    [TIMING.MOLD_SLIDE_START, TIMING.MOLD_SLIDE_START + 30],
    [0, 0.4],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Header type-in
  const headerOpacity = interpolate(
    frame,
    [TIMING.TABLE_HEADER_START, TIMING.TABLE_HEADER_START + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Row appear timings
  const rowStartFrames = [TIMING.ROW1_START, TIMING.ROW2_START, TIMING.ROW3_START];
  const rowDurations = [TIMING.ROW_DURATION, TIMING.ROW_DURATION, TIMING.ROW3_DURATION];

  // Tests row pulse (after conflict line appears)
  const testsPulse =
    frame >= TIMING.CONFLICT_START
      ? interpolate(
          Math.sin(((frame - TIMING.CONFLICT_START) / 30) * Math.PI * 2),
          [-1, 1],
          [0.5, 0.9],
        )
      : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: TABLE_X,
        top: TABLE_Y,
        width: TABLE_WIDTH,
        borderRadius: TABLE_BORDER_RADIUS,
        overflow: 'hidden',
        backgroundColor: TABLE_BG,
        opacity: tableBgOpacity / 0.4, // normalize: container fades from 0→1
      }}
    >
      {/* Table background fill */}
      <div
        style={{
          position: 'absolute',
          inset: 0,
          backgroundColor: TABLE_BG,
          opacity: tableBgOpacity,
          borderRadius: TABLE_BORDER_RADIUS,
        }}
      />

      {/* Header Row */}
      <div
        style={{
          display: 'flex',
          height: HEADER_HEIGHT,
          backgroundColor: TABLE_HEADER_BG,
          alignItems: 'center',
          opacity: headerOpacity,
          borderBottom: `1px solid ${DIVIDER_COLOR}33`,
        }}
      >
        {['COMPONENT', 'ENCODES', 'OWNER'].map((header, i) => (
          <div
            key={header}
            style={{
              width: COL_WIDTHS[i],
              paddingLeft: i === 0 ? 24 : 16,
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              fontWeight: 600,
              color: TEXT_SECONDARY,
              letterSpacing: 2,
            }}
          >
            {header}
          </div>
        ))}
      </div>

      {/* Data Rows */}
      {TABLE_ROWS.map((row, rowIndex) => {
        const startFrame = rowStartFrames[rowIndex];
        const duration = rowDurations[rowIndex];

        const rowProgress = interpolate(
          frame,
          [startFrame, startFrame + duration],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
        );

        const slideX = interpolate(rowProgress, [0, 1], [30, 0]);
        const rowOpacity = rowProgress;

        // Determine border opacity — pulse for Tests after conflict line
        const borderOpacity = row.emphasized && frame >= TIMING.CONFLICT_START
          ? testsPulse
          : row.emphasized
            ? 0.7
            : 0.5;

        return (
          <div
            key={row.component}
            style={{
              display: 'flex',
              height: TABLE_ROW_HEIGHT,
              alignItems: 'center',
              opacity: rowOpacity,
              transform: `translateX(${slideX}px)`,
              position: 'relative',
              borderBottom:
                rowIndex < TABLE_ROWS.length - 1
                  ? `1px solid ${DIVIDER_COLOR}33`
                  : 'none',
              backgroundColor: row.emphasized
                ? `${AMBER}0A` // ~0.04 opacity
                : 'transparent',
            }}
          >
            {/* Left accent border */}
            <div
              style={{
                position: 'absolute',
                left: 0,
                top: 0,
                bottom: 0,
                width: row.accentWidth,
                backgroundColor: row.color,
                opacity: borderOpacity,
              }}
            />

            {/* Component column */}
            <div
              style={{
                width: COL_WIDTHS[0],
                paddingLeft: 24,
                display: 'flex',
                alignItems: 'center',
                gap: 10,
              }}
            >
              {/* Color dot */}
              <div
                style={{
                  width: 10,
                  height: 10,
                  borderRadius: '50%',
                  backgroundColor: row.color,
                  boxShadow: `0 0 8px ${row.color}66`,
                  flexShrink: 0,
                }}
              />
              <span
                style={{
                  fontFamily: 'Inter, sans-serif',
                  fontSize: 18,
                  fontWeight: row.componentWeight,
                  color: row.color,
                }}
              >
                {row.component}
              </span>
            </div>

            {/* Encodes column */}
            <div
              style={{
                width: COL_WIDTHS[1],
                paddingLeft: 16,
                fontFamily: 'Inter, sans-serif',
                fontSize: 16,
                fontWeight: row.encodesWeight,
                color: TEXT_PRIMARY,
                opacity: 0.8,
              }}
            >
              {row.encodes}
            </div>

            {/* Owner column */}
            <div
              style={{
                width: COL_WIDTHS[2],
                paddingLeft: 16,
                fontFamily: 'Inter, sans-serif',
                fontSize: 14,
                color: TEXT_SECONDARY,
                opacity: 0.6,
              }}
            >
              {row.owner}
            </div>
          </div>
        );
      })}
    </div>
  );
};
