import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TABLE, ROWS, ANIM } from './constants';
import { TableRow } from './TableRow';
import { SummaryLine } from './SummaryLine';

export const defaultPart5CompoundReturns05InvestmentComparisonTableProps = {};

export const Part5CompoundReturns05InvestmentComparisonTable: React.FC = () => {
  const frame = useCurrentFrame();

  // Table container fade-in: easeOut(quad) over 20 frames
  const containerOpacity = interpolate(
    frame,
    [ANIM.tableAppear.start, ANIM.tableAppear.start + ANIM.tableAppear.duration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // PDD pulse progress (0-1 during frames 210-240)
  const pulseProgress =
    frame >= ANIM.pddPulse.start && frame <= ANIM.pddPulse.start + ANIM.pddPulse.duration
      ? (frame - ANIM.pddPulse.start) / ANIM.pddPulse.duration
      : 0;

  // Row start frames
  const rowStartFrames = [ANIM.row1.start, ANIM.row2.start, ANIM.row3.start];

  // Calculate table total height for vertical centering
  const tableContentHeight = TABLE.headerHeight + TABLE.rowHeight * ROWS.length;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Table container — centered */}
      <div
        style={{
          position: 'absolute',
          top: TABLE.centerY - tableContentHeight / 2,
          left: TABLE.centerX - TABLE.width / 2,
          width: TABLE.width,
          opacity: containerOpacity,
          border: `1px solid rgba(51, 65, 85, 0.3)`,
          borderRadius: TABLE.borderRadius,
          overflow: 'hidden',
          backgroundColor: COLORS.background,
        }}
      >
        {/* Header row */}
        <div
          style={{
            display: 'flex',
            width: TABLE.width,
            height: TABLE.headerHeight,
            backgroundColor: `rgba(30, 41, 59, 0.4)`,
          }}
        >
          {/* INVESTMENT header */}
          <div
            style={{
              width: TABLE.colWidth,
              height: TABLE.headerHeight,
              display: 'flex',
              alignItems: 'center',
              paddingLeft: 24,
            }}
          >
            <span
              style={{
                fontSize: 12,
                fontWeight: 600,
                color: COLORS.muted,
                opacity: 0.5,
                letterSpacing: 2,
              }}
            >
              INVESTMENT
            </span>
          </div>

          {/* PATCHING header */}
          <div
            style={{
              width: TABLE.colWidth,
              height: TABLE.headerHeight,
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
            }}
          >
            <span
              style={{
                fontSize: 12,
                fontWeight: 600,
                color: COLORS.patching,
                opacity: 0.5,
                letterSpacing: 2,
              }}
            >
              PATCHING
            </span>
          </div>

          {/* PDD header */}
          <div
            style={{
              width: TABLE.colWidth,
              height: TABLE.headerHeight,
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
            }}
          >
            <span
              style={{
                fontSize: 12,
                fontWeight: 600,
                color: COLORS.pdd,
                opacity: 0.5,
                letterSpacing: 2,
              }}
            >
              PDD
            </span>
          </div>
        </div>

        {/* Data rows */}
        {ROWS.map((row, index) => (
          <TableRow
            key={row.investment}
            row={row}
            startFrame={rowStartFrames[index]}
            pulseProgress={
              // Only pass pulse progress once all rows have been revealed
              frame >= ANIM.pddPulse.start ? pulseProgress : 0
            }
          />
        ))}
      </div>

      {/* Summary line */}
      <SummaryLine />
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns05InvestmentComparisonTable;
