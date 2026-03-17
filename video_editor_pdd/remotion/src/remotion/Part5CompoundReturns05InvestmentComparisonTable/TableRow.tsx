import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, TABLE } from './constants';
import type { RowData } from './constants';

// Simple SVG icons for each row type
const BugIcon: React.FC = () => (
  <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke={COLORS.muted} strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" style={{ opacity: 0.4 }}>
    <path d="M8 2l1.88 1.88M14.12 3.88L16 2M9 7.13v-1a3.003 3.003 0 116 0v1" />
    <path d="M12 20c-3.3 0-6-2.7-6-6v-3a4 4 0 014-4h4a4 4 0 014 4v3c0 3.3-2.7 6-6 6z" />
    <path d="M12 20v-9M6.53 9C4.6 8.8 3 7.1 3 5M6 13H2M6 17l-4 1M17.47 9c1.93-.2 3.53-1.9 3.53-4M18 13h4M18 17l4 1" />
  </svg>
);

const CodeIcon: React.FC = () => (
  <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke={COLORS.muted} strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" style={{ opacity: 0.4 }}>
    <polyline points="16 18 22 12 16 6" />
    <polyline points="8 6 2 12 8 18" />
    <line x1="14" y1="4" x2="10" y2="20" />
  </svg>
);

const DocumentIcon: React.FC = () => (
  <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke={COLORS.muted} strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" style={{ opacity: 0.4 }}>
    <path d="M14 2H6a2 2 0 00-2 2v16a2 2 0 002 2h12a2 2 0 002-2V8z" />
    <polyline points="14 2 14 8 20 8" />
    <line x1="16" y1="13" x2="8" y2="13" />
    <line x1="16" y1="17" x2="8" y2="17" />
    <polyline points="10 9 9 9 8 9" />
  </svg>
);

const ICONS: Record<string, React.FC> = {
  bug: BugIcon,
  code: CodeIcon,
  document: DocumentIcon,
};

interface TableRowProps {
  row: RowData;
  /** Frame offset when this row starts appearing */
  startFrame: number;
  /** Whether the PDD pulse is active (frame 210-240) */
  pulseProgress: number;
}

export const TableRow: React.FC<TableRowProps> = ({ row, startFrame, pulseProgress }) => {
  const frame = useCurrentFrame();
  const relativeFrame = frame - startFrame;

  // Row slide-in: easeOut(cubic) from y+15 over 20 frames
  const slideY = interpolate(
    relativeFrame,
    [0, 20],
    [15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const rowOpacity = interpolate(
    relativeFrame,
    [0, 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Staggered cell reveals: investment at 0, patching at +10, pdd at +20
  const patchingOpacity = interpolate(
    relativeFrame,
    [10, 25],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const pddOpacity = interpolate(
    relativeFrame,
    [20, 35],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // PDD glow appear
  const glowOpacity = interpolate(
    relativeFrame,
    [20, 35],
    [0, row.pddGlow],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // PDD pulse effect (from parent timing)
  const pulseExtra = pulseProgress > 0
    ? interpolate(
        pulseProgress,
        [0, 0.5, 1],
        [0, 0.1, 0],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      )
    : 0;

  const IconComponent = ICONS[row.icon] || BugIcon;

  const bgColor = row.alternate
    ? `rgba(17, 24, 39, 0.3)`
    : COLORS.background;

  return (
    <div
      style={{
        display: 'flex',
        width: TABLE.width,
        height: TABLE.rowHeight,
        transform: `translateY(${slideY}px)`,
        opacity: rowOpacity,
        borderBottom: `1px solid rgba(30, 41, 59, 0.3)`,
        backgroundColor: bgColor,
      }}
    >
      {/* Investment cell */}
      <div
        style={{
          width: TABLE.colWidth,
          height: TABLE.rowHeight,
          display: 'flex',
          alignItems: 'center',
          paddingLeft: 24,
          gap: 10,
        }}
      >
        <IconComponent />
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 16,
            color: COLORS.text,
          }}
        >
          {row.investment}
        </span>
      </div>

      {/* Patching cell */}
      <div
        style={{
          width: TABLE.colWidth,
          height: TABLE.rowHeight,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: patchingOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 15,
            color: COLORS.patching,
            opacity: 0.6,
          }}
        >
          {row.patching}
        </span>
      </div>

      {/* PDD cell */}
      <div
        style={{
          width: TABLE.colWidth,
          height: TABLE.rowHeight,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
          opacity: pddOpacity,
          position: 'relative',
        }}
      >
        {/* Glow background */}
        <div
          style={{
            position: 'absolute',
            inset: 4,
            borderRadius: 6,
            backgroundColor: COLORS.pdd,
            opacity: glowOpacity + pulseExtra,
          }}
        />
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: 15,
            fontWeight: 600,
            color: COLORS.pdd,
            opacity: row.pddOpacity + pulseExtra,
            position: 'relative',
            zIndex: 1,
          }}
        >
          {row.pdd}
        </span>
      </div>
    </div>
  );
};

export default TableRow;
