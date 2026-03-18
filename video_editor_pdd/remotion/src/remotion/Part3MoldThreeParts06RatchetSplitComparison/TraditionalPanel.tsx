import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BG_LEFT_PANEL,
  RED,
  TEXT_SECONDARY,
  TEXT_MUTED,
  PANEL_WIDTH,
  ROW_HEIGHT,
  HEADER_Y,
  TRADITIONAL_ROWS,
  FRAME,
} from './constants';

// ── Single row in the traditional panel ──
const TraditionalRow: React.FC<{
  bug: string;
  action: string;
  index: number;
  yOffset: number;
}> = ({ bug, action, index, yOffset }) => {
  const frame = useCurrentFrame();
  const appearFrame = FRAME.LEFT_ROW_START + index * FRAME.LEFT_ROW_STAGGER;

  const opacity = interpolate(frame, [appearFrame, appearFrame + 15], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const slideX = interpolate(frame, [appearFrame, appearFrame + 15], [-20, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const y = 80 + index * ROW_HEIGHT + yOffset;

  return (
    <div
      style={{
        position: 'absolute',
        left: 30,
        top: y,
        width: PANEL_WIDTH - 60,
        height: ROW_HEIGHT,
        opacity,
        transform: `translateX(${slideX}px)`,
        display: 'flex',
        alignItems: 'center',
        gap: 12,
      }}
    >
      {/* Red X icon */}
      <div
        style={{
          width: 20,
          height: 20,
          flexShrink: 0,
          display: 'flex',
          alignItems: 'center',
          justifyContent: 'center',
        }}
      >
        <svg width="16" height="16" viewBox="0 0 16 16">
          <line x1="2" y1="2" x2="14" y2="14" stroke={RED} strokeWidth="2.5" strokeLinecap="round" />
          <line x1="14" y1="2" x2="2" y2="14" stroke={RED} strokeWidth="2.5" strokeLinecap="round" />
        </svg>
      </div>

      {/* Text content */}
      <div style={{ flex: 1, minWidth: 0 }}>
        <div
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 12,
            color: TEXT_SECONDARY,
            whiteSpace: 'nowrap',
            overflow: 'hidden',
            textOverflow: 'ellipsis',
          }}
        >
          {bug}
        </div>
        <div
          style={{
            fontFamily: 'JetBrains Mono, monospace',
            fontSize: 10,
            color: TEXT_MUTED,
            opacity: 0.5,
            marginTop: 2,
          }}
        >
          → {action}
        </div>
      </div>
    </div>
  );
};

// ── Full Traditional Panel ──
export const TraditionalPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Header fade
  const headerOpacity = interpolate(frame, [0, FRAME.HEADERS_DUR], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Scrolling offset after frame 200
  const scrollOffset = interpolate(
    frame,
    [FRAME.LEFT_SCROLL_START, FRAME.TOTAL],
    [0, -180],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.linear,
    }
  );

  // Patch counter — increments as rows appear
  const visibleRowCount = Math.min(
    TRADITIONAL_ROWS.length,
    Math.max(
      0,
      Math.floor((frame - FRAME.LEFT_ROW_START) / FRAME.LEFT_ROW_STAGGER) + 1
    )
  );

  const counterOpacity = interpolate(
    frame,
    [FRAME.LEFT_ROW_START + 10, FRAME.LEFT_ROW_START + 25],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: PANEL_WIDTH,
        height: '100%',
        backgroundColor: BG_LEFT_PANEL,
        overflow: 'hidden',
      }}
    >
      {/* Header */}
      <div
        style={{
          position: 'absolute',
          top: HEADER_Y,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: RED,
          opacity: headerOpacity,
          letterSpacing: 2,
        }}
      >
        TRADITIONAL
      </div>

      {/* Scrolling row container */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          transform: `translateY(${scrollOffset}px)`,
        }}
      >
        {TRADITIONAL_ROWS.map((row, i) => (
          <TraditionalRow
            key={i}
            bug={row.bug}
            action={row.action}
            index={i}
            yOffset={0}
          />
        ))}
      </div>

      {/* Effort counter */}
      <div
        style={{
          position: 'absolute',
          bottom: 260,
          width: '100%',
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 16,
          color: RED,
          opacity: counterOpacity,
        }}
      >
        Patches: {visibleRowCount}
      </div>
    </div>
  );
};

export default TraditionalPanel;
