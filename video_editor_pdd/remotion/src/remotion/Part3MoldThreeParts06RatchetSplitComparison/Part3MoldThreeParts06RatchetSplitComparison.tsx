import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import '../_shared/load-inter-font';
import {
  BG_BLACK,
  SPLIT_X,
  SPLIT_LINE_COLOR,
  TEXT_PRIMARY,
  GREEN,
  CALLOUT_Y,
  FRAME,
} from './constants';
import { TraditionalPanel } from './TraditionalPanel';
import { PddPanel } from './PddPanel';
import { TimelineBar } from './TimelineBar';

// ── Split Divider ──
const SplitDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const lineHeight = interpolate(
    frame,
    [FRAME.SPLIT_DRAW_START, FRAME.SPLIT_DRAW_START + FRAME.SPLIT_DRAW_DUR],
    [0, 100],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: SPLIT_X - 1,
        top: 0,
        width: 2,
        height: `${lineHeight}%`,
        backgroundColor: SPLIT_LINE_COLOR,
        opacity: 0.25,
      }}
    />
  );
};

// ── Callout Text ──
const CalloutText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [FRAME.CALLOUT_START, FRAME.CALLOUT_START + FRAME.CALLOUT_DUR],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulse on "everywhere, forever"
  const pulsePhase = Math.max(0, frame - FRAME.CALLOUT_START - FRAME.CALLOUT_DUR);
  const pulse = pulsePhase > 0
    ? 0.8 + 0.2 * Math.sin(pulsePhase * 0.1)
    : 0.8;

  if (frame < FRAME.CALLOUT_START) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: CALLOUT_Y,
        width: 1920,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: 14,
        color: TEXT_PRIMARY,
        opacity,
      }}
    >
      A bug fix helps one place. A test prevents that bug{' '}
      <span
        style={{
          fontWeight: 700,
          color: GREEN,
          opacity: pulse,
        }}
      >
        everywhere, forever
      </span>
      .
    </div>
  );
};

// ── Main Component ──
export const Part3MoldThreeParts06RatchetSplitComparison: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_BLACK,
        overflow: 'hidden',
      }}
    >
      {/* Left Panel — Traditional */}
      <TraditionalPanel />

      {/* Split divider */}
      <SplitDivider />

      {/* Right Panel — PDD */}
      <PddPanel />

      {/* Timeline bar at bottom */}
      <TimelineBar />

      {/* Callout text */}
      <CalloutText />
    </AbsoluteFill>
  );
};

export const defaultPart3MoldThreeParts06RatchetSplitComparisonProps = {};

export default Part3MoldThreeParts06RatchetSplitComparison;
