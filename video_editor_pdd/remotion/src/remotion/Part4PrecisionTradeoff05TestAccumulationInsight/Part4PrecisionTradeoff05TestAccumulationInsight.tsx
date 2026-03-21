import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import StageColumn from './StageColumn';
import ConnectingArrow from './ConnectingArrow';
import TimelineBar from './TimelineBar';
import {
  CANVAS,
  COLORS,
  STAGES,
  COLUMN_X,
  TITLE_Y,
  TIMELINE_Y,
  CALLOUT_Y,
  ANIM,
} from './constants';

export const defaultPart4PrecisionTradeoff05TestAccumulationInsightProps = {};

export const Part4PrecisionTradeoff05TestAccumulationInsight: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Title fade-in ──
  const titleOpacity = interpolate(
    frame,
    [ANIM.titleStart, ANIM.titleStart + ANIM.titleDur],
    [0, 0.7],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Callout fade-in ──
  const calloutOpacity = interpolate(
    frame,
    [ANIM.calloutStart, ANIM.calloutStart + ANIM.calloutDur],
    [0, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Arrow Y position (roughly midway in the stages area)
  const arrowY = 350;

  // Arrow X positions: span the gap between column edges (spec positions)
  const arrow1FromX = 470;
  const arrow1ToX = 650;
  const arrow2FromX = 1020;
  const arrow2ToX = 1200;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.background,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* ── Section Title ── */}
      <div
        style={{
          position: 'absolute',
          top: TITLE_Y,
          width: CANVAS.width,
          textAlign: 'center',
          fontSize: 18,
          fontWeight: 700,
          color: COLORS.titleText,
          opacity: titleOpacity,
          letterSpacing: 3,
        }}
      >
        TEST ACCUMULATION OVER TIME
      </div>

      {/* ── Stage 1: Day 1 ── */}
      <StageColumn
        stage={STAGES[0]}
        centerX={COLUMN_X[0]}
        animStartFrame={ANIM.stage1Start}
        animDuration={ANIM.stage1Dur}
      />

      {/* ── Arrow 1 → 2 ── */}
      <ConnectingArrow
        fromX={arrow1FromX}
        toX={arrow1ToX}
        y={arrowY}
        animStartFrame={ANIM.arrow1Start}
        animDuration={ANIM.arrow1Dur}
        label="walls added, prompt simplified"
      />

      {/* ── Stage 2: Month 1 ── */}
      <StageColumn
        stage={STAGES[1]}
        centerX={COLUMN_X[1]}
        animStartFrame={ANIM.stage2Start}
        animDuration={ANIM.stage2Dur}
      />

      {/* ── Arrow 2 → 3 ── */}
      <ConnectingArrow
        fromX={arrow2FromX}
        toX={arrow2ToX}
        y={arrowY}
        animStartFrame={ANIM.arrow2Start}
        animDuration={ANIM.arrow2Dur}
        label="walls added, prompt simplified"
      />

      {/* ── Stage 3: Month 6 ── */}
      <StageColumn
        stage={STAGES[2]}
        centerX={COLUMN_X[2]}
        animStartFrame={ANIM.stage3Start}
        animDuration={ANIM.stage3Dur}
        isLast
      />

      {/* ── Timeline Bar ── */}
      <TimelineBar
        y={TIMELINE_Y}
        drawStartFrame={ANIM.timelineDrawStart}
        drawDuration={ANIM.timelineDrawDur}
        fillStartFrame={ANIM.timelineFillStart}
        fillDuration={ANIM.timelineFillDur}
      />

      {/* ── Callout ── */}
      <div
        style={{
          position: 'absolute',
          top: CALLOUT_Y,
          width: CANVAS.width,
          textAlign: 'center',
          fontSize: 13,
          color: COLORS.calloutText,
          opacity: calloutOpacity,
          lineHeight: 1.6,
        }}
      >
        Not just about catching bugs. It&apos;s about making prompts{' '}
        <span style={{ color: COLORS.simplerHighlight, fontWeight: 600 }}>
          simpler
        </span>{' '}
        and regeneration{' '}
        <span style={{ color: COLORS.saferHighlight, fontWeight: 600 }}>
          safer
        </span>{' '}
        over time.
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff05TestAccumulationInsight;
