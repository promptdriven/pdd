import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { COLORS, LAYOUT, TIMING } from './constants';
import { LedgerGrid } from './LedgerGrid';
import { DivergingCurves } from './DivergingCurves';

export const defaultPart5CompoundReturns01SectionTitleCardProps = {};

/**
 * Section 5.1: Part 5 Title Card — Compound Returns
 * Duration: 120 frames (4s @ 30fps)
 */
export const Part5CompoundReturns01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Background fade from black (frames 0-15) ---
  const bgOpacity = interpolate(frame, [0, TIMING.bgFadeEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // --- "PART 5" fade-in (frames 15-35) ---
  const part5Opacity = interpolate(
    frame,
    [TIMING.part5FadeStart, TIMING.part5FadeStart + TIMING.textFadeDuration],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // --- "COMPOUND" typewriter (frames 40+, 3 frames per character) ---
  const compoundText = 'COMPOUND';
  const typewriterStart = TIMING.compoundTypeStart;
  const visibleChars = Math.min(
    compoundText.length,
    Math.max(0, Math.floor((frame - typewriterStart) / TIMING.charDelay) + 1)
  );
  const displayedCompound = frame >= typewriterStart ? compoundText.slice(0, visibleChars) : '';

  // --- Horizontal rule draw from center (frames 60-70) ---
  const ruleProgress = interpolate(
    frame,
    [TIMING.ruleDrawStart, TIMING.ruleDrawStart + TIMING.ruleDrawDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleHalfWidth = LAYOUT.ruleHalfWidth * ruleProgress;

  // --- "RETURNS" fade-in + slide-up (frames 70-90) ---
  const returnsOpacity = interpolate(
    frame,
    [TIMING.returnsFadeStart, TIMING.returnsFadeStart + TIMING.returnsFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );
  const returnsSlideY = interpolate(
    frame,
    [TIMING.returnsFadeStart, TIMING.returnsFadeStart + TIMING.returnsFadeDuration],
    [TIMING.returnsSlideDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#000000' }}>
      {/* Main content with background fade */}
      <AbsoluteFill style={{ opacity: bgOpacity, backgroundColor: COLORS.background }}>
        {/* Ledger grid */}
        <LedgerGrid />

        {/* Ghost diverging curves — start at frame 15 */}
        <Sequence from={TIMING.curvesDrawStart}>
          <DivergingCurves />
        </Sequence>

        {/* "PART 5" section label */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.sectionLabelY,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 14,
            fontWeight: 600,
            color: COLORS.sectionLabel,
            opacity: part5Opacity,
            letterSpacing: 4,
            userSelect: 'none',
          }}
        >
          PART 5
        </div>

        {/* "COMPOUND" — typewriter effect */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.titleLine1Y,
            left: 0,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 72,
            fontWeight: 700,
            color: COLORS.titleText,
            userSelect: 'none',
            lineHeight: 1,
          }}
        >
          {/* Use invisible text to reserve space, overlay visible typed chars */}
          <span style={{ visibility: 'hidden' }}>{compoundText}</span>
          <span
            style={{
              position: 'absolute',
              left: 0,
              right: 0,
              textAlign: 'center',
            }}
          >
            {displayedCompound}
            {/* Blinking cursor during typing */}
            {frame >= typewriterStart && visibleChars < compoundText.length && (
              <span
                style={{
                  borderRight: `2px solid ${COLORS.titleText}`,
                  opacity: frame % 10 < 5 ? 1 : 0,
                  marginLeft: 2,
                }}
              />
            )}
          </span>
        </div>

        {/* Horizontal rule — draws from center outward */}
        {frame >= TIMING.ruleDrawStart && (
          <div
            style={{
              position: 'absolute',
              top: LAYOUT.ruleY,
              left: LAYOUT.centerX - ruleHalfWidth,
              width: ruleHalfWidth * 2,
              height: 2,
              backgroundColor: COLORS.rule,
              opacity: 0.5,
            }}
          />
        )}

        {/* "RETURNS" — fade in + slide up */}
        <div
          style={{
            position: 'absolute',
            top: LAYOUT.titleLine2Y + returnsSlideY,
            left: LAYOUT.titleLine2OffsetX,
            width: '100%',
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: 72,
            fontWeight: 700,
            color: COLORS.titleText,
            opacity: returnsOpacity,
            userSelect: 'none',
            lineHeight: 1,
          }}
        >
          RETURNS
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns01SectionTitleCard;
