import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import { LedgerGrid } from './LedgerGrid';
import { DivergingCurves } from './DivergingCurves';
import {
  BG_COLOR,
  TITLE_COLOR,
  LABEL_COLOR,
  RULE_COLOR,
  FONT_FAMILY,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_LETTER_SPACING,
  LABEL_Y,
  COMPOUND_Y,
  RULE_Y,
  RETURNS_Y,
  RETURNS_X_OFFSET,
  RULE_HALF_WIDTH,
  WIDTH,
  BG_FADE_END,
  LABEL_START,
  COMPOUND_START,
  COMPOUND_CHAR_DELAY,
  RULE_START,
  RULE_DURATION,
  RETURNS_START,
  RETURNS_SLIDE_DURATION,
  FADE_DURATION,
  TOTAL_FRAMES,
} from './constants';

// ── Default props (required by export contract) ─────────────────────
export const defaultPart5CompoundReturns01SectionTitleCardProps = {};

// ── Helpers ─────────────────────────────────────────────────────────

/** Typewriter reveal: returns the visible slice of `text` at the given frame. */
function typewriterText(text: string, localFrame: number, charDelay: number): string {
  if (localFrame < 0) return '';
  const visibleChars = Math.min(
    text.length,
    Math.floor(localFrame / charDelay) + 1,
  );
  return text.slice(0, visibleChars);
}

// ── Main Component ──────────────────────────────────────────────────

export const Part5CompoundReturns01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Background fade (0 → 15) ────────────────────────────────────
  const bgOpacity = interpolate(frame, [0, BG_FADE_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // ── "PART 5" label fade (15 → 35) ──────────────────────────────
  const labelLocalFrame = frame - LABEL_START;
  const labelOpacity = interpolate(labelLocalFrame, [0, FADE_DURATION], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.poly(2)), // easeOut(quad)
  });

  // ── "COMPOUND" typewriter (40 → ~64) ────────────────────────────
  const compoundLocal = frame - COMPOUND_START;
  const compoundText = typewriterText('COMPOUND', compoundLocal, COMPOUND_CHAR_DELAY);

  // ── Horizontal rule draw (60 → 70) ─────────────────────────────
  const ruleLocal = frame - RULE_START;
  const ruleProgress = interpolate(ruleLocal, [0, RULE_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.poly(2)), // easeInOut(quad)
  });
  const ruleWidth = RULE_HALF_WIDTH * 2 * ruleProgress;

  // ── "RETURNS" fade + slide-up (70 → 90) ────────────────────────
  const returnsLocal = frame - RETURNS_START;
  const returnsOpacity = interpolate(
    returnsLocal,
    [0, RETURNS_SLIDE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)), // easeOut(quad)
    },
  );
  const returnsSlideY = interpolate(
    returnsLocal,
    [0, RETURNS_SLIDE_DURATION],
    [10, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)), // easeOut(cubic)
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: 1080,
        overflow: 'hidden',
      }}
    >
      {/* Layer 1 — Ledger grid */}
      <LedgerGrid opacity={bgOpacity} />

      {/* Layer 2 — Diverging ghost curves */}
      <DivergingCurves />

      {/* Layer 3 — Section label: "PART 5" */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: 'absolute',
            width: '100%',
            top: LABEL_Y,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: LABEL_FONT_SIZE,
            fontWeight: LABEL_FONT_WEIGHT,
            color: LABEL_COLOR,
            letterSpacing: LABEL_LETTER_SPACING,
            opacity: labelOpacity,
            userSelect: 'none',
          }}
        >
          PART 5
        </div>
      </Sequence>

      {/* Layer 4 — "COMPOUND" title (typewriter) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: 'absolute',
            width: '100%',
            top: COMPOUND_Y,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            lineHeight: 1,
            userSelect: 'none',
          }}
        >
          {compoundText}
        </div>
      </Sequence>

      {/* Layer 5 — Horizontal rule */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: 'absolute',
            top: RULE_Y,
            left: (WIDTH - ruleWidth) / 2,
            width: ruleWidth,
            height: 2,
            backgroundColor: RULE_COLOR,
            opacity: ruleLocal >= 0 ? 0.5 : 0,
            pointerEvents: 'none',
          }}
        />
      </Sequence>

      {/* Layer 6 — "RETURNS" title (fade + slide-up) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <div
          style={{
            position: 'absolute',
            width: '100%',
            top: RETURNS_Y + returnsSlideY,
            textAlign: 'center',
            fontFamily: FONT_FAMILY,
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            opacity: returnsOpacity,
            lineHeight: 1,
            paddingLeft: RETURNS_X_OFFSET,
            userSelect: 'none',
          }}
        >
          RETURNS
        </div>
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns01SectionTitleCard;
