import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  Easing,
  interpolate,
} from 'remotion';
import { COLORS, QUOTE_TEXT, ATTRIBUTION_TEXT, TIMING } from './constants';
import { NoiseTexture } from './NoiseTexture';
import { WordByWord } from './WordByWord';
import { NarratorReframe } from './NarratorReframe';

export const defaultPart5CompoundReturns08ContrarianQuoteCardProps = {};

/**
 * Section 5.8: Contrarian Quote Card — "The Bet"
 *
 * A clean, typographic quote card with word-by-word reveal,
 * color-coded highlights, and a narrator reframe.
 * 300 frames @ 30fps = 10 seconds.
 */
export const Part5CompoundReturns08ContrarianQuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Background fade ──────────────────────────────────────────────────────
  const bgOpacity = interpolate(
    frame,
    [TIMING.bgFadeStart, TIMING.bgFadeStart + TIMING.bgFadeDuration],
    [0, 1],
    {
      easing: Easing.out(Easing.quad),
      extrapolateRight: 'clamp',
    }
  );

  // ── Decorative quote mark fade ───────────────────────────────────────────
  const quoteMarkOpacity = interpolate(
    frame,
    [TIMING.quoteMarkStart, TIMING.quoteMarkStart + TIMING.quoteMarkFadeDuration],
    [0, 0.15],
    {
      easing: Easing.out(Easing.quad),
      extrapolateRight: 'clamp',
    }
  );

  // ── Attribution fade ─────────────────────────────────────────────────────
  const attributionOpacity = interpolate(
    frame,
    [TIMING.attributionStart, TIMING.attributionStart + TIMING.attributionFadeDuration],
    [0, 0.4],
    {
      easing: Easing.out(Easing.quad),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
        opacity: bgOpacity,
      }}
    >
      {/* Noise texture overlay */}
      <NoiseTexture />

      {/* Decorative opening quote mark */}
      <div
        style={{
          position: 'absolute',
          left: 320,
          top: 340,
          fontFamily: 'Georgia, serif',
          fontSize: 120,
          color: COLORS.decorativeQuote,
          opacity: quoteMarkOpacity,
          lineHeight: 1,
          userSelect: 'none',
        }}
      >
        {'\u201C'}
      </div>

      {/* Quote text — word by word with highlights */}
      <WordByWord
        text={QUOTE_TEXT}
        startFrame={TIMING.wordTypingStart}
        highlightStartFrame={TIMING.highlightStart}
      />

      {/* Attribution */}
      <div
        style={{
          position: 'absolute',
          right: 640,
          top: 580,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: COLORS.attribution,
          opacity: attributionOpacity,
          textAlign: 'right',
          whiteSpace: 'nowrap',
        }}
      >
        {ATTRIBUTION_TEXT}
      </div>

      {/* Narrator reframe */}
      <NarratorReframe startFrame={TIMING.reframeStart} />
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns08ContrarianQuoteCard;
