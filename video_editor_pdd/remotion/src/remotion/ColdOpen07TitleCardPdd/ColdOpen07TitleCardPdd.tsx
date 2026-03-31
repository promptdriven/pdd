// ColdOpen07TitleCardPdd – "Prompt-Driven Development" title card
// Overlays a semi-transparent dark layer on top of a simulated code editor,
// then fades in the title text with a subtle slide-up + blue glow.

import React from 'react';
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from 'remotion';

import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  OVERLAY_COLOR,
  OVERLAY_OPACITY,
  TITLE_COLOR,
  TITLE_TEXT,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_LETTER_SPACING,
  TITLE_GLOW_SHADOW,
  OVERLAY_FADE_START,
  OVERLAY_FADE_END,
  TITLE_FADE_START,
  TITLE_FADE_END,
  TITLE_OFFSET_Y,
  BACKGROUND_COLOR,
} from './constants';
import { FakeCodeEditor } from './FakeCodeEditor';

// ── Default props (required by barrel export) ───────────────────────
export const defaultColdOpen07TitleCardPddProps = {};

// ── Main component ──────────────────────────────────────────────────
export const ColdOpen07TitleCardPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Overlay fade: 0→15 frames, easeOut(quad) ─────────────────────
  const overlayOpacity = interpolate(
    frame,
    [OVERLAY_FADE_START, OVERLAY_FADE_END],
    [0, OVERLAY_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    },
  );

  // ── Title opacity: 15→35 frames, easeOut(cubic) ──────────────────
  const titleOpacity = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // ── Title translateY: 15→35 frames, +10px → 0 ────────────────────
  const titleTranslateY = interpolate(
    frame,
    [TITLE_FADE_START, TITLE_FADE_END],
    [TITLE_OFFSET_Y, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Layer 1 – Simulated code-editor background (spec 06 inheritance) */}
      <AbsoluteFill>
        <FakeCodeEditor />
      </AbsoluteFill>

      {/* Layer 2 – Dark overlay that fades in over the code */}
      <AbsoluteFill
        style={{
          backgroundColor: OVERLAY_COLOR,
          opacity: overlayOpacity,
        }}
      />

      {/* Layer 3 – Title text */}
      <AbsoluteFill
        style={{
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
        }}
      >
        <div
          style={{
            opacity: titleOpacity,
            transform: `translateY(${titleTranslateY}px)`,
            fontFamily: "'Inter', sans-serif",
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            letterSpacing: TITLE_LETTER_SPACING,
            textShadow: TITLE_GLOW_SHADOW,
            textAlign: 'center',
            lineHeight: 1.1,
            userSelect: 'none',
            // Slight upward offset to match spec center at y=480
            marginTop: -60,
          }}
        >
          {TITLE_TEXT}
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen07TitleCardPdd;
