import React from 'react';
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from 'remotion';
import { DriftingDots } from './DriftingDots';
import {
  BG_COLOR,
  ACCENT_BLUE,
  TITLE_COLOR,
  SUBTITLE_COLOR,
  RULE_Y,
  RULE_LEFT,
  RULE_RIGHT,
  RULE_CENTER_X,
  RULE_HEIGHT,
  RULE_GLOW_OPACITY,
  RULE_GLOW_BLUR,
  TITLE_TEXT,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_OPACITY,
  TITLE_Y,
  TITLE_LETTER_SPACING,
  TITLE_RISE_FROM_Y,
  SUBTITLE_TEXT,
  SUBTITLE_FONT_SIZE,
  SUBTITLE_FONT_WEIGHT,
  SUBTITLE_OPACITY,
  SUBTITLE_Y,
  SUBTITLE_LETTER_SPACING,
  RULE_DRAW_START,
  RULE_DRAW_END,
  TITLE_RISE_START,
  TITLE_RISE_END,
  SUBTITLE_FADE_START,
  SUBTITLE_FADE_END,
  FADE_OUT_START,
  FADE_OUT_END,
  CANVAS_WIDTH,
} from './constants';

export const defaultColdOpen09PddTitleCardProps = {};

export const ColdOpen09PddTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // === Global fade-out (frames 150-180) ===
  const globalOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  // === Horizontal Rule: draws from center outward (frames 0-30) ===
  const ruleProgress = interpolate(
    frame,
    [RULE_DRAW_START, RULE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const halfWidth = ((RULE_RIGHT - RULE_LEFT) / 2) * ruleProgress;
  const ruleCurrentLeft = RULE_CENTER_X - halfWidth;
  const ruleCurrentRight = RULE_CENTER_X + halfWidth;
  const ruleCurrentWidth = ruleCurrentRight - ruleCurrentLeft;

  // === Title: rises from y:510 to y:460, fades in (frames 30-60) ===
  const titleOpacity = interpolate(
    frame,
    [TITLE_RISE_START, TITLE_RISE_END],
    [0, TITLE_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const titleY = interpolate(
    frame,
    [TITLE_RISE_START, TITLE_RISE_END],
    [TITLE_RISE_FROM_Y, TITLE_Y],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // === Subtitle: fades in (frames 50-80), no vertical motion ===
  const subtitleOpacity = interpolate(
    frame,
    [SUBTITLE_FADE_START, SUBTITLE_FADE_END],
    [0, SUBTITLE_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
      }}
    >
      {/* Background constellation dots */}
      <DriftingDots globalOpacity={globalOpacity} />

      {/* Horizontal rule — draws from center outward */}
      {ruleCurrentWidth > 0 && (
        <div
          style={{
            position: 'absolute',
            left: ruleCurrentLeft,
            top: RULE_Y,
            width: ruleCurrentWidth,
            height: RULE_HEIGHT,
            background: `linear-gradient(90deg, transparent, ${ACCENT_BLUE} 30%, ${ACCENT_BLUE} 70%, transparent)`,
            opacity: globalOpacity,
          }}
        >
          {/* Glow beneath the line */}
          <div
            style={{
              position: 'absolute',
              left: 0,
              top: 0,
              width: '100%',
              height: '100%',
              background: `linear-gradient(90deg, transparent, ${ACCENT_BLUE} 30%, ${ACCENT_BLUE} 70%, transparent)`,
              opacity: RULE_GLOW_OPACITY,
              filter: `blur(${RULE_GLOW_BLUR}px)`,
              boxShadow: `0 0 ${RULE_GLOW_BLUR}px ${ACCENT_BLUE}`,
            }}
          />
        </div>
      )}

      {/* Title text — rises from behind the line */}
      <div
        style={{
          position: 'absolute',
          top: titleY,
          left: 0,
          width: CANVAS_WIDTH,
          display: 'flex',
          justifyContent: 'center',
          opacity: titleOpacity * globalOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontWeight: TITLE_FONT_WEIGHT,
            fontSize: TITLE_FONT_SIZE,
            color: TITLE_COLOR,
            letterSpacing: TITLE_LETTER_SPACING,
            lineHeight: 1,
          }}
        >
          {TITLE_TEXT}
        </span>
      </div>

      {/* Subtitle text — fades in below the line */}
      <div
        style={{
          position: 'absolute',
          top: SUBTITLE_Y,
          left: 0,
          width: CANVAS_WIDTH,
          display: 'flex',
          justifyContent: 'center',
          opacity: subtitleOpacity * globalOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontWeight: SUBTITLE_FONT_WEIGHT,
            fontSize: SUBTITLE_FONT_SIZE,
            color: SUBTITLE_COLOR,
            letterSpacing: SUBTITLE_LETTER_SPACING,
            textTransform: 'uppercase',
            lineHeight: 1,
          }}
        >
          {SUBTITLE_TEXT}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen09PddTitleCard;
