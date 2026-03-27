import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PANEL_BG,
  PANEL_BORDER,
  PANEL_X,
  PANEL_Y,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_RADIUS,
  PANEL_PADDING,
  TEXT_PRIMARY,
  TEXT_EMPHASIS,
  PURPLE_ACCENT,
  PURPLE_DEEP,
  BADGE_SIZE,
  BADGE_RADIUS,
  BADGE_GAP,
  MAIN_TEXT_WORDS,
  EMPHASIS_TEXT,
  ITALIC_TEXT,
  PANEL_SLIDE_IN_END,
  TEXT_TYPE_START,
  TEXT_TYPE_END,
  EMPHASIS_START,
  EMPHASIS_END,
  ITALIC_START,
  ITALIC_END,
  LOGOS_START,
  LOGOS_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
} from './constants';

/** Word-by-word text renderer with highlighted terms */
const WordByWordText: React.FC = () => {
  const frame = useCurrentFrame();
  const wordCount = MAIN_TEXT_WORDS.length;
  const framesPerWord = (TEXT_TYPE_END - TEXT_TYPE_START) / wordCount;

  return (
    <div
      style={{
        fontFamily: 'Inter, system-ui, sans-serif',
        fontSize: 16,
        fontWeight: 400,
        color: TEXT_PRIMARY,
        lineHeight: 1.6,
        maxWidth: PANEL_WIDTH - PANEL_PADDING * 2,
      }}
    >
      {MAIN_TEXT_WORDS.map((word, i) => {
        const wordAppearFrame = TEXT_TYPE_START + i * framesPerWord;
        const wordOpacity = interpolate(
          frame,
          [wordAppearFrame, wordAppearFrame + 4],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <span
            key={i}
            style={{
              opacity: wordOpacity,
              fontWeight: word.highlight ? 700 : 400,
              color: word.highlight ? PURPLE_ACCENT : TEXT_PRIMARY,
            }}
          >
            {word.text}{' '}
          </span>
        );
      })}
    </div>
  );
};

/** Emphasis pull-quote line */
const EmphasisLine: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [EMPHASIS_START, EMPHASIS_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const scale = interpolate(frame, [EMPHASIS_START, EMPHASIS_END], [0.95, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        fontFamily: 'Inter, system-ui, sans-serif',
        fontSize: 18,
        fontWeight: 600,
        color: TEXT_EMPHASIS,
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'left center',
        marginTop: 20,
        lineHeight: 1.5,
      }}
    >
      {EMPHASIS_TEXT}
    </div>
  );
};

/** Italic mathematical proof line */
const ItalicLine: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [ITALIC_START, ITALIC_END], [0, 0.8], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        fontFamily: 'Inter, system-ui, sans-serif',
        fontSize: 16,
        fontWeight: 400,
        fontStyle: 'italic',
        color: PURPLE_ACCENT,
        opacity,
        marginTop: 16,
        lineHeight: 1.5,
      }}
    >
      {ITALIC_TEXT}
    </div>
  );
};

/** Logo badge pair */
const LogoBadges: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [LOGOS_START, LOGOS_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Subtle glow pulse after appearing
  const glowPulse =
    frame > LOGOS_END
      ? 0.3 +
        0.15 * Math.sin(((frame - LOGOS_END) / 30) * Math.PI * 2)
      : 0;

  const badges = [
    { label: 'Z3', bg: PURPLE_ACCENT },
    { label: 'SF', bg: PURPLE_DEEP },
  ];

  return (
    <div
      style={{
        display: 'flex',
        gap: BADGE_GAP,
        justifyContent: 'center',
        marginTop: 28,
        opacity,
      }}
    >
      {badges.map((badge) => (
        <div
          key={badge.label}
          style={{
            width: BADGE_SIZE,
            height: BADGE_SIZE,
            borderRadius: BADGE_RADIUS,
            backgroundColor: badge.bg,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            boxShadow: `0 0 ${12 + glowPulse * 20}px ${badge.bg}66`,
          }}
        >
          <span
            style={{
              fontFamily: 'Inter, system-ui, sans-serif',
              fontSize: 18,
              fontWeight: 700,
              color: '#FFFFFF',
              letterSpacing: 0.5,
            }}
          >
            {badge.label}
          </span>
        </div>
      ))}
    </div>
  );
};

/**
 * The full annotation panel with slide-in/out and all text content.
 */
export const AnnotationPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Slide-in from right
  const slideInX = interpolate(frame, [0, PANEL_SLIDE_IN_END], [300, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Slide-out to right
  const slideOutX = interpolate(
    frame,
    [PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [0, 300],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  // Panel opacity for slide-in/out
  const slideInOpacity = interpolate(frame, [0, PANEL_SLIDE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });
  const slideOutOpacity = interpolate(
    frame,
    [PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const translateX = slideInX + slideOutX;
  const panelOpacity = Math.min(slideInOpacity, slideOutOpacity);

  return (
    <div
      style={{
        position: 'absolute',
        left: PANEL_X,
        top: PANEL_Y,
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        backgroundColor: PANEL_BG,
        border: `1px solid ${PANEL_BORDER}`,
        borderRadius: PANEL_RADIUS,
        padding: PANEL_PADDING,
        opacity: panelOpacity * 0.95,
        transform: `translateX(${translateX}px)`,
        display: 'flex',
        flexDirection: 'column',
        boxShadow: `0 8px 32px rgba(0,0,0,0.4), inset 0 1px 0 rgba(255,255,255,0.03)`,
        overflow: 'hidden',
      }}
    >
      {/* Subtle top accent line */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: PANEL_PADDING,
          right: PANEL_PADDING,
          height: 2,
          background: `linear-gradient(90deg, transparent, ${PURPLE_ACCENT}66, transparent)`,
          opacity: 0.7,
          borderRadius: 1,
        }}
      />

      <WordByWordText />
      <EmphasisLine />
      <ItalicLine />
      <LogoBadges />
    </div>
  );
};
