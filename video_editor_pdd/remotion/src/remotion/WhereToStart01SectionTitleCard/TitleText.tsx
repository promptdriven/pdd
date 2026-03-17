import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { CANVAS, COLORS, TITLE, TIMING } from './constants';

/** Typewriter effect for "WHERE TO" */
export const TypewriterTitle: React.FC = () => {
  const frame = useCurrentFrame();
  const text = TITLE.LINE1;

  // Characters revealed based on charDelay
  const charsRevealed = Math.floor(frame / TIMING.CHAR_DELAY);
  const visibleText = text.slice(0, Math.min(charsRevealed + 1, text.length));

  // Cursor blink (only while typing)
  const isTyping = charsRevealed < text.length;
  const cursorVisible = isTyping && Math.floor(frame / 4) % 2 === 0;

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.LINE1_Y,
        left: 0,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.FONT_SIZE,
        fontWeight: TITLE.FONT_WEIGHT,
        color: COLORS.TITLE,
        lineHeight: 1,
        whiteSpace: 'pre',
      }}
    >
      {visibleText}
      {cursorVisible && (
        <span style={{ opacity: 0.6 }}>|</span>
      )}
    </div>
  );
};

/** Fade-in + slide-up for "START" */
export const SlideUpTitle: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, TIMING.TITLE_LINE2_FADE], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const translateY = interpolate(frame, [0, TIMING.TITLE_LINE2_FADE], [TIMING.TITLE_LINE2_SLIDE, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.LINE2_Y,
        left: TITLE.LINE2_OFFSET_X,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.FONT_SIZE,
        fontWeight: TITLE.FONT_WEIGHT,
        color: COLORS.TITLE,
        lineHeight: 1,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {TITLE.LINE2}
    </div>
  );
};

/** Section label "WHERE TO START" small text */
export const SectionLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, TIMING.LABEL_FADE], [0, 0.5], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.LABEL_Y,
        left: 0,
        width: CANVAS.WIDTH,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.LABEL_SIZE,
        fontWeight: TITLE.LABEL_WEIGHT,
        color: COLORS.LABEL,
        letterSpacing: TITLE.LABEL_LETTER_SPACING,
        lineHeight: 1,
        opacity,
        textTransform: 'uppercase',
      }}
    >
      {TITLE.LABEL}
    </div>
  );
};

/** Horizontal rule drawing from center outward */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, TIMING.RULE_DRAW], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const halfWidth = (TITLE.RULE_WIDTH / 2) * progress;
  const centerX = CANVAS.WIDTH / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.RULE_Y,
        left: centerX - halfWidth,
        width: halfWidth * 2,
        height: TITLE.RULE_HEIGHT,
        backgroundColor: COLORS.RULE,
        opacity: 0.5,
      }}
    />
  );
};
