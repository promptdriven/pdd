import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TITLE, COLORS, OPACITIES, TIMING, CANVAS } from './constants';

/** Section label — fades in starting at frame 15 */
export const SectionLabel: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(
    frame,
    [TIMING.labelFadeIn.start, TIMING.labelFadeIn.start + TIMING.labelFadeIn.duration],
    [0, OPACITIES.labelText],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(2)) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.labelY,
        left: 0,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.labelFontSize,
        fontWeight: TITLE.labelFontWeight,
        color: COLORS.textSecondary,
        letterSpacing: TITLE.labelLetterSpacing,
        opacity,
        transform: 'translateY(-50%)',
      }}
    >
      {TITLE.sectionLabel}
    </div>
  );
};

/** "WHERE TO" — types on character-by-character starting at frame 40 */
export const TitleLine1: React.FC = () => {
  const frame = useCurrentFrame();
  const text = TITLE.line1;
  const startFrame = TIMING.line1TypeOn.start;
  const charDelay = TIMING.line1TypeOn.charDelay;

  // How many characters are visible
  const elapsed = Math.max(0, frame - startFrame);
  const visibleChars = Math.min(text.length, Math.floor(elapsed / charDelay) + 1);

  // Only render once the sequence starts
  if (frame < startFrame) return null;

  const displayText = text.slice(0, visibleChars);

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.line1Y,
        left: 0,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.fontSize,
        fontWeight: TITLE.fontWeight,
        color: COLORS.textPrimary,
        transform: 'translateY(-50%)',
        whiteSpace: 'pre',
      }}
    >
      {displayText}
    </div>
  );
};

/** Horizontal rule — draws from center outward starting at frame 60 */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();
  const startFrame = TIMING.ruleDraw.start;
  const duration = TIMING.ruleDraw.duration;

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.poly(2)) }
  );

  if (progress <= 0) return null;

  const halfWidth = (TITLE.ruleWidth / 2) * progress;
  const centerX = CANVAS.width / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.ruleY,
        left: centerX - halfWidth,
        width: halfWidth * 2,
        height: TITLE.ruleHeight,
        backgroundColor: COLORS.rule,
        opacity: OPACITIES.rule,
        transform: 'translateY(-50%)',
      }}
    />
  );
};

/** "START" — fades in + slides up starting at frame 70 */
export const TitleLine2: React.FC = () => {
  const frame = useCurrentFrame();
  const startFrame = TIMING.line2FadeSlide.start;
  const duration = TIMING.line2FadeSlide.duration;

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) }
  );

  if (progress <= 0) return null;

  const opacity = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(2)) }
  );

  const slideY = interpolate(progress, [0, 1], [10, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        top: TITLE.line2Y + slideY,
        left: TITLE.line2OffsetX,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TITLE.fontSize,
        fontWeight: TITLE.fontWeight,
        color: COLORS.textPrimary,
        opacity,
        transform: 'translateY(-50%)',
      }}
    >
      {TITLE.line2}
    </div>
  );
};
