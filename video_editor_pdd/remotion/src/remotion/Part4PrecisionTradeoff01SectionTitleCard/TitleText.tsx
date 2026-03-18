import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import { COLORS, OPACITIES, POSITIONS, TIMING, TYPOGRAPHY } from './constants';

/** Section label "PART 4" */
export const SectionLabel: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.labelFadeStart;

  const opacity = interpolate(
    localFrame,
    [0, TIMING.labelFadeDuration],
    [0, OPACITIES.sectionLabel],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.sectionLabel.y,
        left: 0,
        width: '100%',
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.sectionLabel.size,
        fontWeight: TYPOGRAPHY.sectionLabel.weight,
        letterSpacing: TYPOGRAPHY.sectionLabel.letterSpacing,
        color: COLORS.sectionLabel,
        opacity,
      }}
    >
      PART 4
    </div>
  );
};

/** Typewriter "THE PRECISION" */
export const TitleLine1: React.FC = () => {
  const frame = useCurrentFrame();
  const text = 'THE PRECISION';
  const localFrame = frame - TIMING.typewriterStart;

  const charsVisible = localFrame >= 0
    ? Math.min(Math.floor(localFrame / TIMING.charDelay) + 1, text.length)
    : 0;

  const displayText = text.slice(0, charsVisible);

  // Even at frame 0 of the typewriter, we show the first character
  // Opacity is 1 as soon as the sequence starts
  const opacity = localFrame >= 0 ? 1 : 0;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.titleLine1.y,
        left: 0,
        width: '100%',
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.title.size,
        fontWeight: TYPOGRAPHY.title.weight,
        color: COLORS.titleText,
        opacity,
        whiteSpace: 'pre',
      }}
    >
      {displayText}
      {charsVisible < text.length && charsVisible > 0 && (
        <span
          style={{
            display: 'inline-block',
            width: 3,
            height: TYPOGRAPHY.title.size * 0.8,
            backgroundColor: COLORS.titleText,
            marginLeft: 2,
            verticalAlign: 'middle',
            opacity: frame % 16 < 8 ? 0.7 : 0,
          }}
        />
      )}
    </div>
  );
};

/** Horizontal rule between title lines */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.ruleStart;

  if (localFrame < 0) return null;

  const drawProgress = interpolate(
    localFrame,
    [0, TIMING.ruleDuration],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.inOut(Easing.quad) }
  );

  const halfWidth = POSITIONS.rule.halfWidth;
  const currentHalf = halfWidth * drawProgress;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.rule.y,
        left: '50%',
        transform: 'translateX(-50%)',
        width: currentHalf * 2,
        height: 2,
        backgroundColor: COLORS.rule,
        opacity: OPACITIES.rule,
      }}
    />
  );
};

/** Fade-in + slide-up "TRADEOFF" */
export const TitleLine2: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - TIMING.tradeoffStart;

  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, TIMING.tradeoffDuration],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const translateY = interpolate(
    localFrame,
    [0, TIMING.tradeoffDuration],
    [TIMING.tradeoffSlideDistance, 0],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.titleLine2.y,
        left: 0,
        width: '100%',
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: TYPOGRAPHY.title.size,
        fontWeight: TYPOGRAPHY.title.weight,
        color: COLORS.titleText,
        opacity,
        transform: `translateY(${translateY}px)`,
        // offset-right 15px
        paddingLeft: 30,
      }}
    >
      TRADEOFF
    </div>
  );
};
