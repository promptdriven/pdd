import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { TITLE, POSITIONS, COLORS, TIMING } from './constants';

/** Typewriter effect for title line 1 */
export const TypewriterText: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const text = TITLE.LINE1;
  const visibleChars =
    relFrame < 0
      ? 0
      : Math.min(
          text.length,
          Math.floor(relFrame / TIMING.TITLE_LINE1_CHAR_DELAY) + 1
        );

  const displayed = text.slice(0, visibleChars);

  return (
    <text
      x={POSITIONS.CENTER_X}
      y={POSITIONS.TITLE_LINE1_Y}
      textAnchor="middle"
      fontFamily="Inter, sans-serif"
      fontSize={TITLE.FONT_SIZE}
      fontWeight={TITLE.FONT_WEIGHT}
      fill={COLORS.TITLE_TEXT}
      dominantBaseline="central"
    >
      {displayed}
    </text>
  );
};

/** Fade-in + slide-up for title line 2 */
export const SlideUpText: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const opacity =
    relFrame < 0
      ? 0
      : interpolate(relFrame, [0, TIMING.TITLE_LINE2_FADE], [0, 1], {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        });

  const translateY =
    relFrame < 0
      ? TIMING.TITLE_LINE2_SLIDE
      : interpolate(
          relFrame,
          [0, TIMING.TITLE_LINE2_FADE],
          [TIMING.TITLE_LINE2_SLIDE, 0],
          {
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

  return (
    <text
      x={POSITIONS.CENTER_X + POSITIONS.TITLE_LINE2_OFFSET_X}
      y={POSITIONS.TITLE_LINE2_Y + translateY}
      textAnchor="middle"
      fontFamily="Inter, sans-serif"
      fontSize={TITLE.FONT_SIZE}
      fontWeight={TITLE.FONT_WEIGHT}
      fill={COLORS.TITLE_TEXT}
      opacity={opacity}
      dominantBaseline="central"
    >
      {TITLE.LINE2}
    </text>
  );
};

/** Section label "PART 4" with fade-in */
export const SectionLabel: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const opacity =
    relFrame < 0
      ? 0
      : interpolate(relFrame, [0, TIMING.SECTION_LABEL_FADE], [0, 0.5], {
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        });

  return (
    <text
      x={POSITIONS.CENTER_X}
      y={POSITIONS.SECTION_LABEL_Y}
      textAnchor="middle"
      fontFamily="Inter, sans-serif"
      fontSize={TITLE.LABEL_SIZE}
      fontWeight={TITLE.LABEL_WEIGHT}
      fill={COLORS.SECTION_LABEL}
      opacity={opacity}
      letterSpacing={TITLE.LABEL_LETTER_SPACING}
      dominantBaseline="central"
    >
      {TITLE.SECTION_LABEL}
    </text>
  );
};

/** Horizontal rule that draws from center outward */
export const HorizontalRule: React.FC<{ startFrame: number }> = ({
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const relFrame = frame - startFrame;

  const progress =
    relFrame < 0
      ? 0
      : interpolate(relFrame, [0, TIMING.RULE_DRAW_DURATION], [0, 1], {
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.quad),
        });

  const halfWidth = 100; // 200px / 2
  const currentHalf = halfWidth * progress;

  return (
    <line
      x1={POSITIONS.CENTER_X - currentHalf}
      y1={POSITIONS.RULE_Y}
      x2={POSITIONS.CENTER_X + currentHalf}
      y2={POSITIONS.RULE_Y}
      stroke={COLORS.RULE}
      strokeWidth={2}
      opacity={0.5 * progress}
    />
  );
};
