import React from 'react';
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from 'remotion';
import { COLORS, TIMING } from './constants';

/** "PART 3" section label — fades in at frame 15 */
export const SectionLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.PART3_FADE_START, TIMING.PART3_FADE_START + 20],
    [0, 0.5],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: 400,
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color: COLORS.SECTION_LABEL,
          letterSpacing: 4,
          opacity,
          textAlign: 'center',
        }}
      >
        PART 3
      </div>
    </AbsoluteFill>
  );
};

/** "THE MOLD HAS" — typewriter effect starting at frame 40 */
export const TitleLine1: React.FC = () => {
  const frame = useCurrentFrame();
  const text = TIMING.TITLE1_TEXT;

  const localFrame = frame - TIMING.TITLE1_START;
  if (localFrame < 0) return null;

  const charsVisible = Math.min(
    Math.floor(localFrame / TIMING.TITLE1_CHAR_DELAY) + 1,
    text.length
  );

  const visibleText = text.slice(0, charsVisible);

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: 460,
          fontFamily: 'Inter, sans-serif',
          fontSize: 72,
          fontWeight: 700,
          color: COLORS.TITLE,
          textAlign: 'center',
          whiteSpace: 'pre',
        }}
      >
        {visibleText}
      </div>
    </AbsoluteFill>
  );
};

/** Horizontal rule — draws from center outward at frame 60 */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.RULE_START;
  if (localFrame < 0) return null;

  const progress = interpolate(
    localFrame,
    [0, TIMING.RULE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const halfWidth = 100 * progress; // 200px total

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: 505,
          width: halfWidth * 2,
          height: 2,
          backgroundColor: COLORS.RULE,
          opacity: 0.5,
        }}
      />
    </AbsoluteFill>
  );
};

/** "THREE PARTS" — fade in + slide up at frame 70 */
export const TitleLine2: React.FC = () => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.TITLE2_START;
  if (localFrame < 0) return null;

  const opacity = interpolate(
    localFrame,
    [0, TIMING.TITLE2_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    localFrame,
    [0, TIMING.TITLE2_FADE_DURATION],
    [TIMING.TITLE2_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'flex-start',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: 545,
          left: '50%',
          transform: `translateX(calc(-50% + 15px)) translateY(${translateY}px)`,
          fontFamily: 'Inter, sans-serif',
          fontSize: 72,
          fontWeight: 700,
          color: COLORS.TITLE,
          textAlign: 'center',
          opacity,
          whiteSpace: 'nowrap',
        }}
      >
        THREE PARTS
      </div>
    </AbsoluteFill>
  );
};
