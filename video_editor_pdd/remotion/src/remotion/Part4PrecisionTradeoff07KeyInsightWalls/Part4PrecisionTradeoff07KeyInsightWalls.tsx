import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import { BackgroundGradient } from './BackgroundGradient';
import { HorizontalRule } from './HorizontalRule';
import { GlowPulse } from './GlowPulse';
import {
  BACKGROUND_COLOR,
  GRADIENT_LEFT_COLOR,
  GRADIENT_RIGHT_COLOR,
  GRADIENT_OPACITY,
  PRIMARY_TEXT,
  PRIMARY_FONT_SIZE,
  PRIMARY_FONT_WEIGHT,
  PRIMARY_COLOR,
  PRIMARY_Y,
  GLOW_COLOR,
  GLOW_OPACITY,
  GLOW_BLUR,
  GLOW_PULSE_DURATION,
  SECONDARY_TEXT,
  SECONDARY_FONT_SIZE,
  SECONDARY_FONT_WEIGHT,
  SECONDARY_COLOR,
  SECONDARY_TEXT_OPACITY,
  SECONDARY_Y,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_WIDTH_PX,
  RULE_THICKNESS,
  RULE_TOP_Y,
  RULE_BOTTOM_Y,
  RULES_DRAW_START,
  RULES_DRAW_DURATION,
  PRIMARY_FADE_START,
  PRIMARY_FADE_DURATION,
  SECONDARY_FADE_START,
  SECONDARY_FADE_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
} from './constants';

export const defaultPart4PrecisionTradeoff07KeyInsightWallsProps = {};

export const Part4PrecisionTradeoff07KeyInsightWalls: React.FC = () => {
  const frame = useCurrentFrame();

  // Primary text fade + scale (frames 20-40)
  const primaryOpacity = interpolate(
    frame,
    [PRIMARY_FADE_START, PRIMARY_FADE_START + PRIMARY_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const primaryScale = interpolate(
    frame,
    [PRIMARY_FADE_START, PRIMARY_FADE_START + PRIMARY_FADE_DURATION],
    [0.97, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Secondary text fade (frames 50-70)
  const secondaryOpacity = interpolate(
    frame,
    [SECONDARY_FADE_START, SECONDARY_FADE_START + SECONDARY_FADE_DURATION],
    [0, SECONDARY_TEXT_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Global fade out (frames 100-120)
  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* Background gradient glow */}
      <BackgroundGradient
        leftColor={GRADIENT_LEFT_COLOR}
        rightColor={GRADIENT_RIGHT_COLOR}
        baseOpacity={GRADIENT_OPACITY}
        fadeInDuration={20}
      />

      {/* Upper horizontal rule */}
      <HorizontalRule
        y={RULE_TOP_Y}
        maxWidth={RULE_WIDTH_PX}
        color={RULE_COLOR}
        opacity={RULE_OPACITY}
        thickness={RULE_THICKNESS}
        drawStart={RULES_DRAW_START}
        drawDuration={RULES_DRAW_DURATION}
      />

      {/* Lower horizontal rule */}
      <HorizontalRule
        y={RULE_BOTTOM_Y}
        maxWidth={RULE_WIDTH_PX}
        color={RULE_COLOR}
        opacity={RULE_OPACITY}
        thickness={RULE_THICKNESS}
        drawStart={RULES_DRAW_START}
        drawDuration={RULES_DRAW_DURATION}
      />

      {/* Primary text: "More tests, less prompt." */}
      <div
        style={{
          position: 'absolute',
          top: PRIMARY_Y,
          left: 0,
          width: '100%',
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          transform: `translateY(-50%) scale(${primaryScale})`,
          opacity: primaryOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: PRIMARY_FONT_SIZE,
            fontWeight: PRIMARY_FONT_WEIGHT,
            color: PRIMARY_COLOR,
            whiteSpace: 'nowrap',
          }}
        >
          {PRIMARY_TEXT}
        </span>
      </div>

      {/* Glow pulse on primary text */}
      <Sequence from={PRIMARY_FADE_START} durationInFrames={GLOW_PULSE_DURATION + 10}>
        <GlowPulse
          text={PRIMARY_TEXT}
          fontSize={PRIMARY_FONT_SIZE}
          fontWeight={PRIMARY_FONT_WEIGHT}
          glowColor={GLOW_COLOR}
          glowOpacity={GLOW_OPACITY}
          glowBlur={GLOW_BLUR}
          pulseStart={10}
          pulseDuration={GLOW_PULSE_DURATION}
          y={PRIMARY_Y}
        />
      </Sequence>

      {/* Secondary text: "The walls do the precision work." */}
      <div
        style={{
          position: 'absolute',
          top: SECONDARY_Y,
          left: 0,
          width: '100%',
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          transform: 'translateY(-50%)',
          opacity: secondaryOpacity,
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, sans-serif',
            fontSize: SECONDARY_FONT_SIZE,
            fontWeight: SECONDARY_FONT_WEIGHT,
            color: SECONDARY_COLOR,
            whiteSpace: 'nowrap',
          }}
        >
          {SECONDARY_TEXT}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff07KeyInsightWalls;
