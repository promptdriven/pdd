/**
 * Part4PrecisionTradeoff07KeyInsightWalls
 *
 * A typographic emphasis card delivering the core takeaway:
 *   "More tests, less prompt. The walls do the precision work."
 *
 * 120 frames @ 30fps (~4s).
 * Clean centered text on a dark navy-black background with a dual-radial
 * gradient (blue-left / amber-right) and decorative horizontal rules
 * that draw outward from center.
 */
import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';

import {
  WIDTH,
  BG_COLOR,
  PRIMARY_TEXT_COLOR,
  SECONDARY_TEXT_COLOR,
  SECONDARY_TEXT_OPACITY,
  GRADIENT_LEFT_COLOR,
  GRADIENT_RIGHT_COLOR,
  GRADIENT_OPACITY,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_TOP_Y,
  RULE_BOTTOM_Y,
  RULE_WIDTH,
  RULE_THICKNESS,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  PRIMARY_TEXT_Y,
  SECONDARY_TEXT_Y,
  FONT_FAMILY,
  PRIMARY_FONT_SIZE,
  PRIMARY_FONT_WEIGHT,
  SECONDARY_FONT_SIZE,
  SECONDARY_FONT_WEIGHT,
  PRIMARY_TEXT_START,
  PRIMARY_TEXT_FADE_DURATION,
  PRIMARY_SCALE_FROM,
  PRIMARY_SCALE_TO,
  GLOW_COLOR,
  GLOW_OPACITY,
  GLOW_BLUR_PX,
  GLOW_PULSE_DELAY,
  GLOW_PULSE_DURATION,
  SECONDARY_TEXT_START,
  SECONDARY_TEXT_FADE_DURATION,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  GRADIENT_FADE_START,
  GRADIENT_FADE_END,
  PRIMARY_TEXT,
  SECONDARY_TEXT,
} from './constants';

import DrawLine from './DrawLine';
import GlowText from './GlowText';

// ---------------------------------------------------------------------------
// Default props (required by export contract)
// ---------------------------------------------------------------------------
export const defaultPart4PrecisionTradeoff07KeyInsightWallsProps = {};

// ---------------------------------------------------------------------------
// Secondary text sub-section (simple fade-in + fade-out)
// ---------------------------------------------------------------------------
const SecondaryLine: React.FC = () => {
  const frame = useCurrentFrame();

  const fadeIn = interpolate(
    frame,
    [SECONDARY_TEXT_START, SECONDARY_TEXT_START + SECONDARY_TEXT_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: SECONDARY_TEXT_Y,
        left: 0,
        width: WIDTH,
        display: 'flex',
        justifyContent: 'center',
        transform: 'translateY(-50%)',
        opacity: fadeIn * fadeOut,
      }}
    >
      <span
        style={{
          fontFamily: FONT_FAMILY,
          fontSize: SECONDARY_FONT_SIZE,
          fontWeight: SECONDARY_FONT_WEIGHT,
          color: SECONDARY_TEXT_COLOR,
          opacity: SECONDARY_TEXT_OPACITY,
          textAlign: 'center',
          whiteSpace: 'nowrap',
        }}
      >
        {SECONDARY_TEXT}
      </span>
    </div>
  );
};

// ---------------------------------------------------------------------------
// Background gradient (radial blue-left + amber-right)
// ---------------------------------------------------------------------------
const BackgroundGradient: React.FC = () => {
  const frame = useCurrentFrame();

  const gradientOpacity = interpolate(
    frame,
    [GRADIENT_FADE_START, GRADIENT_FADE_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  const combined = gradientOpacity * fadeOut;

  return (
    <>
      {/* Blue radial on the left */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: `radial-gradient(ellipse at 25% 50%, ${GRADIENT_LEFT_COLOR} 0%, transparent 70%)`,
          opacity: GRADIENT_OPACITY * combined,
        }}
      />
      {/* Amber radial on the right */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          background: `radial-gradient(ellipse at 75% 50%, ${GRADIENT_RIGHT_COLOR} 0%, transparent 70%)`,
          opacity: GRADIENT_OPACITY * combined,
        }}
      />
    </>
  );
};

// ---------------------------------------------------------------------------
// Main component
// ---------------------------------------------------------------------------
export const Part4PrecisionTradeoff07KeyInsightWalls: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      {/* Background gradient glow */}
      <BackgroundGradient />

      {/* Upper decorative rule */}
      <DrawLine
        y={RULE_TOP_Y}
        lineWidth={RULE_WIDTH}
        thickness={RULE_THICKNESS}
        color={RULE_COLOR}
        lineOpacity={RULE_OPACITY}
        startFrame={RULE_DRAW_START}
        drawDuration={RULE_DRAW_DURATION}
        fadeOutStart={FADE_OUT_START}
        fadeOutDuration={FADE_OUT_DURATION}
        canvasWidth={WIDTH}
      />

      {/* Primary text with glow pulse */}
      <GlowText
        text={PRIMARY_TEXT}
        fontSize={PRIMARY_FONT_SIZE}
        fontWeight={PRIMARY_FONT_WEIGHT}
        fontFamily={FONT_FAMILY}
        color={PRIMARY_TEXT_COLOR}
        y={PRIMARY_TEXT_Y}
        canvasWidth={WIDTH}
        fadeInStart={PRIMARY_TEXT_START}
        fadeInDuration={PRIMARY_TEXT_FADE_DURATION}
        scaleFrom={PRIMARY_SCALE_FROM}
        scaleTo={PRIMARY_SCALE_TO}
        glowColor={GLOW_COLOR}
        glowMaxOpacity={GLOW_OPACITY}
        glowBlur={GLOW_BLUR_PX}
        glowDelay={GLOW_PULSE_DELAY}
        glowDuration={GLOW_PULSE_DURATION}
        fadeOutStart={FADE_OUT_START}
        fadeOutDuration={FADE_OUT_DURATION}
      />

      {/* Secondary text */}
      <SecondaryLine />

      {/* Lower decorative rule */}
      <DrawLine
        y={RULE_BOTTOM_Y}
        lineWidth={RULE_WIDTH}
        thickness={RULE_THICKNESS}
        color={RULE_COLOR}
        lineOpacity={RULE_OPACITY}
        startFrame={RULE_DRAW_START}
        drawDuration={RULE_DRAW_DURATION}
        fadeOutStart={FADE_OUT_START}
        fadeOutDuration={FADE_OUT_DURATION}
        canvasWidth={WIDTH}
      />
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff07KeyInsightWalls;
