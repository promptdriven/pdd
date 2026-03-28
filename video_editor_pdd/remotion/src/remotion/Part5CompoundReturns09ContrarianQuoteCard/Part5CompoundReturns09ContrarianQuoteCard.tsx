import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  BG_COLOR,
  QUOTE_MARK_COLOR,
  QUOTE_TEXT_COLOR,
  RULE_COLOR,
  ATTRIBUTION_COLOR,
  ACCENT_GLOW_COLOR,
  QUOTE_MARK_OPACITY,
  RULE_OPACITY,
  ATTRIBUTION_OPACITY,
  ACCENT_GLOW_OPACITY,
  QUOTE_MARK_SIZE,
  QUOTE_TEXT_SIZE,
  ATTRIBUTION_SIZE,
  QUOTE_MARK_X,
  QUOTE_MARK_Y,
  QUOTE_CENTER_X,
  QUOTE_LINE1_Y,
  QUOTE_LINE2_Y,
  QUOTE_LINE3_Y,
  RULE_Y,
  RULE_HALF_WIDTH,
  ATTRIBUTION_Y,
  GLOW_RADIUS,
  QUOTE_MARK_START,
  QUOTE_MARK_FADE_DURATION,
  LINE1_START,
  LINE2_START,
  LINE3_START,
  GLOW_START,
  GLOW_FADE_DURATION,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  ATTRIBUTION_START,
  ATTRIBUTION_FADE_DURATION,
  FADEOUT_START,
  FADEOUT_DURATION,
  CHAR_DELAY_FRAMES,
  QUOTE_LINE_1,
  QUOTE_LINE_2,
  QUOTE_LINE_3,
  ATTRIBUTION_TEXT,
} from './constants';
import { TypewriterText } from './TypewriterText';
import { HorizontalRule } from './HorizontalRule';
import { RadialGlow } from './RadialGlow';

export const defaultPart5CompoundReturns09ContrarianQuoteCardProps = {};

export const Part5CompoundReturns09ContrarianQuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade-out at the end
  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_START + FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Opening quotation mark fade-in
  const quoteMarkOpacity = interpolate(
    frame,
    [QUOTE_MARK_START, QUOTE_MARK_START + QUOTE_MARK_FADE_DURATION],
    [0, QUOTE_MARK_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Attribution fade-in
  const attributionOpacity = interpolate(
    frame,
    [ATTRIBUTION_START, ATTRIBUTION_START + ATTRIBUTION_FADE_DURATION],
    [0, ATTRIBUTION_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: globalOpacity,
        fontFamily: 'Inter, sans-serif',
      }}
    >
      {/* Decorative opening quotation mark */}
      <div
        style={{
          position: 'absolute',
          left: QUOTE_MARK_X,
          top: QUOTE_MARK_Y,
          fontSize: QUOTE_MARK_SIZE,
          fontWeight: 700,
          color: QUOTE_MARK_COLOR,
          opacity: quoteMarkOpacity,
          lineHeight: 1,
          fontFamily: 'Inter, sans-serif',
        }}
      >
        {'\u201C'}
      </div>

      {/* Quote line 1 */}
      <TypewriterText
        text={QUOTE_LINE_1}
        startFrame={LINE1_START}
        charDelayFrames={CHAR_DELAY_FRAMES}
        fontSize={QUOTE_TEXT_SIZE}
        fontWeight={400}
        color={QUOTE_TEXT_COLOR}
        centerX={QUOTE_CENTER_X}
        centerY={QUOTE_LINE1_Y}
      />

      {/* Quote line 2 */}
      <TypewriterText
        text={QUOTE_LINE_2}
        startFrame={LINE2_START}
        charDelayFrames={CHAR_DELAY_FRAMES}
        fontSize={QUOTE_TEXT_SIZE}
        fontWeight={400}
        color={QUOTE_TEXT_COLOR}
        centerX={QUOTE_CENTER_X}
        centerY={QUOTE_LINE2_Y}
      />

      {/* Quote line 3 — italic with amber glow */}
      <RadialGlow
        startFrame={GLOW_START}
        fadeDuration={GLOW_FADE_DURATION}
        centerX={QUOTE_CENTER_X}
        centerY={QUOTE_LINE3_Y + 16}
        radius={GLOW_RADIUS}
        color={ACCENT_GLOW_COLOR}
        glowOpacity={ACCENT_GLOW_OPACITY}
      />
      <TypewriterText
        text={QUOTE_LINE_3}
        startFrame={LINE3_START}
        charDelayFrames={CHAR_DELAY_FRAMES}
        fontSize={QUOTE_TEXT_SIZE}
        fontWeight={400}
        fontStyle="italic"
        color={QUOTE_TEXT_COLOR}
        centerX={QUOTE_CENTER_X}
        centerY={QUOTE_LINE3_Y}
      />

      {/* Horizontal rule */}
      <HorizontalRule
        startFrame={RULE_DRAW_START}
        drawDuration={RULE_DRAW_DURATION}
        centerX={QUOTE_CENTER_X}
        centerY={RULE_Y}
        halfWidth={RULE_HALF_WIDTH}
        color={RULE_COLOR}
        ruleOpacity={RULE_OPACITY}
      />

      {/* Attribution */}
      <div
        style={{
          position: 'absolute',
          left: QUOTE_CENTER_X,
          top: ATTRIBUTION_Y,
          transform: 'translateX(-50%)',
          fontSize: ATTRIBUTION_SIZE,
          fontWeight: 400,
          color: ATTRIBUTION_COLOR,
          opacity: attributionOpacity,
          whiteSpace: 'nowrap',
          fontFamily: 'Inter, sans-serif',
        }}
      >
        {ATTRIBUTION_TEXT}
      </div>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns09ContrarianQuoteCard;
