import React from 'react';
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from 'remotion';
import {
  CANVAS,
  COLORS,
  TITLE,
  SUBTITLE,
  TERMINAL,
  QUESTION,
  TIMING,
} from './constants';
import { CodeUnderlay } from './CodeUnderlay';
import { TitleGlow } from './TitleGlow';
import { HorizontalRule } from './HorizontalRule';

export const defaultColdOpen07PddTitleCardProps = {};

export const ColdOpen07PddTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Phase 1: Question fade-out (frames 0–20) ──
  const questionOpacity = interpolate(
    frame,
    [TIMING.QUESTION_FADE_START, TIMING.QUESTION_FADE_START + TIMING.QUESTION_FADE_DURATION],
    [0.9, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Phase 2: "Prompt-Driven" fade-in + slide-up (frames 20–45) ──
  const line1LocalFrame = Math.max(0, frame - TIMING.TITLE_LINE1_START);
  const line1Opacity = interpolate(
    line1LocalFrame,
    [0, TIMING.TITLE_LINE1_DURATION],
    [0, TITLE.OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );
  const line1TranslateY = interpolate(
    line1LocalFrame,
    [0, TIMING.TITLE_LINE1_DURATION],
    [TIMING.TITLE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Phase 4: "Development" fade-in + slide-up (frames 60–85) ──
  const line2LocalFrame = Math.max(0, frame - TIMING.TITLE_LINE2_START);
  const line2Opacity = interpolate(
    line2LocalFrame,
    [0, TIMING.TITLE_LINE2_DURATION],
    [0, TITLE.OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );
  const line2TranslateY = interpolate(
    line2LocalFrame,
    [0, TIMING.TITLE_LINE2_DURATION],
    [TIMING.TITLE_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Phase 5: Subtitle fade-in (frames 80–100) ──
  const subtitleLocalFrame = Math.max(0, frame - TIMING.SUBTITLE_START);
  const subtitleOpacity = interpolate(
    subtitleLocalFrame,
    [0, TIMING.SUBTITLE_DURATION],
    [0, SUBTITLE.OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Phase 5: Terminal breadcrumb fade-in (frames 80–100) ──
  const terminalLocalFrame = Math.max(0, frame - TIMING.TERMINAL_START);
  const terminalOpacity = interpolate(
    terminalLocalFrame,
    [0, TIMING.TERMINAL_DURATION],
    [0, TERMINAL.OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.BACKGROUND,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Dimmed code underlay */}
      <CodeUnderlay />

      {/* Previous question text fading out */}
      {frame < TIMING.QUESTION_FADE_END && (
        <div
          style={{
            position: 'absolute',
            top: QUESTION.Y - QUESTION.FONT_SIZE / 2,
            left: 0,
            width: CANVAS.WIDTH,
            textAlign: 'center',
            fontFamily: QUESTION.FONT_FAMILY,
            fontSize: QUESTION.FONT_SIZE,
            fontWeight: QUESTION.FONT_WEIGHT,
            color: COLORS.QUESTION_TEXT,
            opacity: questionOpacity,
            userSelect: 'none',
          }}
        >
          {QUESTION.TEXT}
        </div>
      )}

      {/* Glow layers behind title text */}
      <TitleGlow y={TITLE.Y_LINE1} text={TITLE.LINE1} startFrame={TIMING.TITLE_LINE1_START} />
      <TitleGlow y={TITLE.Y_LINE2} text={TITLE.LINE2} startFrame={TIMING.TITLE_LINE2_START} />

      {/* Title Line 1: "Prompt-Driven" */}
      {frame >= TIMING.TITLE_LINE1_START && (
        <div
          style={{
            position: 'absolute',
            top: TITLE.Y_LINE1 - TITLE.FONT_SIZE / 2,
            left: 0,
            width: CANVAS.WIDTH,
            textAlign: 'center',
            fontFamily: TITLE.FONT_FAMILY,
            fontSize: TITLE.FONT_SIZE,
            fontWeight: TITLE.FONT_WEIGHT,
            color: COLORS.TITLE,
            opacity: line1Opacity,
            transform: `translateY(${line1TranslateY}px)`,
            userSelect: 'none',
          }}
        >
          {TITLE.LINE1}
        </div>
      )}

      {/* Horizontal rule */}
      <HorizontalRule />

      {/* Title Line 2: "Development" */}
      {frame >= TIMING.TITLE_LINE2_START && (
        <div
          style={{
            position: 'absolute',
            top: TITLE.Y_LINE2 - TITLE.FONT_SIZE / 2,
            left: 0,
            width: CANVAS.WIDTH,
            textAlign: 'center',
            fontFamily: TITLE.FONT_FAMILY,
            fontSize: TITLE.FONT_SIZE,
            fontWeight: TITLE.FONT_WEIGHT,
            color: COLORS.TITLE,
            opacity: line2Opacity,
            transform: `translateY(${line2TranslateY}px)`,
            userSelect: 'none',
          }}
        >
          {TITLE.LINE2}
        </div>
      )}

      {/* Subtitle */}
      {frame >= TIMING.SUBTITLE_START && (
        <div
          style={{
            position: 'absolute',
            top: SUBTITLE.Y - SUBTITLE.FONT_SIZE / 2,
            left: 0,
            width: CANVAS.WIDTH,
            textAlign: 'center',
            fontFamily: SUBTITLE.FONT_FAMILY,
            fontSize: SUBTITLE.FONT_SIZE,
            fontWeight: SUBTITLE.FONT_WEIGHT,
            fontStyle: 'italic',
            color: COLORS.SUBTITLE,
            opacity: subtitleOpacity,
            userSelect: 'none',
          }}
        >
          {SUBTITLE.TEXT}
        </div>
      )}

      {/* Terminal breadcrumb – bottom-right */}
      {frame >= TIMING.TERMINAL_START && (
        <div
          style={{
            position: 'absolute',
            top: TERMINAL.Y,
            left: TERMINAL.X,
            fontFamily: TERMINAL.FONT_FAMILY,
            fontSize: TERMINAL.FONT_SIZE,
            color: COLORS.TITLE,
            opacity: terminalOpacity,
            whiteSpace: 'nowrap',
            userSelect: 'none',
            transform: 'translateX(-100%)',
          }}
        >
          {TERMINAL.TEXT}
        </div>
      )}
    </AbsoluteFill>
  );
};

export default ColdOpen07PddTitleCard;
