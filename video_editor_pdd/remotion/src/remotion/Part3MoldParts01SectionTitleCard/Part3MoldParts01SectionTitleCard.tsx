import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';

import { BlueprintGrid } from './BlueprintGrid';
import { GhostMold } from './GhostMold';
import { TypeWriter } from './TypeWriter';
import {
  WIDTH,
  HEIGHT,
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  TITLE_COLOR,
  SECTION_LABEL_COLOR,
  SECTION_LABEL_OPACITY,
  RULE_COLOR,
  RULE_OPACITY,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  SECTION_LABEL_FONT_SIZE,
  SECTION_LABEL_FONT_WEIGHT,
  SECTION_LABEL_LETTER_SPACING,
  SECTION_LABEL_Y,
  TITLE_LINE1_Y,
  RULE_Y,
  TITLE_LINE2_Y,
  TITLE_LINE2_OFFSET_X,
  RULE_WIDTH,
  FRAME_BG_FADE_START,
  FRAME_BG_FADE_END,
  FRAME_LABEL_FADE_START,
  FRAME_LABEL_FADE_DURATION,
  FRAME_GHOST_DRAW_START,
  FRAME_GHOST_DRAW_DURATION,
  FRAME_TYPEWRITER_START,
  CHARS_PER_FRAME,
  FRAME_RULE_DRAW_START,
  FRAME_RULE_DRAW_DURATION,
  FRAME_LINE2_FADE_START,
  FRAME_LINE2_FADE_DURATION,
  FRAME_LINE2_SLIDE_DISTANCE,
  FRAME_FADEOUT_START,
  FRAME_FADEOUT_DURATION,
  SECTION_LABEL_TEXT,
  TITLE_LINE1_TEXT,
  TITLE_LINE2_TEXT,
} from './constants';

export const defaultPart3MoldParts01SectionTitleCardProps = {};

export const Part3MoldParts01SectionTitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Background fade in (frames 0-15) ──
  const bgOpacity = interpolate(
    frame,
    [FRAME_BG_FADE_START, FRAME_BG_FADE_END],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // ── Section label "PART 3" fade (frames 15-35) ──
  const labelOpacity = interpolate(
    frame,
    [FRAME_LABEL_FADE_START, FRAME_LABEL_FADE_START + FRAME_LABEL_FADE_DURATION],
    [0, SECTION_LABEL_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Ghost mold draw progress (frames 15-45) ──
  const ghostDrawProgress = interpolate(
    frame,
    [FRAME_GHOST_DRAW_START, FRAME_GHOST_DRAW_START + FRAME_GHOST_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // ── Typewriter: "THE MOLD HAS" (frames 40+, 2 frames per char) ──
  const typewriterFrame = Math.max(0, frame - FRAME_TYPEWRITER_START);
  const charsRevealed = typewriterFrame / CHARS_PER_FRAME;

  // ── Horizontal rule draw from center (frames 60-70) ──
  const ruleProgress = interpolate(
    frame,
    [FRAME_RULE_DRAW_START, FRAME_RULE_DRAW_START + FRAME_RULE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );
  const ruleCurrentWidth = RULE_WIDTH * ruleProgress;

  // ── "THREE PARTS" fade + slide (frames 70-90) ──
  const line2Opacity = interpolate(
    frame,
    [FRAME_LINE2_FADE_START, FRAME_LINE2_FADE_START + FRAME_LINE2_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );
  const line2SlideY = interpolate(
    frame,
    [FRAME_LINE2_FADE_START, FRAME_LINE2_FADE_START + FRAME_LINE2_FADE_DURATION],
    [FRAME_LINE2_SLIDE_DISTANCE, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // ── Final fade out (frames 1260-1320) ──
  const fadeOutOpacity = interpolate(
    frame,
    [FRAME_FADEOUT_START, FRAME_FADEOUT_START + FRAME_FADEOUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  // Combine master opacity: fade-in * fade-out
  const masterOpacity = bgOpacity * fadeOutOpacity;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Overall opacity wrapper for fade-in/fade-out */}
      <AbsoluteFill style={{ opacity: masterOpacity }}>
        {/* Blueprint grid */}
        <BlueprintGrid
          spacing={GRID_SPACING}
          color={GRID_COLOR}
          opacity={GRID_OPACITY}
          width={WIDTH}
          height={HEIGHT}
        />

        {/* Ghost mold cross-section */}
        <Sequence from={FRAME_GHOST_DRAW_START}>
          <GhostMold
            drawProgress={ghostDrawProgress}
            frame={frame}
          />
        </Sequence>

        {/* Section label: "PART 3" */}
        <div
          style={{
            position: 'absolute',
            top: SECTION_LABEL_Y,
            left: 0,
            width: WIDTH,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: SECTION_LABEL_FONT_SIZE,
            fontWeight: SECTION_LABEL_FONT_WEIGHT,
            color: SECTION_LABEL_COLOR,
            letterSpacing: SECTION_LABEL_LETTER_SPACING,
            opacity: labelOpacity,
          }}
        >
          {SECTION_LABEL_TEXT}
        </div>

        {/* Title line 1: "THE MOLD HAS" (typewriter) */}
        <div
          style={{
            position: 'absolute',
            top: TITLE_LINE1_Y,
            left: 0,
            width: WIDTH,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            lineHeight: 1,
          }}
        >
          <TypeWriter
            text={TITLE_LINE1_TEXT}
            charsRevealed={charsRevealed}
          />
        </div>

        {/* Horizontal rule — draws from center outward */}
        <div
          style={{
            position: 'absolute',
            top: RULE_Y,
            left: (WIDTH - ruleCurrentWidth) / 2,
            width: ruleCurrentWidth,
            height: 2,
            backgroundColor: RULE_COLOR,
            opacity: RULE_OPACITY,
          }}
        />

        {/* Title line 2: "THREE PARTS" (fade + slide up) */}
        <div
          style={{
            position: 'absolute',
            top: TITLE_LINE2_Y + line2SlideY,
            left: TITLE_LINE2_OFFSET_X,
            width: WIDTH,
            textAlign: 'center',
            fontFamily: 'Inter, sans-serif',
            fontSize: TITLE_FONT_SIZE,
            fontWeight: TITLE_FONT_WEIGHT,
            color: TITLE_COLOR,
            opacity: line2Opacity,
            lineHeight: 1,
          }}
        >
          {TITLE_LINE2_TEXT}
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3MoldParts01SectionTitleCard;
