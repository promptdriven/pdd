import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";

import { BlueprintGrid } from "./BlueprintGrid";
import { TypewriterText } from "./TypewriterText";
import { HorizontalRule } from "./HorizontalRule";
import { TerminalLine } from "./TerminalLine";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  TITLE_TEXT,
  TITLE_COLOR,
  TITLE_FONT_SIZE,
  TITLE_FONT_WEIGHT,
  TITLE_LETTER_SPACING,
  TITLE_Y,
  RULE_Y,
  RULE_COLOR,
  RULE_OPACITY,
  RULE_WIDTH,
  CMD_Y,
  CMD_LINE_SPACING,
  CMD1_TEXT,
  CMD2_TEXT,
  CMD_COLOR_INSTALL,
  CMD_COLOR_UPDATE,
  URL_Y,
  URL_TEXT,
  URL_COLOR,
  URL_UNDERLINE_OPACITY,
  URL_FONT_SIZE,
  URL_FONT_WEIGHT,
  GRID_FADE_START,
  TITLE_TYPE_START,
  FRAMES_PER_CHAR,
  RULE_DRAW_START,
  RULE_DRAW_DURATION,
  CMD1_TYPE_START,
  CMD2_TYPE_START,
  URL_FADE_START,
  URL_FADE_DURATION,
} from "./constants";

export const defaultClosing07FinalTitleCardProps = {};

/**
 * URL text with subtle underline, fades in via parent Sequence timing.
 */
const URLText: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, URL_FADE_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        top: URL_Y,
        left: 0,
        right: 0,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: URL_FONT_SIZE,
          fontWeight: URL_FONT_WEIGHT,
          color: URL_COLOR,
          textDecoration: "none",
          paddingBottom: 3,
          borderBottom: "none",
          boxShadow: `inset 0 -1px 0 0 rgba(100, 116, 139, ${URL_UNDERLINE_OPACITY})`,
        }}
      >
        {URL_TEXT}
      </span>
    </div>
  );
};

/**
 * Background fade from true black — controls the overall opacity of the
 * background so it fades up from absolute black at the very start.
 */
const BackgroundFade: React.FC<{ children: React.ReactNode }> = ({
  children,
}) => {
  const frame = useCurrentFrame();
  const bgOpacity = interpolate(frame, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill style={{ opacity: bgOpacity }}>
      {children}
    </AbsoluteFill>
  );
};

export const Closing07FinalTitleCard: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Background with faint blueprint grid — fades up from black */}
      <Sequence from={GRID_FADE_START} durationInFrames={TOTAL_FRAMES}>
        <BackgroundFade>
          <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
            <BlueprintGrid />
          </AbsoluteFill>
        </BackgroundFade>
      </Sequence>

      {/* Title — types in character by character */}
      <Sequence
        from={TITLE_TYPE_START}
        durationInFrames={TOTAL_FRAMES - TITLE_TYPE_START}
      >
        <TypewriterText
          text={TITLE_TEXT}
          fontSize={TITLE_FONT_SIZE}
          fontWeight={TITLE_FONT_WEIGHT}
          color={TITLE_COLOR}
          letterSpacing={TITLE_LETTER_SPACING}
          framesPerChar={FRAMES_PER_CHAR}
          y={TITLE_Y}
        />
      </Sequence>

      {/* Horizontal rule — draws from center outward */}
      <Sequence
        from={RULE_DRAW_START}
        durationInFrames={TOTAL_FRAMES - RULE_DRAW_START}
      >
        <HorizontalRule
          y={RULE_Y}
          width={RULE_WIDTH}
          color={RULE_COLOR}
          ruleOpacity={RULE_OPACITY}
          drawFrames={RULE_DRAW_DURATION}
        />
      </Sequence>

      {/* First command: $ uv tool install pdd-cli */}
      <Sequence
        from={CMD1_TYPE_START}
        durationInFrames={TOTAL_FRAMES - CMD1_TYPE_START}
      >
        <TerminalLine
          command={CMD1_TEXT}
          color={CMD_COLOR_INSTALL}
          y={CMD_Y}
          framesPerChar={FRAMES_PER_CHAR}
        />
      </Sequence>

      {/* Second command: $ pdd update your_module.py (with pulse) */}
      <Sequence
        from={CMD2_TYPE_START}
        durationInFrames={TOTAL_FRAMES - CMD2_TYPE_START}
      >
        <TerminalLine
          command={CMD2_TEXT}
          color={CMD_COLOR_UPDATE}
          y={CMD_Y + CMD_LINE_SPACING}
          framesPerChar={FRAMES_PER_CHAR}
          pulseOnHold
          pulseStartFrame={120 - CMD2_TYPE_START}
        />
      </Sequence>

      {/* URL — fades in below commands */}
      <Sequence
        from={URL_FADE_START}
        durationInFrames={TOTAL_FRAMES - URL_FADE_START}
      >
        <URLText />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Closing07FinalTitleCard;
