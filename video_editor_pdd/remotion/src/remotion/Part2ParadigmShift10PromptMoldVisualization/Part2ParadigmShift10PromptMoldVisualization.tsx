import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { TriadBox } from "./TriadBox";
import { ArrowConnector } from "./ArrowConnector";
import { SynthesisLine } from "./SynthesisLine";
import {
  BG_COLOR,
  PANEL_X,
  PANEL_Y,
  PANEL_W,
  PANEL_H,
  PANEL_BORDER_RADIUS,
  PANEL_BG,
  PANEL_BLUR,
  PANEL_FADE_START,
  PANEL_FADE_END,
  PROMPT_CENTER_X,
  PROMPT_CENTER_Y,
  PROMPT_BORDER_COLOR,
  PROMPT_FILL,
  PROMPT_ICON_COLOR,
  PROMPT_GLOW,
  CODE_CENTER_X,
  CODE_CENTER_Y,
  CODE_BORDER_COLOR,
  CODE_FILL,
  CODE_ICON_COLOR,
  CODE_GLOW,
  TESTS_CENTER_X,
  TESTS_CENTER_Y,
  TESTS_BORDER_COLOR,
  TESTS_FILL,
  TESTS_ICON_COLOR,
  TESTS_GLOW,
  BOX1_ENTER,
  BOX2_ENTER,
  BOX3_ENTER,
  ARROW1_DRAW_START,
  ARROW1_DRAW_END,
  ARROW1_FROM_X,
  ARROW1_TO_X,
  ARROW1_Y,
  ARROW2_DRAW_START,
  ARROW2_DRAW_END,
  ARROW2_FROM_X,
  ARROW2_TO_X,
  ARROW2_Y,
  SYNTHESIS_PHRASE1_HIGHLIGHT,
  SYNTHESIS_PHRASE2_HIGHLIGHT,
  SYNTHESIS_PHRASE3_HIGHLIGHT,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart2ParadigmShift10PromptMoldVisualizationProps = {};

export const Part2ParadigmShift10PromptMoldVisualization: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Backing panel opacity ---
  const panelFadeIn = interpolate(
    frame,
    [PANEL_FADE_START, PANEL_FADE_END],
    [0, 0.8],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const panelFadeOut = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );
  const panelOpacity = panelFadeIn * panelFadeOut;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Backing panel */}
      <div
        style={{
          position: "absolute",
          left: PANEL_X,
          top: PANEL_Y,
          width: PANEL_W,
          height: PANEL_H,
          borderRadius: PANEL_BORDER_RADIUS,
          background: PANEL_BG,
          backdropFilter: `blur(${PANEL_BLUR}px)`,
          opacity: panelOpacity,
        }}
      />

      {/* Box 1 — PROMPT */}
      <TriadBox
        centerX={PROMPT_CENTER_X}
        centerY={PROMPT_CENTER_Y}
        borderColor={PROMPT_BORDER_COLOR}
        fill={PROMPT_FILL}
        iconColor={PROMPT_ICON_COLOR}
        glowColor={PROMPT_GLOW}
        label="PROMPT"
        subtitle="your mold"
        icon="document"
        entryFrame={BOX1_ENTER}
        pulseHighlightFrame={SYNTHESIS_PHRASE1_HIGHLIGHT}
      />

      {/* Arrow 1: PROMPT → CODE */}
      <ArrowConnector
        fromX={ARROW1_FROM_X}
        toX={ARROW1_TO_X}
        y={ARROW1_Y}
        label="generates"
        drawStartFrame={ARROW1_DRAW_START}
        drawEndFrame={ARROW1_DRAW_END}
      />

      {/* Box 2 — CODE */}
      <TriadBox
        centerX={CODE_CENTER_X}
        centerY={CODE_CENTER_Y}
        borderColor={CODE_BORDER_COLOR}
        fill={CODE_FILL}
        iconColor={CODE_ICON_COLOR}
        glowColor={CODE_GLOW}
        label="CODE"
        subtitle="is plastic"
        icon="code"
        entryFrame={BOX2_ENTER}
        pulseHighlightFrame={SYNTHESIS_PHRASE2_HIGHLIGHT}
      />

      {/* Arrow 2: CODE ↔ TESTS */}
      <ArrowConnector
        fromX={ARROW2_FROM_X}
        toX={ARROW2_TO_X}
        y={ARROW2_Y}
        label="validates"
        bidirectional
        drawStartFrame={ARROW2_DRAW_START}
        drawEndFrame={ARROW2_DRAW_END}
      />

      {/* Box 3 — TESTS */}
      <TriadBox
        centerX={TESTS_CENTER_X}
        centerY={TESTS_CENTER_Y}
        borderColor={TESTS_BORDER_COLOR}
        fill={TESTS_FILL}
        iconColor={TESTS_ICON_COLOR}
        glowColor={TESTS_GLOW}
        label="TESTS"
        subtitle="lock behavior"
        icon="shield"
        entryFrame={BOX3_ENTER}
        pulseHighlightFrame={SYNTHESIS_PHRASE3_HIGHLIGHT}
      />

      {/* Synthesis line */}
      <SynthesisLine />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift10PromptMoldVisualization;
