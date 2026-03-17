import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { useVisualMediaSrc } from "../_shared/visual-runtime";
import "../_shared/load-inter-font";
import SplitPanel from "./SplitPanel";
import {
  BG_COLOR,
  FONT_MONO,
  HEIGHT,
  LEFT_ACCENT,
  LEFT_COLOR_GRADE,
  LEFT_PANEL_WIDTH,
  LEFT_VIGNETTE_EDGE,
  RIGHT_ACCENT,
  RIGHT_COLOR_GRADE,
  RIGHT_PANEL_WIDTH,
  RIGHT_VIGNETTE_EDGE,
  RIGHT_PANEL_X,
  SPLIT_LINE_COLOR,
  SPLIT_LINE_DRAW_DURATION,
  SPLIT_LINE_DRAW_START,
  SPLIT_LINE_OPACITY,
  SPLIT_LINE_WIDTH,
  SPLIT_X,
  TERMINAL_PHASE1_START,
  TERMINAL_PHASE2_START,
  TERMINAL_PHASE3_START,
  WIDTH,
} from "./constants";

export const defaultClosing01SockCallbackSplitProps = {};

/**
 * Section 7.1: Sock Callback — The Final Discard
 *
 * Vertical split screen: LEFT = sock discard (warm amber),
 * RIGHT = code regeneration (cool blue). Both panels show Veo clips
 * with synchronized cost labels appearing at frame 160.
 */
export const Closing01SockCallbackSplit: React.FC = () => {
  const frame = useCurrentFrame();

  // Resolve Veo media via visual-runtime hooks
  const leftSrc = useVisualMediaSrc("leftSrc", staticFile("veo/sock_final_discard.mp4"));
  const rightSrc = useVisualMediaSrc("rightSrc", staticFile("veo/darning_split_screen.mp4"));

  // Split line animation: draws from center outward
  const splitLineProgress = interpolate(
    frame,
    [SPLIT_LINE_DRAW_START, SPLIT_LINE_DRAW_START + SPLIT_LINE_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const splitLineHeight = splitLineProgress * HEIGHT;
  const splitLineTop = (HEIGHT - splitLineHeight) / 2;

  // Terminal snippet progressive reveal
  const terminalText = buildTerminalText(frame);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
      }}
    >
      {/* Left panel — Sock discard */}
      <SplitPanel
        x={0}
        width={LEFT_PANEL_WIDTH}
        headerText="DISCARD"
        accentColor={LEFT_ACCENT}
        colorGradeColor={LEFT_COLOR_GRADE}
        colorGradeOpacity={0.03}
        vignetteEdge={LEFT_VIGNETTE_EDGE}
        videoSrc={leftSrc}
        costLabel="$2"
        costSubLabel="new pair"
      />

      {/* Split divider */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - SPLIT_LINE_WIDTH / 2,
          top: splitLineTop,
          width: SPLIT_LINE_WIDTH,
          height: splitLineHeight,
          backgroundColor: SPLIT_LINE_COLOR,
          opacity: SPLIT_LINE_OPACITY,
        }}
      />

      {/* Right panel — Code regeneration */}
      <SplitPanel
        x={RIGHT_PANEL_X}
        width={RIGHT_PANEL_WIDTH}
        headerText="REGENERATE"
        accentColor={RIGHT_ACCENT}
        colorGradeColor={RIGHT_COLOR_GRADE}
        colorGradeOpacity={0.02}
        vignetteEdge={RIGHT_VIGNETTE_EDGE}
        videoSrc={rightSrc}
        costLabel="~30s"
        costSubLabel="regenerated"
      >
        {/* Terminal snippet in bottom-right */}
        <div
          style={{
            position: "absolute",
            bottom: 60,
            right: 40,
            fontFamily: FONT_MONO,
            fontSize: 10,
            color: RIGHT_ACCENT,
            opacity: terminalText ? 0.25 : 0,
            whiteSpace: "nowrap",
          }}
        >
          {terminalText}
        </div>
      </SplitPanel>
    </AbsoluteFill>
  );
};

/** Build progressive terminal text based on current frame */
function buildTerminalText(frame: number): string {
  if (frame < TERMINAL_PHASE1_START) return "";
  if (frame < TERMINAL_PHASE2_START) return "pdd bug";
  if (frame < TERMINAL_PHASE3_START) return "pdd bug → pdd fix";
  return "pdd bug → pdd fix → ✓";
}

export default Closing01SockCallbackSplit;
