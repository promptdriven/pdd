import React from "react";
import { AbsoluteFill } from "remotion";
import { BG_COLOR, CANVAS_WIDTH, CANVAS_HEIGHT } from "./constants";
import { PromptFileDisplay } from "./PromptFileDisplay";
import { FlowArrow } from "./FlowArrow";
import { TerminalPanel } from "./TerminalPanel";

export const defaultColdOpen08PromptFileGenerateProps = {};

export const ColdOpen08PromptFileGenerate: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
        fontFamily: "sans-serif",
      }}
    >
      {/* Prompt file — left side, visible from frame 0 */}
      <PromptFileDisplay />

      {/* Flow arrow — center, appears at frame 20 */}
      <FlowArrow />

      {/* Terminal output — right side, appears at frame 25 */}
      <TerminalPanel />
    </AbsoluteFill>
  );
};

export default ColdOpen08PromptFileGenerate;
