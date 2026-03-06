import React from "react";
import { AbsoluteFill, OffthreadVideo, staticFile, Sequence } from "remotion";
import { LeftPanel } from "./LeftPanel";
import { RightPanel } from "./RightPanel";
import { SplitLine } from "./SplitLine";
import { QuestionText } from "./QuestionText";
import { PanelLabels } from "./PanelLabels";
import { BG_COLOR, TOTAL_FRAMES } from "./constants";

export const defaultColdOpen08ClosingQuestionCardProps = {};

export const ColdOpen08ClosingQuestionCard: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/cold_open.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
        />
      </AbsoluteFill>

      {/* Split-screen overlay — 90 frames (3s at 30fps) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AbsoluteFill>
          <LeftPanel />
          <RightPanel />
          <SplitLine />
          <QuestionText />
          <PanelLabels />
        </AbsoluteFill>
      </Sequence>
    </AbsoluteFill>
  );
};

export default ColdOpen08ClosingQuestionCard;
