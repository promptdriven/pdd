import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import "../_shared/load-inter-font";
import BackgroundChart from "./BackgroundChart";
import AnnotationCallout from "./AnnotationCallout";
import ContrastLine from "./ContrastLine";
import {
  BACKGROUND_COLOR,
  DURATION_FRAMES,
  ANNOTATION1_START,
  ANNOTATION2_START,
  GITHUB_ACCENT,
  GITHUB_MAIN_TEXT,
  GITHUB_SOURCE,
  GITHUB_FINE_PRINT,
  GITHUB_CALLOUT_X,
  GITHUB_CALLOUT_Y,
  GITHUB_CONNECTOR_TARGET_X,
  GITHUB_CONNECTOR_TARGET_Y,
  UPLEVEL_ACCENT,
  UPLEVEL_MAIN_TEXT,
  UPLEVEL_SOURCE,
  UPLEVEL_FINE_PRINT,
  UPLEVEL_CALLOUT_X,
  UPLEVEL_CALLOUT_Y,
  UPLEVEL_CONNECTOR_TARGET_X,
  UPLEVEL_CONNECTOR_TARGET_Y,
} from "./constants";

export const defaultPart1Economics04ResearchAnnotationsProps = {};

export const Part1Economics04ResearchAnnotations: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: 1920,
        height: 1080,
        overflow: "hidden",
      }}
    >
      {/* Underlying chart from spec 03 holds throughout */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <BackgroundChart />
      </Sequence>

      {/* Annotation 1: GitHub study — materializes at frame 60 */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <AnnotationCallout
          startFrame={ANNOTATION1_START}
          accentColor={GITHUB_ACCENT}
          mainText={GITHUB_MAIN_TEXT}
          source={GITHUB_SOURCE}
          finePrint={GITHUB_FINE_PRINT}
          boxX={GITHUB_CALLOUT_X}
          boxY={GITHUB_CALLOUT_Y}
          targetX={GITHUB_CONNECTOR_TARGET_X}
          targetY={GITHUB_CONNECTOR_TARGET_Y}
        />
      </Sequence>

      {/* Annotation 2: Uplevel study — materializes at frame 300 */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <AnnotationCallout
          startFrame={ANNOTATION2_START}
          accentColor={UPLEVEL_ACCENT}
          mainText={UPLEVEL_MAIN_TEXT}
          source={UPLEVEL_SOURCE}
          finePrint={UPLEVEL_FINE_PRINT}
          boxX={UPLEVEL_CALLOUT_X}
          boxY={UPLEVEL_CALLOUT_Y}
          targetX={UPLEVEL_CONNECTOR_TARGET_X}
          targetY={UPLEVEL_CONNECTOR_TARGET_Y}
        />
      </Sequence>

      {/* Contrast connector dashed line between annotation boxes — frame 390 */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <ContrastLine />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics04ResearchAnnotations;
