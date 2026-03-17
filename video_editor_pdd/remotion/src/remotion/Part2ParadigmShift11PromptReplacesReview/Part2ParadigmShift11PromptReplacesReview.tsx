import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BG_COLOR,
  LEFT_BG,
  RIGHT_BG,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  SPLIT_X,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_START,
  RIGHT_PANEL_WIDTH,
  DIVIDER_WIDTH,
  RED_ACCENT,
  GREEN_ACCENT,
  SPLIT_LINE_START,
  SPLIT_LINE_END,
  HEADER_FADE_START,
  HEADER_FADE_END,
  METER_Y,
} from "./constants";
import { FrozenCodeDiff } from "./FrozenCodeDiff";
import { PulsingQuestionMark } from "./PulsingQuestionMark";
import { PromptDocument } from "./PromptDocument";
import { TestSuitePanel } from "./TestSuitePanel";
import { CognitiveLoadMeter } from "./CognitiveLoadMeter";

export const defaultPart2ParadigmShift11PromptReplacesReviewProps = {};

export const Part2ParadigmShift11PromptReplacesReview: React.FC = () => {
  const frame = useCurrentFrame();

  // Split line draw animation
  const splitLineHeight = interpolate(
    frame,
    [SPLIT_LINE_START, SPLIT_LINE_END],
    [0, CANVAS_HEIGHT],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Header fade in
  const headerOpacity = interpolate(
    frame,
    [HEADER_FADE_START, HEADER_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* ========== LEFT PANEL — Old: Review the Code ========== */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: LEFT_BG,
          overflow: "hidden",
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: headerOpacity * 0.4,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 14,
              fontWeight: 600,
              color: RED_ACCENT,
              letterSpacing: 2,
              textDecoration: "line-through",
              textDecorationColor: RED_ACCENT,
            }}
          >
            REVIEW THE CODE
          </span>
        </div>

        {/* Frozen code diff */}
        <FrozenCodeDiff />

        {/* Pulsing red question mark */}
        <PulsingQuestionMark />

        {/* Cognitive load meter — LEFT */}
        <CognitiveLoadMeter
          centerX={LEFT_PANEL_WIDTH / 2}
          centerY={METER_Y}
          fillPercent={100}
          color={RED_ACCENT}
          status="OVERLOADED"
        />
      </div>

      {/* ========== SPLIT DIVIDER ========== */}
      <div
        style={{
          position: "absolute",
          left: SPLIT_X - DIVIDER_WIDTH / 2,
          top: 0,
          width: DIVIDER_WIDTH,
          height: splitLineHeight,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
        }}
      />

      {/* ========== RIGHT PANEL — New: Review the Spec ========== */}
      <div
        style={{
          position: "absolute",
          left: RIGHT_PANEL_START,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: RIGHT_BG,
          overflow: "hidden",
        }}
      >
        {/* Panel header */}
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: headerOpacity * 0.5,
          }}
        >
          <span
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 14,
              fontWeight: 600,
              color: GREEN_ACCENT,
              letterSpacing: 2,
            }}
          >
            REVIEW THE SPEC
          </span>
        </div>

        {/* Prompt document */}
        <PromptDocument />

        {/* Test suite panel */}
        <TestSuitePanel />

        {/* Cognitive load meter — RIGHT */}
        <CognitiveLoadMeter
          centerX={RIGHT_PANEL_WIDTH / 2}
          centerY={METER_Y}
          fillPercent={25}
          color={GREEN_ACCENT}
          status="MANAGEABLE"
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift11PromptReplacesReview;
