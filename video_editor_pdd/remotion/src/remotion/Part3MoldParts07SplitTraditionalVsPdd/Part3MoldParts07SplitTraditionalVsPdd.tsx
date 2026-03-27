import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { FlowStep } from "./FlowStep";
import { FlowArrow } from "./FlowArrow";
import { PulsingEllipsis } from "./PulsingEllipsis";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  DIVIDER_COLOR,
  DIVIDER_WIDTH,
  DIVIDER_OPACITY,
  PANEL_WIDTH,
  TRAD_HEADER_COLOR,
  TRAD_BORDER_COLOR,
  TRAD_ARROW_COLOR,
  TRAD_ELLIPSIS_COLOR,
  TRAD_STEP_WIDTH,
  PDD_HEADER_COLOR,
  PDD_BORDER_COLOR,
  PDD_ARROW_COLOR,
  PDD_STEP_WIDTH,
  HEADER_SIZE,
  HEADER_Y,
  FLOW_START_Y,
  STEP_SPACING,
  FADE_DURATION,
  TRADITIONAL_STEPS,
  PDD_STEPS,
} from "./constants";

export const defaultPart3MoldParts07SplitTraditionalVsPddProps = {};

export const Part3MoldParts07SplitTraditionalVsPdd: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall fade-in for the split screen (frames 0-20)
  const sceneOpacity = interpolate(
    frame,
    [0, 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Header fade-in (frames 0-15)
  const headerOpacity = interpolate(
    frame,
    [0, FADE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Center X for left panel's flowchart (right panel uses local coordinates)
  const leftCenterX = PANEL_WIDTH / 2; // 460

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: sceneOpacity,
      }}
    >
      {/* Center divider */}
      <div
        style={{
          position: "absolute",
          left: CANVAS_WIDTH / 2 - DIVIDER_WIDTH / 2,
          top: 80,
          width: DIVIDER_WIDTH,
          height: CANVAS_HEIGHT - 160,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
        }}
      />

      {/* ===== LEFT PANEL — TRADITIONAL ===== */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: CANVAS_WIDTH / 2,
          height: CANVAS_HEIGHT,
        }}
      >
        {/* Header */}
        <div
          style={{
            position: "absolute",
            top: HEADER_Y,
            width: "100%",
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: HEADER_SIZE,
            fontWeight: 700,
            color: TRAD_HEADER_COLOR,
            opacity: headerOpacity,
            letterSpacing: 2,
          }}
        >
          TRADITIONAL
        </div>

        {/* Flow steps */}
        {TRADITIONAL_STEPS.map((step, i) => {
          const stepY = FLOW_START_Y + i * STEP_SPACING;
          return (
            <React.Fragment key={`trad-step-${i}`}>
              <FlowStep
                text={step.text}
                stepWidth={TRAD_STEP_WIDTH}
                borderColor={TRAD_BORDER_COLOR}
                startFrame={step.startFrame}
                hasBandaid={step.hasBandaid}
                hasCode={false}
                isFinal={false}
                centerX={leftCenterX}
                y={stepY}
              />
              {/* Arrow between steps (not after last step) */}
              {i < TRADITIONAL_STEPS.length - 1 && (
                <FlowArrow
                  color={TRAD_ARROW_COLOR}
                  startFrame={step.startFrame}
                  centerX={leftCenterX}
                  y={stepY}
                />
              )}
            </React.Fragment>
          );
        })}

        {/* Pulsing ellipsis after last step */}
        <PulsingEllipsis
          color={TRAD_ELLIPSIS_COLOR}
          startFrame={170}
          centerX={leftCenterX}
          y={FLOW_START_Y + TRADITIONAL_STEPS.length * STEP_SPACING + 5}
        />
      </div>

      {/* ===== RIGHT PANEL — PDD ===== */}
      <div
        style={{
          position: "absolute",
          left: CANVAS_WIDTH / 2,
          top: 0,
          width: CANVAS_WIDTH / 2,
          height: CANVAS_HEIGHT,
        }}
      >
        {/* Header */}
        <div
          style={{
            position: "absolute",
            top: HEADER_Y,
            width: "100%",
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: HEADER_SIZE,
            fontWeight: 700,
            color: PDD_HEADER_COLOR,
            opacity: headerOpacity,
            letterSpacing: 2,
          }}
        >
          PDD
        </div>

        {/* Flow steps */}
        {PDD_STEPS.map((step, i) => {
          const stepY = FLOW_START_Y + i * STEP_SPACING;
          // The right panel uses local coordinates (0-960), center at 480
          const localCenterX = PANEL_WIDTH / 2;
          return (
            <React.Fragment key={`pdd-step-${i}`}>
              <FlowStep
                text={step.text}
                stepWidth={PDD_STEP_WIDTH}
                borderColor={PDD_BORDER_COLOR}
                startFrame={step.startFrame}
                hasBandaid={false}
                hasCode={step.hasCode}
                codeText={step.codeText}
                isFinal={step.isFinal}
                centerX={localCenterX}
                y={stepY}
              />
              {/* Arrow between steps (not after last step) */}
              {i < PDD_STEPS.length - 1 && (
                <FlowArrow
                  color={PDD_ARROW_COLOR}
                  startFrame={step.startFrame}
                  centerX={localCenterX}
                  y={stepY}
                />
              )}
            </React.Fragment>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};

export default Part3MoldParts07SplitTraditionalVsPdd;
