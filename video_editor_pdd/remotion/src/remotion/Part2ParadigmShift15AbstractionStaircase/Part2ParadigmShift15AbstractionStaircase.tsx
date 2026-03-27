import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { StaircaseStep } from "./StaircaseStep";
import { ScaleArrow } from "./ScaleArrow";
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  AXIS_COLOR,
  STEPS,
  STEP_ENTRANCE_FRAMES,
  STEP_DRAW_DURATION,
  ARROW_DELAY,
  ARROW_DRAW_DURATION,
  ARROW_COLOR,
  ARROW_OPACITY,
  STEP5_PULSE_START,
  STEP5_PULSE_CYCLE,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  DECADE_MARKERS,
  STEP_GREEN,
} from "./constants";

export const defaultPart2ParadigmShift15AbstractionStaircaseProps = {};

export const Part2ParadigmShift15AbstractionStaircase: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade out at end
  const fadeOutOpacity =
    frame >= FADE_OUT_START
      ? interpolate(
          frame,
          [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
          [1, 0],
          {
            easing: Easing.in(Easing.quad),
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        )
      : 1;

  // Axis labels fade in at frame 0
  const axisOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Grid lines at step heights
  const gridYPositions = [200, 350, 500, 650, 800];

  // Build arrows between steps
  const arrows: {
    fromX: number;
    fromY: number;
    toX: number;
    toY: number;
    entranceFrame: number;
  }[] = [];

  for (let i = 0; i < STEPS.length - 1; i++) {
    const fromStep = STEPS[i];
    const toStep = STEPS[i + 1];
    arrows.push({
      fromX: fromStep.x + fromStep.width - 20,
      fromY: fromStep.y,
      toX: toStep.x + 20,
      toY: toStep.y + toStep.stepHeight,
      entranceFrame: STEP_ENTRANCE_FRAMES[i] + ARROW_DELAY,
    });
  }

  // Step 5 emphasis label
  const step5 = STEPS[4];
  const step5LabelFrame = STEP_ENTRANCE_FRAMES[4] + STEP_DRAW_DURATION;
  const step5LabelOpacity =
    frame >= step5LabelFrame
      ? interpolate(frame, [step5LabelFrame, step5LabelFrame + 30], [0, 1], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 0;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOutOpacity,
        overflow: "hidden",
      }}
    >
      {/* Faint horizontal grid lines */}
      <svg
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 1920,
          height: 1080,
          pointerEvents: "none",
        }}
      >
        {gridYPositions.map((gy) => (
          <line
            key={gy}
            x1={80}
            y1={gy + 30}
            x2={1800}
            y2={gy + 30}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}
      </svg>

      {/* Y-axis label — rotated */}
      <div
        style={{
          position: "absolute",
          left: 20,
          top: 500,
          transform: "rotate(-90deg)",
          transformOrigin: "0 0",
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_COLOR,
          opacity: axisOpacity,
          whiteSpace: "nowrap",
        }}
      >
        Abstraction Level
      </div>

      {/* X-axis decade markers */}
      {DECADE_MARKERS.map((dm) => (
        <div
          key={dm.label}
          style={{
            position: "absolute",
            left: dm.x,
            top: 900,
            transform: "translateX(-50%)",
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 400,
            color: AXIS_COLOR,
            opacity: axisOpacity,
          }}
        >
          {dm.label}
        </div>
      ))}

      {/* X-axis baseline */}
      <svg
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 1920,
          height: 1080,
          pointerEvents: "none",
        }}
      >
        <line
          x1={100}
          y1={880}
          x2={1700}
          y2={880}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={axisOpacity * 0.3}
        />
        {/* Y-axis line */}
        <line
          x1={100}
          y1={160}
          x2={100}
          y2={880}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={axisOpacity * 0.3}
        />
      </svg>

      {/* Staircase Steps */}
      {STEPS.map((step, i) => (
        <StaircaseStep
          key={step.label}
          x={step.x}
          y={step.y}
          width={step.width}
          stepHeight={step.stepHeight}
          fillColor={step.fillColor}
          fillOpacity={step.fillOpacity}
          borderColor={step.borderColor}
          label={step.label}
          decade={step.decade}
          emphasis={step.emphasis}
          entranceFrame={STEP_ENTRANCE_FRAMES[i]}
          drawDuration={STEP_DRAW_DURATION}
          pulseStart={STEP5_PULSE_START}
          pulseCycle={STEP5_PULSE_CYCLE}
        />
      ))}

      {/* Vertical connectors between steps (the riser part of the staircase) */}
      {STEPS.slice(0, -1).map((step, i) => {
        const nextStep = STEPS[i + 1];
        const connectorFrame = STEP_ENTRANCE_FRAMES[i + 1];
        const relFrame = frame - connectorFrame;
        if (relFrame < 0) return null;

        const connectorProgress = interpolate(
          relFrame,
          [0, STEP_DRAW_DURATION],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          }
        );

        return (
          <svg
            key={`connector-${i}`}
            style={{
              position: "absolute",
              left: 0,
              top: 0,
              width: 1920,
              height: 1080,
              pointerEvents: "none",
            }}
          >
            {/* Horizontal line from current step to next step x */}
            <line
              x1={step.x + step.width}
              y1={step.y + step.stepHeight / 2}
              x2={step.x + step.width}
              y2={
                step.y +
                step.stepHeight / 2 -
                (step.y +
                  step.stepHeight / 2 -
                  (nextStep.y + nextStep.stepHeight / 2)) *
                  connectorProgress
              }
              stroke={step.borderColor}
              strokeWidth={1}
              opacity={0.2 * connectorProgress}
              strokeDasharray="4 4"
            />
          </svg>
        );
      })}

      {/* Scale Arrows between steps */}
      {arrows.map((arrow, i) => (
        <ScaleArrow
          key={`arrow-${i}`}
          fromX={arrow.fromX}
          fromY={arrow.fromY}
          toX={arrow.toX}
          toY={arrow.toY}
          entranceFrame={arrow.entranceFrame}
          drawDuration={ARROW_DRAW_DURATION}
          arrowColor={ARROW_COLOR}
          arrowOpacity={ARROW_OPACITY}
          label="Couldn't scale"
        />
      ))}

      {/* Step 5 emphasis label below the step */}
      <div
        style={{
          position: "absolute",
          left: step5.x,
          top: step5.y + step5.stepHeight + 16,
          width: step5.width,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 18,
          fontWeight: 700,
          color: STEP_GREEN,
          opacity: step5LabelOpacity * 0.9,
          textShadow: `0 0 12px ${STEP_GREEN}66`,
        }}
      >
        Natural language → Code
      </div>

      {/* Title — subtle top label */}
      <div
        style={{
          position: "absolute",
          top: 40,
          left: 0,
          width: 1920,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: "#E2E8F0",
          opacity: axisOpacity * 0.85,
          letterSpacing: 1,
        }}
      >
        The Abstraction Staircase
      </div>

      {/* Subtitle */}
      <div
        style={{
          position: "absolute",
          top: 78,
          left: 0,
          width: 1920,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 400,
          color: AXIS_COLOR,
          opacity: axisOpacity * 0.65,
        }}
      >
        Each level emerged when complexity exceeded the previous abstraction
      </div>

      {/* Upward arrow indicator on Y-axis */}
      <svg
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 1920,
          height: 1080,
          pointerEvents: "none",
        }}
      >
        <polygon
          points="100,160 95,175 105,175"
          fill={AXIS_COLOR}
          opacity={axisOpacity * 0.4}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift15AbstractionStaircase;
