import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  GRID_LINE_COLOR,
  GRID_LINE_OPACITY,
  AXIS_LABEL_COLOR,
  EMPHASIS_COLOR,
  STEPS,
  STEP_FRAME_STARTS,
  STEP_DRAW_DURATION,
  ARROW_DELAY,
  FADE_OUT_START,
  FADE_OUT_DURATION,
  GRID_Y_POSITIONS,
  DECADE_MARKERS,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";
import StaircaseStep from "./StaircaseStep";
import ScaleArrow from "./ScaleArrow";

export const defaultPart2ParadigmShift15AbstractionStaircaseProps = {};

export const Part2ParadigmShift15AbstractionStaircase: React.FC = () => {
  const frame = useCurrentFrame();

  // Axis labels fade-in over first 30 frames
  const axisOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.poly(2)),
  });

  // Global fade-out at end
  const fadeOutOpacity = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_START + FADE_OUT_DURATION],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.poly(2)),
    }
  );

  // Vertical connecting lines between steps (risers of the staircase)
  const renderRisers = () => {
    return STEPS.slice(0, -1).map((step, i) => {
      const nextStep = STEPS[i + 1];
      const riserFrame = STEP_FRAME_STARTS[i + 1];
      const relFrame = frame - riserFrame;
      if (relFrame < 0) return null;

      const progress = interpolate(relFrame, [0, STEP_DRAW_DURATION], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.poly(2)),
      });

      const x = step.x2;
      const topY = nextStep.y + nextStep.stepHeight;
      const bottomY = step.y;
      const currentTopY = bottomY + (topY - bottomY) * progress;

      return (
        <div
          key={`riser-${i}`}
          style={{
            position: "absolute",
            left: x - 1,
            top: currentTopY,
            width: 2,
            height: bottomY - currentTopY,
            backgroundColor: step.fillColor,
            opacity: 0.4 * progress,
          }}
        />
      );
    });
  };

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
        opacity: fadeOutOpacity,
      }}
    >
      {/* Faint horizontal grid lines at step heights */}
      {GRID_Y_POSITIONS.map((y) => (
        <div
          key={`grid-${y}`}
          style={{
            position: "absolute",
            left: 80,
            top: y + 30,
            width: CANVAS_WIDTH - 160,
            height: 1,
            backgroundColor: GRID_LINE_COLOR,
            opacity: GRID_LINE_OPACITY,
          }}
        />
      ))}

      {/* Y-axis label: "Abstraction Level" rotated 90° */}
      <div
        style={{
          position: "absolute",
          left: 18,
          top: CANVAS_HEIGHT / 2,
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: axisOpacity,
          transform: "rotate(-90deg)",
          transformOrigin: "center center",
          whiteSpace: "nowrap",
          letterSpacing: "0.5px",
        }}
      >
        Abstraction Level
      </div>

      {/* Y-axis vertical line */}
      <div
        style={{
          position: "absolute",
          left: 80,
          top: 160,
          width: 2,
          height: 740,
          backgroundColor: AXIS_LABEL_COLOR,
          opacity: axisOpacity * 0.15,
          borderRadius: 1,
        }}
      />

      {/* X-axis horizontal line */}
      <div
        style={{
          position: "absolute",
          left: 80,
          top: 900,
          width: CANVAS_WIDTH - 160,
          height: 2,
          backgroundColor: AXIS_LABEL_COLOR,
          opacity: axisOpacity * 0.15,
          borderRadius: 1,
        }}
      />

      {/* X-axis decade markers */}
      {DECADE_MARKERS.map((marker) => (
        <div
          key={`decade-${marker.label}`}
          style={{
            position: "absolute",
            left: marker.x - 30,
            top: 916,
            width: 60,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            fontWeight: 400,
            color: AXIS_LABEL_COLOR,
            opacity: axisOpacity,
          }}
        >
          {marker.label}
        </div>
      ))}

      {/* Vertical riser lines between steps */}
      {renderRisers()}

      {/* "Couldn't scale" arrows between steps */}
      {STEPS.slice(0, -1).map((step, i) => (
        <ScaleArrow
          key={`arrow-${i}`}
          fromStep={step}
          toStep={STEPS[i + 1]}
          enterFrame={STEP_FRAME_STARTS[i] + ARROW_DELAY}
        />
      ))}

      {/* Staircase steps */}
      {STEPS.map((step, i) => (
        <StaircaseStep
          key={`step-${i}`}
          step={step}
          enterFrame={STEP_FRAME_STARTS[i]}
          drawDuration={STEP_DRAW_DURATION}
        />
      ))}

      {/* Emphasized label below step 5 */}
      {frame >= STEP_FRAME_STARTS[4] && (
        <div
          style={{
            position: "absolute",
            left: STEPS[4].x1,
            top: STEPS[4].y + STEPS[4].stepHeight + 12,
            width: STEPS[4].x2 - STEPS[4].x1,
            textAlign: "center",
            fontFamily: "Inter, sans-serif",
            fontSize: 18,
            fontWeight: 700,
            color: EMPHASIS_COLOR,
            opacity: interpolate(
              frame,
              [STEP_FRAME_STARTS[4], STEP_FRAME_STARTS[4] + 30],
              [0, 0.9],
              {
                extrapolateLeft: "clamp",
                extrapolateRight: "clamp",
              }
            ),
          }}
        >
          Where we are now
        </div>
      )}

      {/* Title at top */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 40,
          width: CANVAS_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 28,
          fontWeight: 700,
          color: "#E2E8F0",
          opacity: axisOpacity * 0.85,
          letterSpacing: "0.5px",
        }}
      >
        The Abstraction Staircase
      </div>

      {/* Subtitle */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 78,
          width: CANVAS_WIDTH,
          textAlign: "center",
          fontFamily: "Inter, sans-serif",
          fontSize: 16,
          fontWeight: 400,
          color: AXIS_LABEL_COLOR,
          opacity: axisOpacity * 0.7,
        }}
      >
        Every time complexity exceeded the current abstraction, the industry
        moved up
      </div>

      {/* Upward arrow indicator on y-axis */}
      <svg
        width={40}
        height={40}
        viewBox="0 0 40 40"
        style={{
          position: "absolute",
          left: 62,
          top: 130,
          opacity: axisOpacity * 0.4,
        }}
      >
        <polygon points="20,5 30,25 10,25" fill={AXIS_LABEL_COLOR} />
      </svg>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift15AbstractionStaircase;
