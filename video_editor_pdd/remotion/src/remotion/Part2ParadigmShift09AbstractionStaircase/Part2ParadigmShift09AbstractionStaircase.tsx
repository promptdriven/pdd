import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BACKGROUND_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  Y_AXIS_COLOR,
  Y_AXIS_OPACITY,
  ACTIVE_COLOR,
  STEPS,
  ANIM,
  STEP_WIDTH,
} from "./constants";
import { StaircaseStep } from "./StaircaseStep";
import { AbstractionIcon } from "./AbstractionIcon";
import { ScaleArrow } from "./ScaleArrow";
import { PulsingGlow, ParticleDrift } from "./PulsingGlow";

export const defaultPart2ParadigmShift09AbstractionStaircaseProps = {};

export const Part2ParadigmShift09AbstractionStaircase: React.FC = () => {
  const frame = useCurrentFrame();

  // Background & grid fade in
  const gridOpacity = interpolate(frame, [0, ANIM.BG_END], [0, GRID_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Y-axis label fade in
  const yAxisOpacity = interpolate(
    frame,
    [0, ANIM.BG_END],
    [0, Y_AXIS_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BACKGROUND_COLOR }}>
      {/* Perspective grid */}
      <PerspectiveGrid opacity={gridOpacity} />

      {/* Y-axis label */}
      <div
        style={{
          position: "absolute",
          left: 30,
          top: 350,
          opacity: yAxisOpacity,
        }}
      >
        {/* Upward arrow */}
        <svg
          width={20}
          height={200}
          style={{ position: "absolute", left: 10, top: 0 }}
        >
          <line
            x1={10}
            y1={190}
            x2={10}
            y2={10}
            stroke={Y_AXIS_COLOR}
            strokeWidth={1}
            opacity={Y_AXIS_OPACITY}
          />
          <polygon
            points="10,5 6,15 14,15"
            fill={Y_AXIS_COLOR}
            opacity={Y_AXIS_OPACITY}
          />
        </svg>
        {/* Vertical text */}
        <div
          style={{
            position: "absolute",
            left: -50,
            top: 60,
            transform: "rotate(-90deg)",
            transformOrigin: "center center",
            fontFamily: "Inter, sans-serif",
            fontSize: 11,
            color: Y_AXIS_COLOR,
            opacity: Y_AXIS_OPACITY,
            whiteSpace: "nowrap",
            letterSpacing: 1,
          }}
        >
          Abstraction level
        </div>
      </div>

      {/* Steps, arrows, icons, and labels */}
      {STEPS.map((step, i) => {
        const stepStartFrame = ANIM.STEP_BASE_FRAME + i * ANIM.STEP_INTERVAL;
        const localFrame = frame - stepStartFrame;

        return (
          <React.Fragment key={step.level}>
            {/* "Couldn't scale" arrow from previous step */}
            {i > 0 && (
              <ScaleArrow
                fromX={STEPS[i - 1].x}
                fromY={STEPS[i - 1].y}
                toX={step.x}
                toY={step.y}
                localFrame={localFrame}
                isDramatic={i === 4}
              />
            )}

            {/* Step platform */}
            <StaircaseStep
              x={step.x}
              y={step.y}
              localFrame={localFrame}
            />

            {/* Abstraction icon */}
            <AbstractionIcon
              type={step.iconType}
              x={step.x}
              y={step.y}
              color={step.color}
              localFrame={localFrame}
              isActive={step.isActive}
              glowFrame={frame - ANIM.STEP5_GLOW_START}
            />

            {/* Step label */}
            <StepLabel
              text={step.label}
              decade={step.decade}
              x={step.x}
              y={step.y}
              color={step.color}
              localFrame={localFrame}
              isActive={step.isActive}
            />
          </React.Fragment>
        );
      })}

      {/* Step 5 pulsing glow */}
      <PulsingGlow
        x={STEPS[4].x}
        y={STEPS[4].y}
        startFrame={ANIM.STEP5_GLOW_START}
      />

      {/* Particle drift on step 5 */}
      <ParticleDrift
        x={STEPS[4].x + STEP_WIDTH / 2}
        y={STEPS[4].y}
        startFrame={ANIM.PARTICLE_START}
      />

      {/* Dashed future line from step 5 */}
      <FutureLine
        x={STEPS[4].x + STEP_WIDTH}
        y={STEPS[4].y - 80}
        frame={frame}
      />
    </AbsoluteFill>
  );
};

// Perspective grid sub-component
const PerspectiveGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  if (opacity <= 0) return null;

  const lines: React.ReactNode[] = [];
  const vanishX = 1600;
  const vanishY = 100;

  // Horizontal guide lines
  for (let i = 0; i < 8; i++) {
    const y = 200 + i * 120;
    lines.push(
      <line
        key={`h${i}`}
        x1={0}
        y1={y}
        x2={1920}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={0.5}
        opacity={opacity}
      />
    );
  }

  // Converging lines toward vanish point
  for (let i = 0; i < 6; i++) {
    const startX = i * 350;
    lines.push(
      <line
        key={`v${i}`}
        x1={startX}
        y1={1080}
        x2={vanishX}
        y2={vanishY}
        stroke={GRID_COLOR}
        strokeWidth={0.5}
        opacity={opacity * 0.5}
      />
    );
  }

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {lines}
    </svg>
  );
};

// Step label sub-component
interface StepLabelProps {
  text: string;
  decade: string;
  x: number;
  y: number;
  color: string;
  localFrame: number;
  isActive?: boolean;
}

const StepLabel: React.FC<StepLabelProps> = ({
  text,
  decade,
  x,
  y,
  color,
  localFrame,
  isActive,
}) => {
  const labelDelay = ANIM.STEP_DRAW_DURATION + 5;
  const labelOpacity = interpolate(
    localFrame,
    [labelDelay, labelDelay + ANIM.LABEL_FADE_DURATION],
    [0, isActive ? 0.7 : 0.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const decadeOpacity = interpolate(
    localFrame,
    [labelDelay + 5, labelDelay + 5 + ANIM.LABEL_FADE_DURATION],
    [0, isActive ? 0.4 : 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  if (labelOpacity <= 0) return null;

  const decadeColor = isActive ? ACTIVE_COLOR : "#475569";

  return (
    <>
      <div
        style={{
          position: "absolute",
          left: x + 80,
          top: y - 75,
          fontFamily: "Inter, sans-serif",
          fontSize: 14,
          fontWeight: isActive ? 600 : 400,
          color,
          opacity: labelOpacity,
          whiteSpace: "nowrap",
        }}
      >
        {text}
      </div>
      <div
        style={{
          position: "absolute",
          left: x + 80,
          top: y - 55,
          fontFamily: "Inter, sans-serif",
          fontSize: 10,
          color: decadeColor,
          opacity: decadeOpacity,
          whiteSpace: "nowrap",
        }}
      >
        {decade}
      </div>
    </>
  );
};

// Dashed future line from step 5
const FutureLine: React.FC<{ x: number; y: number; frame: number }> = ({
  x,
  y,
  frame,
}) => {
  const startFrame = ANIM.HOLD_START;
  const opacity = interpolate(
    frame,
    [startFrame, startFrame + 30],
    [0, 0.2],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  if (opacity <= 0) return null;

  return (
    <svg
      width={300}
      height={100}
      style={{ position: "absolute", left: x, top: y }}
    >
      <line
        x1={0}
        y1={50}
        x2={250}
        y2={10}
        stroke={ACTIVE_COLOR}
        strokeWidth={1.5}
        strokeDasharray="6 4"
        opacity={opacity}
      />
      {/* Small arrow at end */}
      <polygon
        points="250,10 242,8 244,16"
        fill={ACTIVE_COLOR}
        opacity={opacity}
      />
    </svg>
  );
};

export default Part2ParadigmShift09AbstractionStaircase;
