import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  STEP_POSITIONS,
  STEPS,
  BLUE,
  DIM_BORDER,
  TEXT_LIGHT,
  TEXT_DIM,
  STEP1_START,
  STEP2_START,
  STEP3_START,
  STEP4_START,
  LOOP_START,
} from "./constants";
import { PromptDocIcon, WallIcons, TerminalIcon, DiffViewIcon } from "./PipelineIcons";
import { ProgressBar } from "./ProgressBar";
import { LoopArrow } from "./LoopArrow";

export const defaultWhereToStart05RegenerateCompareLoopProps = {};

/**
 * Connecting arrow between two pipeline steps.
 * Draws as a horizontal line with an arrowhead.
 */
const ConnectingArrow: React.FC<{
  fromX: number;
  toX: number;
  y: number;
  lit: boolean;
  litProgress: number;
}> = ({ fromX, toX, y, lit, litProgress }) => {
  const color = lit ? BLUE : DIM_BORDER;
  const opacity = lit ? interpolate(litProgress, [0, 1], [0.3, 0.5]) : 0.3;

  const arrowStartX = fromX + 40; // offset from step center
  const arrowEndX = toX - 40;
  const midY = y;

  return (
    <svg
      style={{ position: "absolute", top: 0, left: 0 }}
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
    >
      {/* Line */}
      <line
        x1={arrowStartX}
        y1={midY}
        x2={arrowEndX}
        y2={midY}
        stroke={color}
        strokeWidth={1.5}
        strokeOpacity={opacity}
      />
      {/* Arrowhead */}
      <polygon
        points={`${arrowEndX},${midY} ${arrowEndX - 6},${midY - 4} ${arrowEndX - 6},${midY + 4}`}
        fill={color}
        fillOpacity={opacity}
      />
    </svg>
  );
};

/**
 * A single pipeline step: icon area + label + sublabel, positioned absolutely.
 */
const PipelineStep: React.FC<{
  x: number;
  y: number;
  label: string;
  sublabel: string;
  visible: boolean;
  glowOpacity: number;
  children: React.ReactNode;
}> = ({ x, y, label, sublabel, visible, glowOpacity, children }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: x,
        top: y,
        transform: "translate(-50%, -50%)",
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        gap: 12,
        opacity: visible ? 1 : 0.3,
      }}
    >
      {/* Glow behind icon */}
      {glowOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            width: 80,
            height: 80,
            borderRadius: "50%",
            background: `radial-gradient(circle, ${BLUE}22 0%, transparent 70%)`,
            opacity: glowOpacity,
            top: -8,
            left: "50%",
            transform: "translateX(-50%)",
            pointerEvents: "none",
          }}
        />
      )}

      {/* Icon container */}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          minHeight: 65,
        }}
      >
        {children}
      </div>

      {/* Label */}
      <div
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 11,
          color: TEXT_LIGHT,
          opacity: 0.5,
          textAlign: "center",
          whiteSpace: "nowrap",
        }}
      >
        {label}
      </div>

      {/* Sublabel */}
      <div
        style={{
          fontFamily: "JetBrains Mono, monospace",
          fontSize: 9,
          color: TEXT_DIM,
          opacity: 0.3,
          textAlign: "center",
          whiteSpace: "nowrap",
          marginTop: -6,
        }}
      >
        {sublabel}
      </div>
    </div>
  );
};

/**
 * Pipeline skeleton: dim circles/dots at step positions, visible from frame 0.
 */
const PipelineSkeleton: React.FC = () => {
  return (
    <>
      {STEP_POSITIONS.map(([x, y], i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: x,
            top: y,
            transform: "translate(-50%, -50%)",
            width: 60,
            height: 60,
            border: `1px solid ${DIM_BORDER}`,
            borderRadius: 8,
            opacity: 0.15,
          }}
        />
      ))}
    </>
  );
};

export const WhereToStart05RegenerateCompareLoop: React.FC = () => {
  const frame = useCurrentFrame();

  // Step activation progress (0-1) for each step
  const step1Progress = interpolate(frame - STEP1_START, [0, 15], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const step2Progress = interpolate(frame - STEP2_START, [0, 15], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const step3Progress = interpolate(frame - STEP3_START, [0, 15], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const step4Progress = interpolate(frame - STEP4_START, [0, 15], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Arrow lighting progress (lags step by a few frames)
  const arrow1Lit = frame >= STEP1_START + 5;
  const arrow1Progress = interpolate(frame - (STEP1_START + 5), [0, 10], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const arrow2Lit = frame >= STEP2_START + 5;
  const arrow2Progress = interpolate(frame - (STEP2_START + 5), [0, 10], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const arrow3Lit = frame >= STEP3_START + 5;
  const arrow3Progress = interpolate(frame - (STEP3_START + 5), [0, 10], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Skeleton fade (visible immediately, fades as steps appear)
  const skeletonOpacity = interpolate(frame, [0, 20], [1, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Pipeline skeleton - visible from frame 0 */}
      <div style={{ opacity: skeletonOpacity }}>
        <PipelineSkeleton />
      </div>

      {/* Connecting arrows (dim from frame 0, light up as steps activate) */}
      <ConnectingArrow
        fromX={STEP_POSITIONS[0][0]}
        toX={STEP_POSITIONS[1][0]}
        y={STEP_POSITIONS[0][1]}
        lit={arrow1Lit}
        litProgress={arrow1Progress}
      />
      <ConnectingArrow
        fromX={STEP_POSITIONS[1][0]}
        toX={STEP_POSITIONS[2][0]}
        y={STEP_POSITIONS[1][1]}
        lit={arrow2Lit}
        litProgress={arrow2Progress}
      />
      <ConnectingArrow
        fromX={STEP_POSITIONS[2][0]}
        toX={STEP_POSITIONS[3][0]}
        y={STEP_POSITIONS[2][1]}
        lit={arrow3Lit}
        litProgress={arrow3Progress}
      />

      {/* Step 1: Generate Prompt */}
      <PipelineStep
        x={STEP_POSITIONS[0][0]}
        y={STEP_POSITIONS[0][1]}
        label={STEPS[0].label}
        sublabel={STEPS[0].sublabel}
        visible={frame >= STEP1_START}
        glowOpacity={step1Progress * 0.6}
      >
        {frame >= STEP1_START && (
          <PromptDocIcon
            progress={interpolate(frame - STEP1_START, [0, 12], [0, 1], {
              easing: Easing.out(Easing.cubic),
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })}
          />
        )}
      </PipelineStep>

      {/* Step 2: Add Tests */}
      <PipelineStep
        x={STEP_POSITIONS[1][0]}
        y={STEP_POSITIONS[1][1]}
        label={STEPS[1].label}
        sublabel={STEPS[1].sublabel}
        visible={frame >= STEP2_START}
        glowOpacity={step2Progress * 0.6}
      >
        {frame >= STEP2_START && (
          <WallIcons frame={frame - STEP2_START} />
        )}
      </PipelineStep>

      {/* Step 3: Regenerate */}
      <PipelineStep
        x={STEP_POSITIONS[2][0]}
        y={STEP_POSITIONS[2][1]}
        label={STEPS[2].label}
        sublabel={STEPS[2].sublabel}
        visible={frame >= STEP3_START}
        glowOpacity={step3Progress * 0.6}
      >
        {frame >= STEP3_START && (
          <TerminalIcon
            progress={interpolate(frame - STEP3_START, [0, 12], [0, 1], {
              easing: Easing.out(Easing.cubic),
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })}
            frame={frame - STEP3_START}
          />
        )}
      </PipelineStep>

      {/* Step 4: Compare */}
      <PipelineStep
        x={STEP_POSITIONS[3][0]}
        y={STEP_POSITIONS[3][1]}
        label={STEPS[3].label}
        sublabel={STEPS[3].sublabel}
        visible={frame >= STEP4_START}
        glowOpacity={step4Progress * 0.6}
      >
        {frame >= STEP4_START && (
          <DiffViewIcon
            progress={interpolate(frame - STEP4_START, [0, 12], [0, 1], {
              easing: Easing.out(Easing.cubic),
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            })}
            frame={frame - STEP4_START}
          />
        )}
      </PipelineStep>

      {/* Loop arrow (Step 4 → Step 2) */}
      {frame >= LOOP_START && (
        <LoopArrow frame={frame - LOOP_START} />
      )}

      {/* Progress bar */}
      <ProgressBar frame={frame} />
    </AbsoluteFill>
  );
};

export default WhereToStart05RegenerateCompareLoop;
