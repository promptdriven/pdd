import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  GREEN_LINE_COLOR,
  RED_LINE_COLOR,
  DEBT_AREA_COLOR,
  FONT_FAMILY,
  GENERATE_LINE_DATA,
  PATCH_LINE_DATA,
  SMALL_CODEBASE_DATA,
  LARGE_CODEBASE_DATA,
  FORK_START,
  FORK_ANIM_DURATION,
  dataToSmoothPath,
  xToPixel,
  yToPixel,
  CHART_BOTTOM,
  DataPoint,
} from "./constants";

/** Partially reveal an SVG path using stroke-dashoffset */
const AnimatedPath: React.FC<{
  d: string;
  color: string;
  strokeWidth: number;
  progress: number;
  dashed?: boolean;
}> = ({ d, color, strokeWidth, progress, dashed }) => {
  const totalLength = 4000; // generous upper-bound
  return (
    <path
      d={d}
      fill="none"
      stroke={color}
      strokeWidth={strokeWidth}
      strokeLinecap="round"
      strokeLinejoin="round"
      strokeDasharray={dashed ? "8 4" : totalLength}
      strokeDashoffset={dashed ? 0 : totalLength * (1 - progress)}
    />
  );
};

/** Debt-fill area between generate and patch lines */
const DebtArea: React.FC<{ opacity: number }> = ({ opacity }) => {
  const gen = GENERATE_LINE_DATA;
  const patch = PATCH_LINE_DATA;
  // Build polygon between generate (top, lower cost) and patch (bottom, higher cost)
  // Actually generate is lower cost → lower y-pixel → higher on screen
  const topPoints = gen
    .filter((p) => p.x <= 2020)
    .map((p) => `${xToPixel(p.x)},${yToPixel(p.y)}`);
  const bottomPoints = [...patch]
    .reverse()
    .map((p) => `${xToPixel(p.x)},${yToPixel(p.y)}`);
  const points = [...topPoints, ...bottomPoints].join(" ");

  return <polygon points={points} fill={DEBT_AREA_COLOR} opacity={opacity} />;
};

/** Fork label positioned near the end of a fork line */
const ForkLabel: React.FC<{
  data: DataPoint[];
  label: string;
  color: string;
  opacity: number;
}> = ({ data, label, color, opacity }) => {
  const last = data[data.length - 1];
  const px = xToPixel(last.x) + 12;
  const py = yToPixel(last.y) + 5;
  return (
    <text
      x={px}
      y={py}
      fill={color}
      fontSize={14}
      fontFamily={FONT_FAMILY}
      fontWeight={600}
      opacity={opacity}
    >
      {label}
    </text>
  );
};

export const ForkingLines: React.FC = () => {
  const frame = useCurrentFrame();

  // Base lines draw in over frames 0–90
  const baseProgress = interpolate(frame, [0, 80], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Fork progress: starts at FORK_START, animates over FORK_ANIM_DURATION
  const forkProgress = interpolate(
    frame,
    [FORK_START, FORK_START + FORK_ANIM_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Fork label fade
  const forkLabelOpacity = interpolate(
    frame,
    [FORK_START + FORK_ANIM_DURATION - 30, FORK_START + FORK_ANIM_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Debt area opacity
  const debtOpacity = interpolate(frame, [20, 60], [0, 0.6], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  const generatePath = dataToSmoothPath(GENERATE_LINE_DATA);
  const patchPath = dataToSmoothPath(PATCH_LINE_DATA);
  const smallPath = dataToSmoothPath(SMALL_CODEBASE_DATA);
  const largePath = dataToSmoothPath(LARGE_CODEBASE_DATA);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Debt area fill */}
      <DebtArea opacity={debtOpacity} />

      {/* Generate line (blue, background context) */}
      <AnimatedPath
        d={generatePath}
        color={BLUE_LINE_COLOR}
        strokeWidth={2.5}
        progress={baseProgress}
      />

      {/* Patch line up to fork point (amber) */}
      <AnimatedPath
        d={patchPath}
        color={AMBER_LINE_COLOR}
        strokeWidth={3}
        progress={baseProgress}
      />

      {/* Generate line label */}
      {baseProgress > 0.8 && (
        <text
          x={xToPixel(2026) + 12}
          y={yToPixel(0.03) + 5}
          fill={BLUE_LINE_COLOR}
          fontSize={13}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={interpolate(baseProgress, [0.8, 1], [0, 0.85], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Generate
        </text>
      )}

      {/* Patch line label */}
      {baseProgress > 0.8 && forkProgress < 0.1 && (
        <text
          x={xToPixel(2020) + 12}
          y={yToPixel(0.48) - 12}
          fill={AMBER_LINE_COLOR}
          fontSize={13}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={interpolate(baseProgress, [0.8, 1], [0, 0.85], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        >
          Patch
        </text>
      )}

      {/* Small codebase fork (green) */}
      {forkProgress > 0 && (
        <>
          <AnimatedPath
            d={smallPath}
            color={GREEN_LINE_COLOR}
            strokeWidth={3}
            progress={forkProgress}
          />
          <ForkLabel
            data={SMALL_CODEBASE_DATA}
            label="Small codebase"
            color={GREEN_LINE_COLOR}
            opacity={forkLabelOpacity}
          />
        </>
      )}

      {/* Large codebase fork (red) */}
      {forkProgress > 0 && (
        <>
          <AnimatedPath
            d={largePath}
            color={RED_LINE_COLOR}
            strokeWidth={3}
            progress={forkProgress}
          />
          <ForkLabel
            data={LARGE_CODEBASE_DATA}
            label="Large codebase"
            color={RED_LINE_COLOR}
            opacity={forkLabelOpacity}
          />
        </>
      )}

      {/* Fork point dot */}
      {forkProgress > 0 && (
        <circle
          cx={xToPixel(2020)}
          cy={yToPixel(0.48)}
          r={5}
          fill={AMBER_LINE_COLOR}
          opacity={interpolate(forkProgress, [0, 0.15], [0, 1], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          })}
        />
      )}
    </svg>
  );
};

export default ForkingLines;
