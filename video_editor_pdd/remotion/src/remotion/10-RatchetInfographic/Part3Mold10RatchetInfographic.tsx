import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { RatchetChart } from "./RatchetChart";
import { PawlIcon } from "./PawlIcon";
import { MilestoneLabels } from "./MilestoneLabels";
import {
  AXIS_DRAW_START,
  AXIS_DRAW_END,
  YLABEL_FADE_START,
  YLABEL_FADE_END,
  TIMELINE_Y,
  TIMELINE_X_START,
  TIMELINE_WIDTH,
  TIMELINE_COLOR,
  SLATE_400,
  FADEOUT_START,
  FADEOUT_END,
  CHART_X,
  CHART_Y,
  CHART_H,
  BG_COLOR,
} from "./constants";

export const defaultPart3Mold10RatchetInfographicProps = {};

export const Part3Mold10RatchetInfographic: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall fade envelope: fully visible from frame 0, fade out at end
  const overallOpacity = interpolate(
    frame,
    [0, 1, FADEOUT_START, FADEOUT_END],
    [1, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    }
  );

  // Timeline axis draw-in (width 0 → 100%)
  const axisWidth = interpolate(
    frame,
    [AXIS_DRAW_START, AXIS_DRAW_END],
    [0, TIMELINE_WIDTH],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Y-axis label opacity
  const yLabelOpacity = interpolate(
    frame,
    [YLABEL_FADE_START, YLABEL_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part3_mold.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay */}
      <AbsoluteFill style={{ opacity: overallOpacity }}>
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: "absolute", top: 0, left: 0 }}
        >
          {/* Timeline horizontal axis */}
          <line
            x1={TIMELINE_X_START}
            y1={TIMELINE_Y}
            x2={TIMELINE_X_START + axisWidth}
            y2={TIMELINE_Y}
            stroke={TIMELINE_COLOR}
            strokeWidth={2}
          />

          {/* Y-axis label "Mold Precision" rotated */}
          <text
            x={CHART_X - 40}
            y={CHART_Y + CHART_H / 2}
            fill={SLATE_400}
            fontSize={18}
            fontFamily="Inter, sans-serif"
            fontWeight={500}
            textAnchor="middle"
            transform={`rotate(-90, ${CHART_X - 40}, ${CHART_Y + CHART_H / 2})`}
            opacity={yLabelOpacity}
          >
            Mold Precision
          </text>
        </svg>

        {/* Test bars + ratchet stepped line */}
        <RatchetChart />

        {/* Pawl icon sliding along line */}
        <PawlIcon />

        {/* Generation milestone labels */}
        <MilestoneLabels />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part3Mold10RatchetInfographic;
