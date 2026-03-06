import React from "react";
import {
  AbsoluteFill,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { TimelineTrack } from "./TimelineTrack";
import { TimelineNode } from "./TimelineNode";
import { ConclusionText } from "./ConclusionText";
import {
  PANEL_X,
  PANEL_Y,
  PANEL_W,
  PANEL_H,
  PANEL_RADIUS,
  PANEL_BG,
  PANEL_FADE_END,
  TRACK_Y,
  NODES,
  NODE1_DIM_START,
  NODE1_DIM_END,
  NODE2_DIM_START,
  NODE2_DIM_END,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

export const defaultPart2ParadigmShift07HdlTimelineProps = {};

export const Part2ParadigmShift07HdlTimeline: React.FC = () => {
  const frame = useCurrentFrame();

  // Backing panel opacity
  const panelOpacity = interpolate(
    frame,
    [0, PANEL_FADE_END, FADEOUT_START, FADEOUT_END],
    [0, 0.8, 0.8, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Global fade out for all elements
  const globalOpacity = interpolate(
    frame,
    [FADEOUT_START, FADEOUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Node 1 dims when node 2 activates
  const node1Opacity = interpolate(
    frame,
    [NODE1_DIM_START, NODE1_DIM_END],
    [1, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // Node 2 dims when node 3 activates
  const node2Opacity = interpolate(
    frame,
    [NODE2_DIM_START, NODE2_DIM_END],
    [1, 0.7],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const dimOpacities = [node1Opacity, node2Opacity, 1];

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part2_paradigm_shift.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Overlay content */}
      <AbsoluteFill>
        {/* Backing panel */}
        <div
          style={{
            position: "absolute",
            left: PANEL_X,
            top: PANEL_Y,
            width: PANEL_W,
            height: PANEL_H,
            borderRadius: PANEL_RADIUS,
            backgroundColor: PANEL_BG,
            backdropFilter: "blur(10px)",
            WebkitBackdropFilter: "blur(10px)",
            opacity: panelOpacity,
          }}
        />

        {/* Timeline track */}
        <TimelineTrack globalOpacity={globalOpacity} />

        {/* Timeline nodes */}
        {NODES.map((node, i) => (
          <TimelineNode
            key={node.year}
            x={node.x}
            y={TRACK_Y}
            icon={node.icon}
            year={node.year}
            descriptor={node.descriptor}
            color={node.color}
            activateFrame={node.activateFrame}
            dimOpacity={dimOpacities[i]}
            globalOpacity={globalOpacity}
          />
        ))}

        {/* Conclusion text with underline */}
        <ConclusionText globalOpacity={globalOpacity} />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift07HdlTimeline;
