import React from "react";
import {
  AbsoluteFill,
  Sequence,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import { BlueprintGrid } from "./BlueprintGrid";
import { FlowNode } from "./FlowNode";
import { DrawLine, DrawArrow } from "./DrawLine";
import { MiniMoldAddWall, MiniMoldReshape } from "./MiniMold";
import {
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  ROOT_BORDER_COLOR,
  ROOT_TEXT_COLOR,
  ROOT_NODE_WIDTH,
  ROOT_NODE_HEIGHT,
  ROOT_NODE_X,
  ROOT_NODE_Y,
  LEFT_BRANCH_COLOR,
  RIGHT_BRANCH_COLOR,
  ACTION_TEXT_COLOR,
  LEFT_FORK_X,
  LEFT_FORK_Y,
  RIGHT_FORK_X,
  RIGHT_FORK_Y,
  LEFT_NODE_WIDTH,
  LEFT_NODE_HEIGHT,
  LEFT_NODE_X,
  LEFT_NODE_Y,
  RIGHT_NODE_WIDTH,
  RIGHT_NODE_HEIGHT,
  RIGHT_NODE_X,
  RIGHT_NODE_Y,
  LEFT_ACTION_Y,
  RIGHT_ACTION_Y,
  LEFT_MOLD_X,
  LEFT_MOLD_Y,
  RIGHT_MOLD_X,
  RIGHT_MOLD_Y,
  LEFT_RESOLUTION_Y,
  RIGHT_RESOLUTION_Y,
  TOTAL_FRAMES,
  ROOT_FADE_START,
  ROOT_FADE_DURATION,
  FORK_DRAW_START,
  FORK_DRAW_DURATION,
  LEFT_NODE_START,
  LEFT_NODE_FADE_DURATION,
  LEFT_ACTION_START,
  LEFT_ACTION_FADE_DURATION,
  RIGHT_NODE_START,
  RIGHT_NODE_FADE_DURATION,
  RIGHT_ACTION_START,
  RIGHT_ACTION_FADE_DURATION,
  LEFT_MOLD_ANIM_START,
  RIGHT_MOLD_ANIM_START,
  MOLD_ANIM_DURATION,
  LEFT_ARROW_START,
  RIGHT_ARROW_START,
  ARROW_DRAW_DURATION,
} from "./constants";

export const defaultPart3MoldParts08BugForkRoadProps = {};

const ActionText: React.FC<{
  text: string;
  x: number;
  y: number;
  fadeStart: number;
  fadeDuration: number;
  color: string;
}> = ({ text, x, y, fadeStart, fadeDuration, color }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [fadeStart, fadeStart + fadeDuration],
    [0, 0.85],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: x - 120,
        top: y,
        width: 240,
        textAlign: "center",
        fontFamily: "Inter, sans-serif",
        fontSize: 14,
        fontWeight: 400,
        color,
        opacity,
        lineHeight: 1.4,
      }}
    >
      {text}
    </div>
  );
};

const ResolutionNode: React.FC<{
  x: number;
  y: number;
  color: string;
  fadeStart: number;
}> = ({ x, y, color, fadeStart }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeStart + 20], [0, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: x - 50,
        top: y - 15,
        width: 100,
        height: 30,
        borderRadius: 15,
        border: `1.5px solid ${color}`,
        backgroundColor: "#1E1E2E",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 12,
          fontWeight: 500,
          color,
        }}
      >
        Resolved
      </span>
    </div>
  );
};

const Divider: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [270, 300], [0, 0.8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 960 - 1,
        top: 340,
        width: 2,
        height: 400,
        backgroundColor: "#94A3B8",
        opacity: opacity * 0.15,
      }}
    />
  );
};

const DistinctionLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [300, 330], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        bottom: 100,
        left: 0,
        width: 1920,
        textAlign: "center",
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: "Inter, sans-serif",
          fontSize: 18,
          fontWeight: 500,
          color: "#94A3B8",
          letterSpacing: "1px",
        }}
      >
        PDD separates{" "}
        <span style={{ color: LEFT_BRANCH_COLOR, fontWeight: 600 }}>
          code failures
        </span>{" "}
        from{" "}
        <span style={{ color: RIGHT_BRANCH_COLOR, fontWeight: 600 }}>
          specification failures
        </span>
      </span>
    </div>
  );
};

export const Part3MoldParts08BugForkRoad: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        {/* Blueprint grid background */}
        <BlueprintGrid
          spacing={GRID_SPACING}
          color={GRID_COLOR}
          opacity={GRID_OPACITY}
        />

        {/* Center divider (subtle) */}
        <Divider />

        {/* Starting node: "Bug found" */}
        <FlowNode
          text="Bug found"
          borderColor={ROOT_BORDER_COLOR}
          textColor={ROOT_TEXT_COLOR}
          x={ROOT_NODE_X}
          y={ROOT_NODE_Y}
          width={ROOT_NODE_WIDTH}
          height={ROOT_NODE_HEIGHT}
          fadeStartFrame={ROOT_FADE_START}
          fadeDuration={ROOT_FADE_DURATION}
          fontSize={16}
          fontWeight={700}
        />

        {/* Fork lines diverging */}
        <DrawLine
          fromX={ROOT_NODE_X}
          fromY={ROOT_NODE_Y + ROOT_NODE_HEIGHT / 2}
          toX={LEFT_FORK_X}
          toY={LEFT_FORK_Y}
          color={LEFT_BRANCH_COLOR}
          strokeWidth={2}
          drawStartFrame={FORK_DRAW_START}
          drawDuration={FORK_DRAW_DURATION}
        />
        <DrawLine
          fromX={ROOT_NODE_X}
          fromY={ROOT_NODE_Y + ROOT_NODE_HEIGHT / 2}
          toX={RIGHT_FORK_X}
          toY={RIGHT_FORK_Y}
          color={RIGHT_BRANCH_COLOR}
          strokeWidth={2}
          drawStartFrame={FORK_DRAW_START}
          drawDuration={FORK_DRAW_DURATION}
        />

        {/* Left branch: Code bug */}
        <FlowNode
          text="Code bug"
          borderColor={LEFT_BRANCH_COLOR}
          textColor={LEFT_BRANCH_COLOR}
          x={LEFT_NODE_X}
          y={LEFT_NODE_Y}
          width={LEFT_NODE_WIDTH}
          height={LEFT_NODE_HEIGHT}
          fadeStartFrame={LEFT_NODE_START}
          fadeDuration={LEFT_NODE_FADE_DURATION}
        />
        <ActionText
          text="Add a wall"
          x={LEFT_NODE_X}
          y={LEFT_ACTION_Y}
          fadeStart={LEFT_ACTION_START}
          fadeDuration={LEFT_ACTION_FADE_DURATION}
          color={ACTION_TEXT_COLOR}
        />

        {/* Left mini mold animation */}
        <MiniMoldAddWall
          x={LEFT_MOLD_X}
          y={LEFT_MOLD_Y}
          color={LEFT_BRANCH_COLOR}
          animStartFrame={LEFT_MOLD_ANIM_START}
          animDuration={MOLD_ANIM_DURATION}
        />

        {/* Left resolution arrow */}
        <DrawArrow
          fromX={LEFT_NODE_X}
          fromY={LEFT_MOLD_Y + 50}
          toX={LEFT_NODE_X}
          toY={LEFT_RESOLUTION_Y - 20}
          color={LEFT_BRANCH_COLOR}
          strokeWidth={2}
          drawStartFrame={LEFT_ARROW_START}
          drawDuration={ARROW_DRAW_DURATION}
          arrowOpacity={0.3}
        />

        {/* Left resolution node */}
        <ResolutionNode
          x={LEFT_NODE_X}
          y={LEFT_RESOLUTION_Y}
          color={LEFT_BRANCH_COLOR}
          fadeStart={LEFT_ARROW_START + ARROW_DRAW_DURATION}
        />

        {/* Right branch: Prompt defect */}
        <FlowNode
          text="Prompt defect"
          borderColor={RIGHT_BRANCH_COLOR}
          textColor={RIGHT_BRANCH_COLOR}
          x={RIGHT_NODE_X}
          y={RIGHT_NODE_Y}
          width={RIGHT_NODE_WIDTH}
          height={RIGHT_NODE_HEIGHT}
          fadeStartFrame={RIGHT_NODE_START}
          fadeDuration={RIGHT_NODE_FADE_DURATION}
        />
        <ActionText
          text="Change the mold itself"
          x={RIGHT_NODE_X}
          y={RIGHT_ACTION_Y}
          fadeStart={RIGHT_ACTION_START}
          fadeDuration={RIGHT_ACTION_FADE_DURATION}
          color={ACTION_TEXT_COLOR}
        />

        {/* Right mini mold animation */}
        <MiniMoldReshape
          x={RIGHT_MOLD_X}
          y={RIGHT_MOLD_Y}
          color={RIGHT_BRANCH_COLOR}
          animStartFrame={RIGHT_MOLD_ANIM_START}
          animDuration={MOLD_ANIM_DURATION}
        />

        {/* Right resolution arrow */}
        <DrawArrow
          fromX={RIGHT_NODE_X}
          fromY={RIGHT_MOLD_Y + 50}
          toX={RIGHT_NODE_X}
          toY={RIGHT_RESOLUTION_Y - 20}
          color={RIGHT_BRANCH_COLOR}
          strokeWidth={2}
          drawStartFrame={RIGHT_ARROW_START}
          drawDuration={ARROW_DRAW_DURATION}
          arrowOpacity={0.3}
        />

        {/* Right resolution node */}
        <ResolutionNode
          x={RIGHT_NODE_X}
          y={RIGHT_RESOLUTION_Y}
          color={RIGHT_BRANCH_COLOR}
          fadeStart={RIGHT_ARROW_START + ARROW_DRAW_DURATION}
        />

        {/* Distinction label at bottom */}
        <DistinctionLabel />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part3MoldParts08BugForkRoad;
