import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  BACKGROUND_COLOR,
  ROOT_X,
  ROOT_Y,
  ROOT_WIDTH,
  ROOT_HEIGHT,
  RED_ACCENT,
  BLUE_BRANCH,
  AMBER_BRANCH,
  LEFT_BRANCH_X,
  RIGHT_BRANCH_X,
  BRANCH_NODE_Y,
  FORK_TARGET_Y,
  LEFT_NODE_WIDTH,
  RIGHT_NODE_WIDTH,
  BRANCH_NODE_HEIGHT,
  ACTION_TEXT_COLOR,
  ACTION_TEXT_Y,
  MINI_MOLD_Y,
  ROOT_FADE_START,
  ROOT_FADE_DURATION,
  FORK_DRAW_START,
  FORK_DRAW_DURATION,
  LEFT_NODE_START,
  LEFT_ACTION_START,
  LEFT_ACTION_DURATION,
  RIGHT_NODE_START,
  RIGHT_ACTION_START,
  RIGHT_ACTION_DURATION,
  LEFT_MOLD_ANIM_START,
  RIGHT_MOLD_ANIM_START,
  MOLD_ANIM_DURATION,
  RESOLUTION_Y,
} from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { FlowNode } from './FlowNode';
import { DrawLine } from './DrawLine';
import { MiniMold } from './MiniMold';
import { ResolutionArrow } from './ResolutionArrow';

export const defaultPart3MoldParts08BugForkRoadProps = {};

export const Part3MoldParts08BugForkRoad: React.FC = () => {
  const frame = useCurrentFrame();

  // Action text fade-in helpers
  const leftActionOpacity = interpolate(
    frame,
    [LEFT_ACTION_START, LEFT_ACTION_START + LEFT_ACTION_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const rightActionOpacity = interpolate(
    frame,
    [RIGHT_ACTION_START, RIGHT_ACTION_START + RIGHT_ACTION_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Final fade for transition readiness (frames 480-540)
  const finalFade = interpolate(frame, [480, 540], [1, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        opacity: finalFade,
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Starting node: "Bug found" */}
      <FlowNode
        text="Bug found"
        borderColor={RED_ACCENT}
        textColor={RED_ACCENT}
        x={ROOT_X}
        y={ROOT_Y}
        width={ROOT_WIDTH}
        height={ROOT_HEIGHT}
        fadeStartFrame={ROOT_FADE_START}
        fadeDuration={ROOT_FADE_DURATION}
        fontSize={16}
        fontWeight={700}
      />

      {/* Fork lines */}
      <DrawLine
        fromX={ROOT_X}
        fromY={ROOT_Y + ROOT_HEIGHT / 2}
        toX={LEFT_BRANCH_X}
        toY={FORK_TARGET_Y}
        color={BLUE_BRANCH}
        strokeWidth={2}
        drawStartFrame={FORK_DRAW_START}
        drawDuration={FORK_DRAW_DURATION}
      />
      <DrawLine
        fromX={ROOT_X}
        fromY={ROOT_Y + ROOT_HEIGHT / 2}
        toX={RIGHT_BRANCH_X}
        toY={FORK_TARGET_Y}
        color={AMBER_BRANCH}
        strokeWidth={2}
        drawStartFrame={FORK_DRAW_START}
        drawDuration={FORK_DRAW_DURATION}
      />

      {/* Left branch: "Code bug" node */}
      <FlowNode
        text="Code bug"
        borderColor={BLUE_BRANCH}
        textColor={BLUE_BRANCH}
        x={LEFT_BRANCH_X}
        y={BRANCH_NODE_Y}
        width={LEFT_NODE_WIDTH}
        height={BRANCH_NODE_HEIGHT}
        fadeStartFrame={LEFT_NODE_START}
        fadeDuration={ROOT_FADE_DURATION}
        fontSize={14}
        fontWeight={600}
      />

      {/* Left action text: "Add a wall" */}
      <div
        style={{
          position: 'absolute',
          left: LEFT_BRANCH_X - 90,
          top: ACTION_TEXT_Y,
          width: 180,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: ACTION_TEXT_COLOR,
          opacity: leftActionOpacity,
        }}
      >
        Add a wall
      </div>

      {/* Left mini mold */}
      <MiniMold
        action="addWall"
        x={LEFT_BRANCH_X}
        y={MINI_MOLD_Y}
        accentColor={BLUE_BRANCH}
        animStartFrame={LEFT_MOLD_ANIM_START}
        animDuration={MOLD_ANIM_DURATION}
      />

      {/* Left resolution arrow */}
      <ResolutionArrow
        x={LEFT_BRANCH_X}
        fromY={MINI_MOLD_Y + 55}
        toY={RESOLUTION_Y}
        color={BLUE_BRANCH}
        fadeStartFrame={LEFT_MOLD_ANIM_START + MOLD_ANIM_DURATION}
      />

      {/* Right branch: "Prompt defect" node */}
      <FlowNode
        text="Prompt defect"
        borderColor={AMBER_BRANCH}
        textColor={AMBER_BRANCH}
        x={RIGHT_BRANCH_X}
        y={BRANCH_NODE_Y}
        width={RIGHT_NODE_WIDTH}
        height={BRANCH_NODE_HEIGHT}
        fadeStartFrame={RIGHT_NODE_START}
        fadeDuration={ROOT_FADE_DURATION}
        fontSize={14}
        fontWeight={600}
      />

      {/* Right action text: "Change the mold itself" */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_BRANCH_X - 110,
          top: ACTION_TEXT_Y,
          width: 220,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: ACTION_TEXT_COLOR,
          opacity: rightActionOpacity,
        }}
      >
        Change the mold itself
      </div>

      {/* Right mini mold */}
      <MiniMold
        action="reshapeNozzle"
        x={RIGHT_BRANCH_X}
        y={MINI_MOLD_Y}
        accentColor={AMBER_BRANCH}
        animStartFrame={RIGHT_MOLD_ANIM_START}
        animDuration={MOLD_ANIM_DURATION}
      />

      {/* Right resolution arrow */}
      <ResolutionArrow
        x={RIGHT_BRANCH_X}
        fromY={MINI_MOLD_Y + 55}
        toY={RESOLUTION_Y}
        color={AMBER_BRANCH}
        fadeStartFrame={RIGHT_MOLD_ANIM_START + MOLD_ANIM_DURATION}
      />

      {/* Distinction label at bottom center */}
      <DistinctionLabel frame={frame} />
    </AbsoluteFill>
  );
};

const DistinctionLabel: React.FC<{ frame: number }> = ({ frame }) => {
  const opacity = interpolate(frame, [270, 300], [0, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const y = interpolate(frame, [270, 300], [10, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 100,
        left: 0,
        right: 0,
        textAlign: 'center',
        opacity,
        transform: `translateY(${y}px)`,
      }}
    >
      {/* Divider line */}
      <div
        style={{
          width: 400,
          height: 2,
          backgroundColor: '#94A3B8',
          opacity: 0.75,
          margin: '0 auto 16px auto',
        }}
      />
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 18,
          fontWeight: 500,
          color: '#E2E8F0',
          opacity: 0.85,
        }}
      >
        PDD separates code failures from specification failures
      </span>
    </div>
  );
};

export default Part3MoldParts08BugForkRoad;
