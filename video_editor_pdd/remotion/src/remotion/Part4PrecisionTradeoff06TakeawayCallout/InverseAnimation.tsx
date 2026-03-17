import React from 'react';
import { Easing, interpolate } from 'remotion';
import {
  AMBER,
  PROMPT_COLOR,
  ARROW_COLOR,
  PROMPT_START_LINES,
  PROMPT_END_LINES,
  WALL_START_COUNT,
  WALL_END_COUNT,
  MINI_ANIM_DURATION,
  WALL_STAGGER_FRAMES,
} from './constants';
import { PromptDocument } from './PromptDocument';
import { WallIcon } from './WallIcon';

interface InverseAnimationProps {
  /** Frame offset within the parent Sequence (0 = first frame of this animation) */
  localFrame: number;
}

/**
 * The mini "prompt shrinks / walls multiply" inverse-relationship animation.
 * localFrame counts from 0 at the start of this animation's Sequence.
 */
export const InverseAnimation: React.FC<InverseAnimationProps> = ({
  localFrame,
}) => {
  // Fade in the whole cluster
  const fadeIn = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Prompt line count shrinks
  const promptLines = interpolate(
    localFrame,
    [0, MINI_ANIM_DURATION],
    [PROMPT_START_LINES, PROMPT_END_LINES],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  // Wall count grows — stagger-based: each wall appears WALL_STAGGER_FRAMES apart
  const visibleWalls: number[] = [];
  for (let i = 0; i < WALL_END_COUNT; i++) {
    if (i < WALL_START_COUNT) {
      visibleWalls.push(1);
    } else {
      const wallIndex = i - WALL_START_COUNT;
      const wallAppearFrame = wallIndex * WALL_STAGGER_FRAMES;
      const wallOpacity = interpolate(
        localFrame,
        [wallAppearFrame, wallAppearFrame + 8],
        [0, 1],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.out(Easing.quad),
        },
      );
      visibleWalls.push(wallOpacity);
    }
  }

  // Layout constants
  const promptW = 40;
  const promptH = 60;
  const arrowWidth = 80;

  // Arrange walls in a grid
  const wallSize = 14;
  const wallGap = 4;
  const wallsPerRow = 5;

  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity: fadeIn,
        gap: 24,
      }}
    >
      {/* Prompt document — shrinks */}
      <div style={{ width: promptW, height: promptH, flexShrink: 0 }}>
        <PromptDocument
          lineCount={promptLines}
          width={promptW}
          height={promptH}
          color={PROMPT_COLOR}
        />
      </div>

      {/* Double-headed arrow */}
      <svg width={arrowWidth} height={20} viewBox={`0 0 ${arrowWidth} 20`}>
        <defs>
          <marker
            id="arrowLeft"
            markerWidth="6"
            markerHeight="6"
            refX="6"
            refY="3"
            orient="auto"
          >
            <path d="M6,0 L0,3 L6,6" fill={ARROW_COLOR} opacity={0.5} />
          </marker>
          <marker
            id="arrowRight"
            markerWidth="6"
            markerHeight="6"
            refX="0"
            refY="3"
            orient="auto"
          >
            <path d="M0,0 L6,3 L0,6" fill={ARROW_COLOR} opacity={0.5} />
          </marker>
        </defs>
        <line
          x1={8}
          y1={10}
          x2={arrowWidth - 8}
          y2={10}
          stroke={ARROW_COLOR}
          strokeWidth={1.5}
          opacity={0.5}
          markerStart="url(#arrowLeft)"
          markerEnd="url(#arrowRight)"
        />
      </svg>

      {/* Wall cluster — grows */}
      <div
        style={{
          display: 'flex',
          flexWrap: 'wrap',
          width: wallsPerRow * (wallSize + wallGap),
          gap: wallGap,
        }}
      >
        {visibleWalls.map((opacity, i) =>
          opacity > 0 ? (
            <div key={i} style={{ opacity }}>
              <WallIcon size={wallSize} color={AMBER} />
            </div>
          ) : null,
        )}
      </div>
    </div>
  );
};

export default InverseAnimation;
