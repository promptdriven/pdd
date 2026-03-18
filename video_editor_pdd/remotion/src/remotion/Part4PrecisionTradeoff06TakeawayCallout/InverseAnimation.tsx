import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  AMBER,
  PROMPT_BLUE,
  ARROW_COLOR,
  MINI_ANIM_START,
  MINI_ANIM_DURATION,
  PROMPT_START_LINES,
  PROMPT_END_LINES,
  WALL_START_COUNT,
  WALL_END_COUNT,
  WALL_STAGGER,
  WIDTH,
} from './constants';

/** Prompt document icon that shrinks its line count */
const PromptDoc: React.FC<{ lineCount: number; color: string }> = ({
  lineCount,
  color,
}) => {
  const docW = 40;
  const docH = 60;
  const maxLines = PROMPT_START_LINES;
  const lineH = 2;
  const gap = (docH - 8) / maxLines;

  return (
    <div style={{ width: docW, height: docH, position: 'relative' }}>
      {/* Doc background */}
      <div
        style={{
          width: docW,
          height: docH,
          borderRadius: 3,
          border: `1px solid ${color}`,
          opacity: 0.6,
          position: 'absolute',
          top: 0,
          left: 0,
        }}
      />
      {/* Lines */}
      {Array.from({ length: Math.round(lineCount) }).map((_, i) => (
        <div
          key={i}
          style={{
            position: 'absolute',
            top: 4 + i * gap,
            left: 5,
            width: docW - 10 - (i % 3 === 2 ? 8 : 0),
            height: lineH,
            backgroundColor: color,
            opacity: 0.7,
            borderRadius: 1,
          }}
        />
      ))}
    </div>
  );
};

/** Single wall brick icon */
const WallBrick: React.FC<{ color: string; opacity: number }> = ({
  color,
  opacity,
}) => (
  <svg width={14} height={18} viewBox="0 0 10 14" style={{ opacity }}>
    <rect x="0" y="0" width="10" height="3" rx="0.5" fill={color} />
    <rect x="0" y="4" width="4.5" height="3" rx="0.5" fill={color} />
    <rect x="5.5" y="4" width="4.5" height="3" rx="0.5" fill={color} />
    <rect x="0" y="8" width="10" height="3" rx="0.5" fill={color} />
    <rect x="0" y="12" width="4.5" height="2" rx="0.5" fill={color} />
    <rect x="5.5" y="12" width="4.5" height="2" rx="0.5" fill={color} />
  </svg>
);

export const InverseAnimation: React.FC = () => {
  const frame = useCurrentFrame();
  const localFrame = frame - MINI_ANIM_START;

  if (localFrame < 0) return null;

  const progress = interpolate(localFrame, [0, MINI_ANIM_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  const lineCount = interpolate(
    progress,
    [0, 1],
    [PROMPT_START_LINES, PROMPT_END_LINES]
  );

  const wallCount = Math.round(
    interpolate(progress, [0, 1], [WALL_START_COUNT, WALL_END_COUNT])
  );

  // Fade in the entire animation
  const fadeIn = interpolate(localFrame, [0, 10], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const cols = 5;
  const wallSpacingX = 18;
  const wallSpacingY = 22;

  return (
    <div
      style={{
        position: 'absolute',
        top: 660,
        left: 0,
        width: WIDTH,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        gap: 60,
        opacity: fadeIn,
      }}
    >
      {/* Prompt document */}
      <PromptDoc lineCount={lineCount} color={PROMPT_BLUE} />

      {/* Arrow */}
      <svg width={80} height={20} viewBox="0 0 80 20">
        <line
          x1={5}
          y1={8}
          x2={75}
          y2={8}
          stroke={ARROW_COLOR}
          strokeWidth={1}
          opacity={0.3}
        />
        <line
          x1={5}
          y1={12}
          x2={75}
          y2={12}
          stroke={ARROW_COLOR}
          strokeWidth={1}
          opacity={0.3}
        />
        {/* Left arrowhead */}
        <polygon points="5,10 12,5 12,15" fill={ARROW_COLOR} opacity={0.3} />
        {/* Right arrowhead */}
        <polygon points="75,10 68,5 68,15" fill={ARROW_COLOR} opacity={0.3} />
      </svg>

      {/* Wall cluster */}
      <div
        style={{
          display: 'flex',
          flexWrap: 'wrap',
          width: cols * wallSpacingX,
          gap: 2,
          alignItems: 'flex-start',
        }}
      >
        {Array.from({ length: wallCount }).map((_, i) => {
          const wallLocalDelay = i * WALL_STAGGER;
          const wallOpacity = interpolate(
            localFrame,
            [wallLocalDelay, wallLocalDelay + 8],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );
          return (
            <WallBrick key={i} color={AMBER} opacity={wallOpacity} />
          );
        })}
      </div>
    </div>
  );
};

export default InverseAnimation;
