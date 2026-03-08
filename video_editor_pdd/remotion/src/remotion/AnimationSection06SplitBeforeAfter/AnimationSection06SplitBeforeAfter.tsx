import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS,
  COLORS,
  TYPOGRAPHY,
  POSITIONS,
  ANIMATION_TIMING,
} from './constants';
import { FilmReelIcon } from './FilmReelIcon';
import { CodeBracketIcon } from './CodeBracketIcon';
import { StaticBars } from './StaticBars';
import { FloatingCodeTokens } from './FloatingCodeTokens';
import { DividerLine } from './DividerLine';

export const AnimationSection06SplitBeforeAfter: React.FC = () => {
  const frame = useCurrentFrame();

  // Left panel slide in from left
  const leftOffsetX = interpolate(
    frame,
    [ANIMATION_TIMING.leftSlideStart, ANIMATION_TIMING.leftSlideEnd],
    [-CANVAS.dividerX, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Right panel slide in from right
  const rightOffsetX = interpolate(
    frame,
    [ANIMATION_TIMING.rightSlideStart, ANIMATION_TIMING.rightSlideEnd],
    [CANVAS.dividerX, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Before label fade
  const beforeLabelOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.beforeLabelStart, ANIMATION_TIMING.beforeLabelEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // After label fade
  const afterLabelOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.afterLabelStart, ANIMATION_TIMING.afterLabelEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Animated gradient hue shift for right panel
  const hueShift = interpolate(frame, [0, ANIMATION_TIMING.totalDuration], [0, 20], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* LEFT PANEL — "Before" */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.dividerX,
          height: CANVAS.height,
          backgroundColor: COLORS.leftPanel,
          transform: `translateX(${leftOffsetX}px)`,
          overflow: 'hidden',
        }}
      >
        {/* Before label */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.leftLabelX,
            top: POSITIONS.labelY,
            opacity: beforeLabelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: TYPOGRAPHY.label.fontFamily,
              fontSize: TYPOGRAPHY.label.fontSize,
              fontWeight: TYPOGRAPHY.label.fontWeight,
              color: COLORS.beforeLabel,
            }}
          >
            Before
          </span>
        </div>

        {/* Film reel icon */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.leftLabelX,
            top: POSITIONS.iconY,
            opacity: beforeLabelOpacity,
          }}
        >
          <FilmReelIcon />
        </div>

        {/* Static placeholder bars */}
        <StaticBars />
      </div>

      {/* Divider line */}
      <DividerLine />

      {/* RIGHT PANEL — "After" */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.dividerX,
          top: 0,
          width: CANVAS.dividerX,
          height: CANVAS.height,
          background: `linear-gradient(135deg, hsl(${220 + hueShift}, 73%, 33%) 0%, ${COLORS.rightGradientEnd} 100%)`,
          transform: `translateX(${rightOffsetX}px)`,
          overflow: 'hidden',
        }}
      >
        {/* After label */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.rightLabelX - CANVAS.dividerX,
            top: POSITIONS.labelY,
            opacity: afterLabelOpacity,
          }}
        >
          <span
            style={{
              fontFamily: TYPOGRAPHY.label.fontFamily,
              fontSize: TYPOGRAPHY.label.fontSize,
              fontWeight: TYPOGRAPHY.label.fontWeight,
              color: COLORS.afterLabel,
            }}
          >
            After
          </span>
        </div>

        {/* Code bracket icon */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.rightLabelX - CANVAS.dividerX,
            top: POSITIONS.iconY,
            opacity: afterLabelOpacity,
          }}
        >
          <CodeBracketIcon />
        </div>

        {/* Floating code tokens */}
        <FloatingCodeTokens />
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06SplitBeforeAfterProps = {};

export default AnimationSection06SplitBeforeAfter;
