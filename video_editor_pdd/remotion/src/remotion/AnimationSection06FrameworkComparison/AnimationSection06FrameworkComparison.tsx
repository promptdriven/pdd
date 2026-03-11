import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS,
  COLORS,
  TYPOGRAPHY,
  POSITIONS,
  DIMENSIONS,
  ANIMATION_TIMING,
  RIGHT_PANEL_OPACITY,
} from './constants';
import { MiniBarChart } from './MiniBarChart';
import { FilmReelIcon } from './FilmReelIcon';
import { VerticalDivider } from './VerticalDivider';

export const AnimationSection06FrameworkComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Left panel fade-in (frame 0-20)
  const leftOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.leftFadeStart, ANIMATION_TIMING.leftFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Left label slide down (frame 0-20)
  const leftLabelY = interpolate(
    frame,
    [ANIMATION_TIMING.leftFadeStart, ANIMATION_TIMING.leftFadeEnd],
    [POSITIONS.labelSlideStartY, POSITIONS.labelSlideEndY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Right panel fade-in (frame 25-45, to 60% opacity)
  const rightOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.rightFadeStart, ANIMATION_TIMING.rightFadeEnd],
    [0, RIGHT_PANEL_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Right label slide down (frame 25-45)
  const rightLabelY = interpolate(
    frame,
    [ANIMATION_TIMING.rightFadeStart, ANIMATION_TIMING.rightFadeEnd],
    [POSITIONS.labelSlideStartY, POSITIONS.labelSlideEndY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Glow border pulse (frame 40-60): 0.2 → 0.6 → 0.2
  const glowOpacity = interpolate(
    frame,
    [
      ANIMATION_TIMING.glowPulseStart,
      ANIMATION_TIMING.glowPulseMid,
      ANIMATION_TIMING.glowPulseEnd,
    ],
    [0.2, 0.6, 0.2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <AbsoluteFill
      style={{
        width: CANVAS.width,
        height: CANVAS.height,
        backgroundColor: '#FF0000',
      }}
    >
      {/* Left panel — Remotion */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.halfWidth,
          height: CANVAS.height,
          backgroundColor: COLORS.leftBackground,
          opacity: leftOpacity,
          overflow: 'hidden',
        }}
      >
        {/* Glow border (inner) */}
        <div
          style={{
            position: 'absolute',
            inset: 0,
            border: `${DIMENSIONS.glowBorderWidth}px solid ${COLORS.glowBorder}`,
            opacity: frame >= ANIMATION_TIMING.glowPulseStart ? glowOpacity : 0.2,
            boxShadow: `inset 0 0 20px ${COLORS.glowBorder}`,
            pointerEvents: 'none',
          }}
        />

        {/* Label: Remotion */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.leftLabelX,
            top: leftLabelY,
            color: COLORS.labelText,
            fontSize: TYPOGRAPHY.label.fontSize,
            fontFamily: TYPOGRAPHY.label.fontFamily,
            fontWeight: TYPOGRAPHY.label.fontWeight,
          }}
        >
          Remotion
        </div>

        {/* Sub-label: Deterministic Rendering */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.leftLabelX,
            top: leftLabelY + (POSITIONS.leftSubLabelY - POSITIONS.leftLabelY),
            color: COLORS.leftSubLabel,
            fontSize: TYPOGRAPHY.subLabel.fontSize,
            fontFamily: TYPOGRAPHY.subLabel.fontFamily,
            fontWeight: TYPOGRAPHY.subLabel.fontWeight,
          }}
        >
          Deterministic Rendering
        </div>

        {/* Mini bar chart */}
        <MiniBarChart />
      </div>

      {/* Vertical divider */}
      <VerticalDivider />

      {/* Right panel — Veo */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.halfWidth,
          top: 0,
          width: CANVAS.halfWidth,
          height: CANVAS.height,
          backgroundColor: COLORS.rightBackground,
          opacity: rightOpacity,
          overflow: 'hidden',
        }}
      >
        {/* Label: Veo */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.rightLabelX - CANVAS.halfWidth,
            top: rightLabelY,
            color: COLORS.labelText,
            fontSize: TYPOGRAPHY.label.fontSize,
            fontFamily: TYPOGRAPHY.label.fontFamily,
            fontWeight: TYPOGRAPHY.label.fontWeight,
          }}
        >
          Veo
        </div>

        {/* Sub-label: AI-Generated Footage */}
        <div
          style={{
            position: 'absolute',
            left: POSITIONS.rightLabelX - CANVAS.halfWidth,
            top: rightLabelY + (POSITIONS.rightSubLabelY - POSITIONS.rightLabelY),
            color: COLORS.rightSubLabel,
            fontSize: TYPOGRAPHY.subLabel.fontSize,
            fontFamily: TYPOGRAPHY.subLabel.fontFamily,
            fontWeight: TYPOGRAPHY.subLabel.fontWeight,
          }}
        >
          AI-Generated Footage
        </div>

        {/* Film reel icon */}
        <FilmReelIcon />
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06FrameworkComparisonProps = {};

export default AnimationSection06FrameworkComparison;
