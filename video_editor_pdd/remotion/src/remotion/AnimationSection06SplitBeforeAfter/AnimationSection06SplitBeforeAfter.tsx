import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS,
  COLORS,
  DIMENSIONS,
  ANIMATION_TIMING,
} from './constants';
import { DividerLine } from './DividerLine';
import { BeforeCircle } from './BeforeCircle';
import { AfterSquare } from './AfterSquare';
import { PanelLabel } from './PanelLabel';

export const AnimationSection06SplitBeforeAfter: React.FC = () => {
  const frame = useCurrentFrame();

  // Left panel opacity
  const leftOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.leftPanelStart, ANIMATION_TIMING.leftPanelEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Right panel opacity
  const rightOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.rightPanelStart, ANIMATION_TIMING.rightPanelEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.backgroundLeft }}>
      {/* Left panel: Before (forest) */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.dividerX,
          height: CANVAS.height,
          backgroundColor: COLORS.backgroundLeft,
          opacity: leftOpacity,
          overflow: 'hidden',
        }}
      >
        <BeforeCircle />
        <PanelLabel
          text="BEFORE"
          fadeStart={ANIMATION_TIMING.leftPanelStart}
          fadeEnd={ANIMATION_TIMING.leftPanelEnd}
        />
        {/* Inner vignette */}
        <div
          style={{
            position: 'absolute',
            inset: 0,
            boxShadow: `inset 0 0 ${DIMENSIONS.vignetteSize}px rgba(0, 0, 0, 0.4)`,
            pointerEvents: 'none',
          }}
        />
      </div>

      {/* Right panel: After (beach) */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.dividerX,
          top: 0,
          width: CANVAS.dividerX,
          height: CANVAS.height,
          backgroundColor: COLORS.backgroundRight,
          opacity: rightOpacity,
          overflow: 'hidden',
        }}
      >
        <AfterSquare />
        <PanelLabel
          text="AFTER"
          fadeStart={ANIMATION_TIMING.rightPanelStart}
          fadeEnd={ANIMATION_TIMING.rightPanelEnd}
        />
        {/* Inner vignette */}
        <div
          style={{
            position: 'absolute',
            inset: 0,
            boxShadow: `inset 0 0 ${DIMENSIONS.vignetteSize}px rgba(0, 0, 0, 0.4)`,
            pointerEvents: 'none',
          }}
        />
      </div>

      {/* Vertical divider (on top of panels) */}
      <DividerLine />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection06SplitBeforeAfterProps = {};

export default AnimationSection06SplitBeforeAfter;
