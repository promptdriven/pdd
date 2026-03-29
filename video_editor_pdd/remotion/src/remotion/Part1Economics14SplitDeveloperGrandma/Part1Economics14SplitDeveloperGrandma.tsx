import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { useVisualMediaAssetSrc } from '../_shared/visual-runtime';
import { SplitPanel } from './SplitPanel';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BACKGROUND_COLOR,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  DIVIDER_WIDTH,
  DIVIDER_FADE_FRAMES,
  DIVIDER_GAP,
  PANEL_WIDTH,
  LEFT_LABEL,
  RIGHT_LABEL,
} from './constants';

export const defaultPart1Economics14SplitDeveloperGrandmaProps = {};

export const Part1Economics14SplitDeveloperGrandma: React.FC = () => {
  const frame = useCurrentFrame();

  // Resolve video sources via the visual media runtime
  const leftSrc = useVisualMediaAssetSrc('leftSrc');
  const rightSrc = useVisualMediaAssetSrc('rightSrc');

  // Divider fade-in: easeOut(quad) over 15 frames
  const dividerOpacity = interpolate(
    frame,
    [0, DIVIDER_FADE_FRAMES],
    [0, DIVIDER_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Divider vertical draw-in: extends from center outward
  const dividerHeight = interpolate(
    frame,
    [0, DIVIDER_FADE_FRAMES],
    [0, CANVAS_HEIGHT],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Center x position for divider
  const dividerX = PANEL_WIDTH + DIVIDER_GAP / 2 - DIVIDER_WIDTH / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Left panel — Developer with Cursor */}
      <SplitPanel
        side="left"
        videoSrc={leftSrc}
        label={LEFT_LABEL}
        fallbackGradient="linear-gradient(135deg, #0A1628 0%, #1E3A5F 50%, #2563EB 100%)"
      />

      {/* Center divider */}
      <div
        style={{
          position: 'absolute',
          left: dividerX,
          top: (CANVAS_HEIGHT - dividerHeight) / 2,
          width: DIVIDER_WIDTH,
          height: dividerHeight,
          backgroundColor: DIVIDER_COLOR,
          opacity: dividerOpacity,
        }}
      />

      {/* Right panel — Grandmother darning */}
      <SplitPanel
        side="right"
        videoSrc={rightSrc}
        label={RIGHT_LABEL}
        fallbackGradient="linear-gradient(135deg, #3D2B1F 0%, #78593A 50%, #D4A76A 100%)"
      />
    </AbsoluteFill>
  );
};

export default Part1Economics14SplitDeveloperGrandma;
