import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION } from './constants';
import { PanelHeader } from './PanelHeader';
import { TypewriterText } from './TypewriterText';
import { ArrowDivider } from './ArrowDivider';

export const VeoSection10SplitComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Left panel: slides in from -948 to 0, out to -948
  const leftSlideIn = interpolate(
    frame,
    [ANIMATION.slideInStart, ANIMATION.slideInEnd],
    [-DIMENSIONS.panelWidth, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const leftSlideOut = interpolate(
    frame,
    [ANIMATION.slideOutStart, ANIMATION.slideOutEnd],
    [0, -DIMENSIONS.panelWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  const leftX = frame < ANIMATION.slideOutStart ? leftSlideIn : leftSlideOut;

  // Right panel: slides in from 1920 to 972, out to 1920
  const rightSlideIn = interpolate(
    frame,
    [ANIMATION.slideInStart, ANIMATION.slideInEnd],
    [CANVAS.width, DIMENSIONS.rightPanelX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const rightSlideOut = interpolate(
    frame,
    [ANIMATION.slideOutStart, ANIMATION.slideOutEnd],
    [DIMENSIONS.rightPanelX, CANVAS.width],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
    }
  );

  const rightX = frame < ANIMATION.slideOutStart ? rightSlideIn : rightSlideOut;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Left panel: code-editor style prompt */}
      <div
        style={{
          position: 'absolute',
          left: leftX,
          top: 0,
          width: DIMENSIONS.panelWidth,
          height: DIMENSIONS.panelHeight,
          backgroundColor: COLORS.leftPanelBg,
          overflow: 'hidden',
          zIndex: 2,
        }}
      >
        <PanelHeader text="PROMPT" align="left" />
        <TypewriterText />
      </div>

      {/* Right panel: Veo video output */}
      <div
        style={{
          position: 'absolute',
          left: rightX,
          top: 0,
          width: DIMENSIONS.panelWidth,
          height: DIMENSIONS.panelHeight,
          overflow: 'hidden',
          zIndex: 2,
        }}
      >
        <PanelHeader text="OUTPUT" align="right" />
        <OffthreadVideo
          src={staticFile('veo/veo_section.mp4')}
          style={{
            width: CANVAS.width,
            height: CANVAS.height,
            objectFit: 'cover',
            marginLeft: -(CANVAS.width - DIMENSIONS.panelWidth),
          }}
        />
      </div>

      {/* Divider with arrow */}
      <ArrowDivider />
    </AbsoluteFill>
  );
};

export const defaultVeoSection10SplitComparisonProps = {};

export default VeoSection10SplitComparison;
