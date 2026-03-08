import React from 'react';
import {
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from 'remotion';
import {
  CANVAS,
  COLORS,
  POSITIONS,
  DIMENSIONS,
  TYPOGRAPHY,
  ANIMATION,
} from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
}

export const SplitPanel: React.FC<SplitPanelProps> = ({ side }) => {
  const frame = useCurrentFrame();
  const isLeft = side === 'left';

  const fadeStart = isLeft
    ? ANIMATION.leftPanelFadeStart
    : ANIMATION.rightPanelFadeStart;
  const fadeEnd = isLeft
    ? ANIMATION.leftPanelFadeEnd
    : ANIMATION.rightPanelFadeEnd;

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Ken Burns zoom — linear across entire duration
  const scale = interpolate(
    frame,
    [0, ANIMATION.totalDuration],
    [ANIMATION.kenBurnsScaleStart, ANIMATION.kenBurnsScaleEnd],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Label translate upward
  const labelTranslateY = interpolate(
    frame,
    [fadeStart + 5, fadeEnd],
    [ANIMATION.labelTranslateDistance, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const labelOpacity = interpolate(frame, [fadeStart + 5, fadeEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const panelLeft = isLeft ? 0 : DIMENSIONS.rightPanelStart;
  const panelWidth = isLeft ? DIMENSIONS.leftPanelWidth : CANVAS.width - DIMENSIONS.rightPanelStart;
  const tintColor = isLeft ? COLORS.oceanTint : COLORS.forestTint;
  const labelColor = isLeft ? COLORS.oceanLabel : COLORS.forestLabel;
  const labelText = isLeft ? 'Ocean at Sunset' : 'Forest Canopy';
  const labelCenterX = isLeft ? POSITIONS.leftPanelCenter : POSITIONS.rightPanelCenter;

  // Use different start times in the video for each panel to show different footage
  // Ocean: start of veo_section.mp4, Forest: 5s into veo_section.mp4
  const videoStartFrom = isLeft ? 0 : 150; // 5s at 30fps

  return (
    <div
      style={{
        position: 'absolute',
        left: panelLeft,
        top: 0,
        width: panelWidth,
        height: CANVAS.height,
        overflow: 'hidden',
        opacity,
      }}
    >
      {/* Video still with Ken Burns zoom */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          transform: `scale(${scale})`,
          transformOrigin: 'center center',
        }}
      >
        <OffthreadVideo
          src={staticFile('veo/veo_section.mp4')}
          startFrom={videoStartFrom}
          style={{
            position: 'absolute',
            top: '50%',
            left: '50%',
            transform: 'translate(-50%, -50%)',
            minWidth: '100%',
            minHeight: '100%',
            objectFit: 'cover',
          }}
          muted
        />
      </div>

      {/* Color tint overlay */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: '100%',
          height: '100%',
          backgroundColor: tintColor,
        }}
      />

      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: POSITIONS.labelY - 30,
          width: '100%',
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          opacity: labelOpacity,
          transform: `translateY(${labelTranslateY}px)`,
        }}
      >
        <span
          style={{
            color: labelColor,
            fontFamily: TYPOGRAPHY.label.fontFamily,
            fontWeight: TYPOGRAPHY.label.fontWeight,
            fontSize: TYPOGRAPHY.label.fontSize,
            textShadow: '0 2px 8px rgba(0,0,0,0.6)',
          }}
        >
          {labelText}
        </span>
      </div>
    </div>
  );
};
