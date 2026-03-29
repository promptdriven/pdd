import React from 'react';
import {
  AbsoluteFill,
  OffthreadVideo,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import {
  PANEL_WIDTH,
  PANEL_HEIGHT,
  PANEL_FADE_FRAMES,
  LABEL_COLOR,
  LABEL_BG_COLOR,
  LABEL_FONT_SIZE,
  LABEL_PADDING_H,
  LABEL_PADDING_V,
  LABEL_BOTTOM_OFFSET,
  LABEL_BORDER_RADIUS,
  LABEL_OPACITY,
} from './constants';

interface SplitPanelProps {
  side: 'left' | 'right';
  videoSrc: string | null;
  label: string;
  fallbackGradient: string;
}

export const SplitPanel: React.FC<SplitPanelProps> = ({
  side,
  videoSrc,
  label,
  fallbackGradient,
}) => {
  const frame = useCurrentFrame();

  const panelOpacity = interpolate(frame, [0, PANEL_FADE_FRAMES], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const leftOffset = side === 'left' ? 0 : PANEL_WIDTH + 40;

  return (
    <AbsoluteFill
      style={{
        left: leftOffset,
        width: PANEL_WIDTH,
        height: PANEL_HEIGHT,
        opacity: panelOpacity,
        overflow: 'hidden',
      }}
    >
      {videoSrc ? (
        <OffthreadVideo
          src={videoSrc}
          style={{
            width: PANEL_WIDTH,
            height: PANEL_HEIGHT,
            objectFit: 'cover',
          }}
        />
      ) : (
        <AbsoluteFill
          style={{
            background: fallbackGradient,
            width: PANEL_WIDTH,
            height: PANEL_HEIGHT,
          }}
        />
      )}

      {/* Panel label */}
      <div
        style={{
          position: 'absolute',
          bottom: LABEL_BOTTOM_OFFSET,
          left: '50%',
          transform: 'translateX(-50%)',
          backgroundColor: LABEL_BG_COLOR,
          color: LABEL_COLOR,
          fontSize: LABEL_FONT_SIZE,
          fontFamily: 'Inter, system-ui, sans-serif',
          fontWeight: 500,
          paddingLeft: LABEL_PADDING_H,
          paddingRight: LABEL_PADDING_H,
          paddingTop: LABEL_PADDING_V,
          paddingBottom: LABEL_PADDING_V,
          borderRadius: LABEL_BORDER_RADIUS,
          opacity: LABEL_OPACITY,
          whiteSpace: 'nowrap',
          letterSpacing: '0.02em',
        }}
      >
        {label}
      </div>
    </AbsoluteFill>
  );
};

export default SplitPanel;
