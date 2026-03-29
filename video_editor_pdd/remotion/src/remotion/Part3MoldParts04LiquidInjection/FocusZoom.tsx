import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  FOCUS_WALL,
  WALL_GLOW_COLOR,
  FONT_MONO,
  FRAME_FOCUS_ZOOM_START,
  FRAME_FOCUS_ZOOM_END,
  FRAME_ZOOM_OUT_START,
  FRAME_ZOOM_OUT_END,
} from './constants';

/**
 * Renders the zoom-focus effect on the null → None wall.
 * This applies a scale transform to the parent content by wrapping children,
 * and also draws an additional highlight layer on the focus wall.
 */
export const FocusZoom: React.FC<{ children: React.ReactNode }> = ({ children }) => {
  const frame = useCurrentFrame();

  // Zoom in: frames 180-210
  const zoomIn = interpolate(
    frame,
    [FRAME_FOCUS_ZOOM_START, FRAME_FOCUS_ZOOM_END],
    [1.0, 1.25],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Zoom out: frames 270-300
  const zoomOut = interpolate(
    frame,
    [FRAME_ZOOM_OUT_START, FRAME_ZOOM_OUT_END],
    [1.25, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Combined scale
  let scale = 1.0;
  if (frame < FRAME_FOCUS_ZOOM_START) {
    scale = 1.0;
  } else if (frame <= FRAME_FOCUS_ZOOM_END) {
    scale = zoomIn;
  } else if (frame < FRAME_ZOOM_OUT_START) {
    scale = 1.25;
  } else if (frame <= FRAME_ZOOM_OUT_END) {
    scale = zoomOut;
  } else {
    scale = 1.0;
  }

  // Focus center point (the null → None wall)
  const focusCx = FOCUS_WALL.x + FOCUS_WALL.width / 2;
  const focusCy = FOCUS_WALL.y + FOCUS_WALL.height / 2;

  // Calculate translation to keep focus point centered during zoom
  const translateX = (1 - scale) * focusCx;
  const translateY = (1 - scale) * focusCy;

  return (
    <div
      style={{
        width: '100%',
        height: '100%',
        transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
        transformOrigin: '0 0',
      }}
    >
      {children}
    </div>
  );
};

/**
 * An additional highlight layer specifically for the focus wall,
 * with label pulse and stronger glow.
 */
export const FocusWallHighlight: React.FC = () => {
  const frame = useCurrentFrame();

  // Only show during and after the focus sequence
  const showHighlight = frame >= FOCUS_WALL.hitFrame;
  if (!showHighlight) return null;

  // Pulse label on contact (frame 150)
  const hitFrame = FOCUS_WALL.hitFrame;
  const pulseScale = interpolate(
    frame,
    [hitFrame, hitFrame + 8, hitFrame + 20],
    [1, 1.3, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Extra glow during zoom focus (180-270)
  const extraGlow = interpolate(
    frame,
    [FRAME_FOCUS_ZOOM_START, FRAME_FOCUS_ZOOM_END, FRAME_ZOOM_OUT_START, FRAME_ZOOM_OUT_END],
    [0, 0.5, 0.5, 0.15],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0, pointerEvents: 'none' }}
      viewBox="0 0 1920 1080"
    >
      <defs>
        <filter id="focusGlow" x="-100%" y="-100%" width="300%" height="300%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="12" />
        </filter>
      </defs>

      {/* Expanded glow around focus wall */}
      <rect
        x={FOCUS_WALL.x - 20}
        y={FOCUS_WALL.y - 20}
        width={FOCUS_WALL.width + 40}
        height={FOCUS_WALL.height + 40}
        fill={WALL_GLOW_COLOR}
        opacity={extraGlow}
        rx={8}
        filter="url(#focusGlow)"
      />

      {/* Pulsing label */}
      <text
        x={FOCUS_WALL.x + FOCUS_WALL.width / 2}
        y={FOCUS_WALL.y - 24}
        fill={WALL_GLOW_COLOR}
        fontSize={16}
        fontFamily={FONT_MONO}
        fontWeight="bold"
        textAnchor="middle"
        opacity={0.95}
        transform={`scale(${pulseScale})`}
        style={{
          transformOrigin: `${FOCUS_WALL.x + FOCUS_WALL.width / 2}px ${FOCUS_WALL.y - 24}px`,
          transformBox: 'fill-box',
        }}
      >
        null → None
      </text>
    </svg>
  );
};
