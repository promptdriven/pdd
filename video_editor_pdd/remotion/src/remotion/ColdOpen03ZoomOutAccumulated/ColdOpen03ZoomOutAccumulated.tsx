import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  DIVIDER_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  LEFT_BG,
  RIGHT_BG,
  ZOOM_START,
  ZOOM_END,
  ZOOM_FROM,
  ZOOM_TO,
  PATCH_COUNTER_COLOR,
  PATCH_COUNTER_OPACITY,
  GARMENT_COUNTER_COLOR,
  GARMENT_COUNTER_OPACITY,
  PATCH_COUNT_TARGET,
  GARMENT_COUNT_TARGET,
  PULSE_START,
  PULSE_DURATION,
} from './constants';
import { CodebaseGrid } from './CodebaseGrid';
import { DresserDrawer } from './DresserDrawer';
import { FloatingComments } from './FloatingComments';
import { AnimatedCounter } from './AnimatedCounter';

export const defaultColdOpen03ZoomOutAccumulatedProps = {};

export const ColdOpen03ZoomOutAccumulated: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom-out scale: 1.0 -> 0.15 over frames 10-90
  const zoomScale = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [ZOOM_FROM, ZOOM_TO],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Brightness pulse for frames 180-210
  const pulsePhase = interpolate(
    frame,
    [PULSE_START, PULSE_START + PULSE_DURATION],
    [0, Math.PI * 2],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );
  const brightnessOffset =
    frame >= PULSE_START ? Math.sin(pulsePhase) * 0.02 : 0;
  const brightness = 1 + brightnessOffset;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#0A1628',
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* LEFT PANEL — Codebase Sprawl */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: DIVIDER_X,
          height: CANVAS_HEIGHT,
          backgroundColor: LEFT_BG,
          overflow: 'hidden',
          filter: `brightness(${brightness})`,
        }}
      >
        {/* Zoomed content container */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: DIVIDER_X,
            height: CANVAS_HEIGHT,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            transform: `scale(${zoomScale})`,
          }}
        >
          {/* Inner scaling container — much larger than panel to fill at low zoom */}
          <div
            style={{
              position: 'relative',
              width: DIVIDER_X / ZOOM_TO,
              height: CANVAS_HEIGHT / ZOOM_TO,
            }}
          >
            <CodebaseGrid />
          </div>
        </div>

        {/* Floating comments overlay (not affected by zoom) */}
        <Sequence from={90} durationInFrames={120}>
          <div
            style={{
              position: 'absolute',
              left: 0,
              top: 0,
              width: DIVIDER_X,
              height: CANVAS_HEIGHT,
            }}
          >
            <FloatingComments />
          </div>
        </Sequence>

        {/* Patch counter */}
        <AnimatedCounter
          from={0}
          to={PATCH_COUNT_TARGET}
          suffix="patches"
          color={PATCH_COUNTER_COLOR}
          counterOpacity={PATCH_COUNTER_OPACITY}
          align="left"
          x={24}
          y={CANVAS_HEIGHT - 40}
        />
      </div>

      {/* RIGHT PANEL — Mended Garments */}
      <div
        style={{
          position: 'absolute',
          left: DIVIDER_X,
          top: 0,
          width: CANVAS_WIDTH - DIVIDER_X,
          height: CANVAS_HEIGHT,
          backgroundColor: RIGHT_BG,
          overflow: 'hidden',
          filter: `brightness(${brightness})`,
        }}
      >
        {/* Zoomed content container */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: CANVAS_WIDTH - DIVIDER_X,
            height: CANVAS_HEIGHT,
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
            transform: `scale(${zoomScale})`,
          }}
        >
          <div
            style={{
              position: 'relative',
              width: (CANVAS_WIDTH - DIVIDER_X) / ZOOM_TO,
              height: CANVAS_HEIGHT / ZOOM_TO,
            }}
          >
            <DresserDrawer />
          </div>
        </div>

        {/* Garment counter */}
        <AnimatedCounter
          from={0}
          to={GARMENT_COUNT_TARGET}
          suffix="mended garments"
          color={GARMENT_COUNTER_COLOR}
          counterOpacity={GARMENT_COUNTER_OPACITY}
          align="right"
          x={CANVAS_WIDTH - DIVIDER_X - 240}
          y={CANVAS_HEIGHT - 40}
        />
      </div>

      {/* SPLIT DIVIDER */}
      <div
        style={{
          position: 'absolute',
          left: DIVIDER_X - DIVIDER_WIDTH / 2,
          top: 0,
          width: DIVIDER_WIDTH,
          height: CANVAS_HEIGHT,
          backgroundColor: DIVIDER_COLOR,
          opacity: DIVIDER_OPACITY,
          zIndex: 10,
        }}
      />
    </AbsoluteFill>
  );
};

export default ColdOpen03ZoomOutAccumulated;
