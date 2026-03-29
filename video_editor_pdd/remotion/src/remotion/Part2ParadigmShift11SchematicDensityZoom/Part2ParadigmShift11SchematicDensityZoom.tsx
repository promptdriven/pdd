import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  TOTAL_FRAMES,
  ZOOM_START_SCALE,
  ZOOM_END_SCALE,
  COUNTER_START,
  COUNTER_END,
  COUNTER_FONT_SIZE,
  COUNTER_LABEL_FONT_SIZE,
  COUNTER_COLOR,
  COUNTER_LABEL_COLOR,
  COUNTER_X,
  COUNTER_Y,
  HAND_VISIBLE_END,
} from './constants';
import EngineeringGrid from './EngineeringGrid';
import SchematicCanvas from './SchematicCanvas';
import DrawingHand from './DrawingHand';

export const defaultPart2ParadigmShift11SchematicDensityZoomProps = {};

/**
 * Section 2.11: Schematic Density Zoom-Out
 *
 * Animated zoom-out from a hand-drawn schematic. Starts with ~20 visible
 * transistors, zooms out to 50,000+. A drawing hand slows and fades.
 * Counter tracks transistor count with exponential acceleration.
 *
 * Duration: 420 frames (14s @ 30fps)
 */
export const Part2ParadigmShift11SchematicDensityZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Zoom: easeInOutCubic from startScale → endScale over full duration ──
  const zoomScale = interpolate(frame, [0, TOTAL_FRAMES - 1], [ZOOM_START_SCALE, ZOOM_END_SCALE], {
    easing: Easing.inOut(Easing.poly(3)),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // ── Counter: piecewise interpolation to hit spec milestones ──
  // Phase 1: 20→100 (frames 0-60), Phase 2: 100→500 (60-150),
  // Phase 3: 500→5000 (150-240), Phase 4: 5000→25000 (240-330),
  // Phase 5: 25000→50000 (330-420)
  const counterValue = Math.round(
    interpolate(
      frame,
      [0, 60, 150, 240, 330, 419],
      [COUNTER_START, 100, 500, 5000, 25000, COUNTER_END],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    )
  );

  // Format counter with commas
  const formattedCount = counterValue.toLocaleString('en-US');

  // ── Visible transistor count tracks the counter ──
  const visibleTransistors = counterValue;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Engineering paper grid (static background) */}
      <EngineeringGrid />

      {/* Zoomable schematic layer */}
      <div
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          transform: `scale(${zoomScale})`,
          transformOrigin: '50% 50%',
          willChange: 'transform',
        }}
      >
        <SchematicCanvas visibleCount={visibleTransistors} />
      </div>

      {/* Drawing hand (visible for first 300 frames, fades at 240) */}
      <Sequence from={0} durationInFrames={HAND_VISIBLE_END}>
        <DrawingHand />
      </Sequence>

      {/* Transistor counter – lower right */}
      <div
        style={{
          position: 'absolute',
          left: COUNTER_X,
          top: COUNTER_Y,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          zIndex: 10,
        }}
      >
        {/* Counter background pill for readability */}
        <div
          style={{
            backgroundColor: 'rgba(245, 240, 232, 0.85)',
            borderRadius: 12,
            padding: '8px 20px 6px',
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
          }}
        >
          <span
            style={{
              fontFamily: '"JetBrains Mono", "SF Mono", "Fira Code", monospace',
              fontSize: COUNTER_FONT_SIZE,
              fontWeight: 400,
              color: COUNTER_COLOR,
              lineHeight: 1.2,
              letterSpacing: '-0.5px',
              opacity: 0.95,
            }}
          >
            {formattedCount}
          </span>
          <span
            style={{
              fontFamily: '"Inter", "Helvetica Neue", Arial, sans-serif',
              fontSize: COUNTER_LABEL_FONT_SIZE,
              fontWeight: 400,
              color: COUNTER_LABEL_COLOR,
              lineHeight: 1.4,
              marginTop: 2,
              opacity: 0.78,
            }}
          >
            transistors
          </span>
        </div>
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift11SchematicDensityZoom;
