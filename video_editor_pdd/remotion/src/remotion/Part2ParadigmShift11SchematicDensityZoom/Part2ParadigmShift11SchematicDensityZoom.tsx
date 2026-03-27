// ============================================================
// Part2ParadigmShift11SchematicDensityZoom.tsx
// Main component – Animated zoom-out from a hand-drawn schematic
// that becomes overwhelmingly dense.
// ============================================================
import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import { EngineeringGrid } from './EngineeringGrid';
import { SchematicCanvas } from './SchematicCanvas';
import { DrawingHand } from './DrawingHand';
import { TransistorCounter } from './TransistorCounter';
import {
  WIDTH,
  HEIGHT,
  TOTAL_FRAMES,
  BG_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
  STROKE_COLOR,
  WIRE_COLOR,
  STROKE_WIDTH,
  WIRE_WIDTH,
  HAND_COLOR,
  HAND_OPACITY,
  HAND_FADE_START,
  HAND_FADE_DURATION,
  COUNTER_COLOR,
  COUNTER_LABEL_COLOR,
  COUNTER_FONT_SIZE,
  COUNTER_LABEL_SIZE,
  ZOOM_START_SCALE,
  ZOOM_END_SCALE,
  COUNTER_START,
  COUNTER_END,
  SCHEMATIC_WIDTH,
  SCHEMATIC_HEIGHT,
} from './constants';

export const defaultPart2ParadigmShift11SchematicDensityZoomProps = {};

export const Part2ParadigmShift11SchematicDensityZoom: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Zoom animation ──────────────────────────────────────
  // Smooth easeInOutCubic zoom from 8x to 0.1x
  const zoomProgress = interpolate(frame, [0, TOTAL_FRAMES], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.poly(3)),
  });

  // Exponential zoom interpolation (log-space)
  const logStart = Math.log(ZOOM_START_SCALE);
  const logEnd = Math.log(ZOOM_END_SCALE);
  const currentScale = Math.exp(logStart + zoomProgress * (logEnd - logStart));

  // ── Transistor count (for rendering) ─────────────────────
  // Exponential growth curve matching the counter
  const countProgress = interpolate(frame, [0, TOTAL_FRAMES], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.exp),
  });
  const logCountStart = Math.log(COUNTER_START);
  const logCountEnd = Math.log(COUNTER_END);
  const visibleTransistors = Math.round(
    Math.exp(logCountStart + countProgress * (logCountEnd - logCountStart)),
  );

  // ── Center offset for zoom ──────────────────────────────
  // Keep the schematic centered as we zoom
  const translateX = (WIDTH - SCHEMATIC_WIDTH * currentScale) / 2;
  const translateY = (HEIGHT - SCHEMATIC_HEIGHT * currentScale) / 2;

  // ── Counter background pill for readability ──────────────
  const counterBgOpacity = interpolate(frame, [0, 20], [0.7, 0.85], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
        width: WIDTH,
        height: HEIGHT,
      }}
    >
      {/* Engineering paper grid */}
      <EngineeringGrid
        spacing={GRID_SPACING}
        color={GRID_COLOR}
        opacity={GRID_OPACITY}
        width={WIDTH}
        height={HEIGHT}
      />

      {/* Zoomable schematic layer */}
      <div
        style={{
          position: 'absolute',
          width: SCHEMATIC_WIDTH,
          height: SCHEMATIC_HEIGHT,
          transform: `translate(${translateX}px, ${translateY}px) scale(${currentScale})`,
          transformOrigin: '0 0',
          willChange: 'transform',
        }}
      >
        <SchematicCanvas
          visibleCount={visibleTransistors}
          canvasWidth={SCHEMATIC_WIDTH}
          canvasHeight={SCHEMATIC_HEIGHT}
          strokeColor={STROKE_COLOR}
          wireColor={WIRE_COLOR}
          strokeWidth={STROKE_WIDTH / currentScale} // keep apparent width constant at small scales
          wireWidth={WIRE_WIDTH / currentScale}
        />
      </div>

      {/* Drawing hand overlay – in screen space */}
      <DrawingHand
        frame={frame}
        handColor={HAND_COLOR}
        handOpacity={HAND_OPACITY}
        fadeOutStart={HAND_FADE_START}
        fadeOutDuration={HAND_FADE_DURATION}
        areaWidth={WIDTH}
        areaHeight={HEIGHT}
      />

      {/* Counter container – lower right */}
      <div
        style={{
          position: 'absolute',
          right: 40,
          bottom: 40,
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'flex-end',
        }}
      >
        {/* Counter background pill for readability */}
        <div
          style={{
            position: 'absolute',
            inset: -12,
            backgroundColor: BG_COLOR,
            opacity: counterBgOpacity,
            borderRadius: 12,
            boxShadow: '0 2px 12px rgba(0,0,0,0.06)',
            border: `1px solid ${GRID_COLOR}`,
          }}
        />
        <TransistorCounter
          frame={frame}
          totalFrames={TOTAL_FRAMES}
          startValue={COUNTER_START}
          endValue={COUNTER_END}
          counterColor={COUNTER_COLOR}
          labelColor={COUNTER_LABEL_COLOR}
          counterFontSize={COUNTER_FONT_SIZE}
          labelFontSize={COUNTER_LABEL_SIZE}
          x={0}
          y={0}
        />
      </div>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift11SchematicDensityZoom;
