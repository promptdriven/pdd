import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
} from 'remotion';
import { useVisualMediaAssetSrc } from '../_shared/visual-runtime';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BG_COLOR,
  SPLIT_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_X,
  RIGHT_PANEL_WIDTH,
  LEFT_LABEL,
  LEFT_LABEL_COLOR,
  LEFT_COLOR_GRADE,
  LEFT_COLOR_GRADE_OPACITY,
  LEFT_VIGNETTE_EDGE,
  LEFT_VIGNETTE_OPACITY,
  RIGHT_LABEL,
  RIGHT_LABEL_COLOR,
  RIGHT_COLOR_GRADE,
  RIGHT_COLOR_GRADE_OPACITY,
  RIGHT_VIGNETTE_EDGE,
  RIGHT_VIGNETTE_OPACITY,
  LABEL_FONT_SIZE,
  LABEL_FONT_WEIGHT,
  LABEL_LETTER_SPACING,
  LABEL_Y,
  PHASE_HOLD_END,
  PULSE_CYCLE_FRAMES,
  PULSE_MIN_OPACITY,
  PULSE_MAX_OPACITY,
} from './constants';
import { SplitPanel } from './SplitPanel';
import { SplitDivider } from './SplitDivider';
import { PanelHeader } from './PanelHeader';

export const defaultColdOpen01SplitScreenHookProps = {};

export const ColdOpen01SplitScreenHook: React.FC = () => {
  const frame = useCurrentFrame();

  // Resolve video sources via the shared visual-runtime hook
  const leftVideoSrc = useVisualMediaAssetSrc('leftSrc');
  const rightVideoSrc = useVisualMediaAssetSrc('rightSrc');

  // Year label opacity — static at base opacity, then gentle pulse from frame 210+
  const labelOpacity = (() => {
    if (frame < PHASE_HOLD_END) {
      return PULSE_MIN_OPACITY;
    }
    // Pulse phase: sine wave between 0.25 and 0.35 over 30 frames
    const pulseFrame = frame - PHASE_HOLD_END;
    const cycleProgress = (pulseFrame % PULSE_CYCLE_FRAMES) / PULSE_CYCLE_FRAMES;
    return interpolate(
      Math.sin(cycleProgress * Math.PI * 2),
      [-1, 1],
      [PULSE_MIN_OPACITY, PULSE_MAX_OPACITY],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
    );
  })();

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Left panel — Developer (2025) */}
      <SplitPanel
        x={0}
        width={LEFT_PANEL_WIDTH}
        videoSrc={leftVideoSrc}
        colorGrade={LEFT_COLOR_GRADE}
        colorGradeOpacity={LEFT_COLOR_GRADE_OPACITY}
        vignetteEdge={LEFT_VIGNETTE_EDGE}
        vignetteOpacity={LEFT_VIGNETTE_OPACITY}
      />
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: LEFT_PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          pointerEvents: 'none',
        }}
      >
        <PanelHeader
          text={LEFT_LABEL}
          color={LEFT_LABEL_COLOR}
          opacity={labelOpacity}
          letterSpacing={LABEL_LETTER_SPACING}
          y={LABEL_Y}
          fontSize={LABEL_FONT_SIZE}
          fontWeight={LABEL_FONT_WEIGHT}
          panelWidth={LEFT_PANEL_WIDTH}
        />
      </div>

      {/* Split divider */}
      <SplitDivider
        x={SPLIT_X}
        width={DIVIDER_WIDTH}
        color={DIVIDER_COLOR}
        opacity={DIVIDER_OPACITY}
        canvasHeight={CANVAS_HEIGHT}
      />

      {/* Right panel — Grandmother (1955) */}
      <SplitPanel
        x={RIGHT_PANEL_X}
        width={RIGHT_PANEL_WIDTH}
        videoSrc={rightVideoSrc}
        colorGrade={RIGHT_COLOR_GRADE}
        colorGradeOpacity={RIGHT_COLOR_GRADE_OPACITY}
        vignetteEdge={RIGHT_VIGNETTE_EDGE}
        vignetteOpacity={RIGHT_VIGNETTE_OPACITY}
      />
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X,
          top: 0,
          width: RIGHT_PANEL_WIDTH,
          height: CANVAS_HEIGHT,
          pointerEvents: 'none',
        }}
      >
        <PanelHeader
          text={RIGHT_LABEL}
          color={RIGHT_LABEL_COLOR}
          opacity={labelOpacity}
          letterSpacing={LABEL_LETTER_SPACING}
          y={LABEL_Y}
          fontSize={LABEL_FONT_SIZE}
          fontWeight={LABEL_FONT_WEIGHT}
          panelWidth={RIGHT_PANEL_WIDTH}
        />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenHook;
