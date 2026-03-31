import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import {
  BG_DEEP_NAVY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_WIDTH,
  PANEL_GAP,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  COLOR_BLUE,
  PHASE_REGEN_START,
  PHASE_REGEN_END,
} from './constants';
import { CodeEditorPanel } from './CodeEditorPanel';
import { TerminalPanel } from './TerminalPanel';
import { ShimmerEffect } from './ShimmerEffect';

export const defaultColdOpen09TestFixCycleProps = {};

export const ColdOpen09TestFixCycle: React.FC = () => {
  const frame = useCurrentFrame();

  // Layout fade-in over first 20 frames
  const layoutOpacity = interpolate(frame, [0, 20], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Subtle upward slide on entry
  const layoutTranslateY = interpolate(frame, [0, 20], [12, 0], {
    easing: Easing.out(Easing.quad),
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Total width used by panels
  const totalPanelWidth = LEFT_PANEL_WIDTH + PANEL_GAP + RIGHT_PANEL_WIDTH;
  const horizontalOffset = (CANVAS_WIDTH - totalPanelWidth) / 2;
  const panelHeight = CANVAS_HEIGHT - 60; // 30px top/bottom margin
  const panelTop = 30;

  // Editor panel height for shimmer
  const editorHeight = panelHeight;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_DEEP_NAVY,
        overflow: 'hidden',
      }}
    >
      <div
        style={{
          position: 'absolute',
          top: panelTop,
          left: horizontalOffset,
          width: totalPanelWidth,
          height: panelHeight,
          display: 'flex',
          gap: PANEL_GAP,
          opacity: layoutOpacity,
          transform: `translateY(${layoutTranslateY}px)`,
        }}
      >
        {/* Left panel: Code Editor */}
        <div style={{ position: 'relative', width: LEFT_PANEL_WIDTH, height: editorHeight }}>
          <CodeEditorPanel width={LEFT_PANEL_WIDTH} height={editorHeight} />

          {/* Shimmer overlay during regeneration */}
          <Sequence from={PHASE_REGEN_START} durationInFrames={PHASE_REGEN_END - PHASE_REGEN_START}>
            <ShimmerEffect
              width={LEFT_PANEL_WIDTH}
              height={editorHeight}
              color={COLOR_BLUE}
              peakOpacity={0.15}
              durationFrames={45}
              startFrame={0}
            />
          </Sequence>
        </div>

        {/* Right panel: Terminal */}
        <TerminalPanel width={RIGHT_PANEL_WIDTH} height={panelHeight} />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen09TestFixCycle;
