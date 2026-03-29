import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from 'remotion';
import ContextWindowPanel from './ContextWindowPanel';
import TokenBlockGrid from './TokenBlockGrid';
import RightPanelBlocks from './RightPanelBlocks';
import {
  BG_COLOR,
  PANEL_WIDTH,
  PANEL_HEIGHT,
  LEFT_PANEL_X,
  LEFT_PANEL_Y,
  RIGHT_PANEL_X,
  RIGHT_PANEL_Y,
  LEFT_BORDER_COLOR,
  LEFT_HEADER_COLOR,
  RIGHT_BORDER_COLOR,
  RIGHT_HEADER_COLOR,
  LABEL_RED,
  LABEL_GREEN,
  COMPARISON_LABEL_START,
} from './constants';

export const defaultPart1Economics11PatchingVsRegenerationProps = {};

export const Part1Economics11PatchingVsRegeneration: React.FC = () => {
  const frame = useCurrentFrame();

  // Comparison labels fade in at frame 360
  const labelOpacity = interpolate(
    frame,
    [COMPARISON_LABEL_START, COMPARISON_LABEL_START + 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Left Panel: Agentic Patching */}
      <ContextWindowPanel
        x={LEFT_PANEL_X}
        y={LEFT_PANEL_Y}
        width={PANEL_WIDTH}
        height={PANEL_HEIGHT}
        header="Agentic Patching"
        headerColor={LEFT_HEADER_COLOR}
        borderColor={LEFT_BORDER_COLOR}
        borderStyle="dashed"
      >
        <TokenBlockGrid panelWidth={PANEL_WIDTH} panelHeight={PANEL_HEIGHT} />
      </ContextWindowPanel>

      {/* Right Panel: PDD Regeneration */}
      <ContextWindowPanel
        x={RIGHT_PANEL_X}
        y={RIGHT_PANEL_Y}
        width={PANEL_WIDTH}
        height={PANEL_HEIGHT}
        header="PDD Regeneration"
        headerColor={RIGHT_HEADER_COLOR}
        borderColor={RIGHT_BORDER_COLOR}
        borderStyle="solid"
      >
        <RightPanelBlocks panelWidth={PANEL_WIDTH} panelHeight={PANEL_HEIGHT} />
      </ContextWindowPanel>

      {/* Comparison label: Left panel */}
      <div
        style={{
          position: 'absolute',
          left: LEFT_PANEL_X,
          top: LEFT_PANEL_Y + PANEL_HEIGHT + 20,
          width: PANEL_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: LABEL_RED,
          opacity: labelOpacity,
        }}
      >
        15,000 tokens — mostly wrong
      </div>

      {/* Comparison label: Right panel */}
      <div
        style={{
          position: 'absolute',
          left: RIGHT_PANEL_X,
          top: RIGHT_PANEL_Y + PANEL_HEIGHT + 20,
          width: PANEL_WIDTH,
          textAlign: 'center',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 400,
          color: LABEL_GREEN,
          opacity: labelOpacity,
        }}
      >
        2,300 tokens — all curated
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics11PatchingVsRegeneration;
