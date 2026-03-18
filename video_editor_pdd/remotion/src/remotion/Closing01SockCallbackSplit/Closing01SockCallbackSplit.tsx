import React, { useMemo } from 'react';
import {
  AbsoluteFill,
  staticFile,
} from 'remotion';
import { CANVAS, SPLIT, COLORS } from './constants';
import { SplitDivider } from './SplitDivider';
import { PanelHeader } from './PanelHeader';
import { VeoPanel } from './VeoPanel';
import { CostLabel } from './CostLabel';
import { TerminalSnippet } from './TerminalSnippet';

export const defaultClosing01SockCallbackSplitProps = {};

/**
 * Section 7.1: Sock Callback — The Final Discard
 *
 * Vertical split screen. Left: holey sock discarded for a fresh one.
 * Right: buggy code regenerated instead of patched.
 * Cost labels appear: "$2" (sock) and "~30s" (code regeneration).
 */
export const Closing01SockCallbackSplit: React.FC = () => {
  // Resolve Veo sources — sock_final_discard.mp4 is available as an asset.
  // For the right panel, no exact match exists so we fall back to a
  // developer-themed clip that's available.
  const leftSrc = useMemo(() => {
    try {
      return staticFile('veo/sock_final_discard.mp4');
    } catch {
      return null;
    }
  }, []);

  const rightSrc = useMemo(() => {
    try {
      return staticFile('veo/developer_prompt_shift.mp4');
    } catch {
      return null;
    }
  }, []);

  return (
    <AbsoluteFill
      style={{
        backgroundColor: CANVAS.BACKGROUND,
        width: CANVAS.WIDTH,
        height: CANVAS.HEIGHT,
      }}
    >
      {/* Left panel — Sock Discard */}
      <VeoPanel
        src={leftSrc}
        panelX={0}
        panelWidth={SPLIT.LEFT_WIDTH}
        gradeColor={COLORS.AMBER_GRADE}
        gradeOpacity={0.03}
        vignetteColor={COLORS.LEFT_VIGNETTE}
      />

      {/* Right panel — Code Regeneration */}
      <VeoPanel
        src={rightSrc}
        panelX={SPLIT.RIGHT_X}
        panelWidth={SPLIT.RIGHT_WIDTH}
        gradeColor={COLORS.BLUE_GRADE}
        gradeOpacity={0.02}
        vignetteColor={COLORS.RIGHT_VIGNETTE}
      />

      {/* Split divider line */}
      <SplitDivider />

      {/* Panel headers */}
      <PanelHeader
        text="DISCARD"
        color={COLORS.AMBER}
        panelX={0}
        panelWidth={SPLIT.LEFT_WIDTH}
      />
      <PanelHeader
        text="REGENERATE"
        color={COLORS.BLUE}
        panelX={SPLIT.RIGHT_X}
        panelWidth={SPLIT.RIGHT_WIDTH}
      />

      {/* Cost labels — left: "$2" / "new pair" */}
      <CostLabel
        cost="$2"
        subLabel="new pair"
        color={COLORS.AMBER}
        centerX={SPLIT.LEFT_WIDTH / 2}
      />

      {/* Cost labels — right: "~30s" / "regenerated" */}
      <CostLabel
        cost="~30s"
        subLabel="regenerated"
        color={COLORS.BLUE}
        centerX={SPLIT.RIGHT_X + SPLIT.RIGHT_WIDTH / 2}
      />

      {/* Terminal snippet in right panel */}
      <TerminalSnippet />
    </AbsoluteFill>
  );
};

export default Closing01SockCallbackSplit;
