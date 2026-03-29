import React from 'react';
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
  staticFile,
} from 'remotion';
import { CANVAS_WIDTH, CANVAS_HEIGHT, BG_COLOR, FADE_IN_END } from './constants';
import SplitPanel from './SplitPanel';
import CenterDivider from './CenterDivider';

// ---------------------------------------------------------------------------
// Media resolution — import the shared hook for visual-media alias lookup.
// The wrapper layer provides per-visual aliases (leftSrc, rightSrc, etc.)
// that this hook resolves at runtime.
// ---------------------------------------------------------------------------
import { useVisualMediaAssetSrc } from '../_shared/visual-runtime';

// ---------------------------------------------------------------------------
// Fallback map: alias → known Veo filename for standalone preview
// ---------------------------------------------------------------------------
const FALLBACK_FILES: Record<string, string> = {
  leftSrc: 'developer_cursor_edit.mp4',
  leftRevealSrc: 'developer_codebase_zoomout.mp4',
  rightSrc: 'grandmother_darning.mp4',
  rightRevealSrc: 'grandmother_drawer_zoomout.mp4',
};

function useMediaSrc(alias: string): string {
  const resolved = useVisualMediaAssetSrc(alias);
  if (resolved) return resolved;
  const fallback = FALLBACK_FILES[alias];
  if (fallback) return staticFile(`veo/${fallback}`);
  return staticFile('veo/darning_split_screen.mp4');
}

// ---------------------------------------------------------------------------
// Default props (empty — this component is self-contained)
// ---------------------------------------------------------------------------
export const defaultColdOpen01SplitScreenDarningProps = {};

// ---------------------------------------------------------------------------
// Main component
// ---------------------------------------------------------------------------
/**
 * ColdOpen01SplitScreenDarning
 *
 * Split-screen composition: developer editing code (left) vs. grandmother
 * darning socks (right). Both sides progress through an initial task then
 * zoom out to reveal accumulated repair work.
 *
 * Duration: 270 frames (9 s @ 30 fps)
 */
export const ColdOpen01SplitScreenDarning: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Resolve video sources ──────────────────────────────────────────
  const leftClip1 = useMediaSrc('leftSrc');
  const leftClip2 = useMediaSrc('leftRevealSrc');
  const rightClip1 = useMediaSrc('rightSrc');
  const rightClip2 = useMediaSrc('rightRevealSrc');

  // ── Global fade-in from black ──────────────────────────────────────
  const globalOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Content fades in from black over the first 15 frames */}
      <AbsoluteFill style={{ opacity: globalOpacity }}>
        {/* Left panel — developer */}
        <SplitPanel clip1Src={leftClip1} clip2Src={leftClip2} side="left" />

        {/* Center divider */}
        <CenterDivider />

        {/* Right panel — grandmother */}
        <SplitPanel clip1Src={rightClip1} clip2Src={rightClip2} side="right" />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenDarning;
