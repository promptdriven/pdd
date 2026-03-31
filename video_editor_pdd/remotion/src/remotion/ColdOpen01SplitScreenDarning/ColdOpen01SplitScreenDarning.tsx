import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  staticFile,
} from 'remotion';
import { SplitPanel } from './SplitPanel';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BACKGROUND_COLOR,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  DIVIDER_GAP,
  DIVIDER_THICKNESS,
  PANEL_WIDTH,
  FADE_IN_START,
  FADE_IN_END,
  LEFT_LABEL,
  RIGHT_LABEL,
  LABEL_FONT_SIZE,
  LABEL_COLOR,
  LABEL_OPACITY_PRIMARY,
  LABEL_BG_COLOR,
} from './constants';

// ---------------------------------------------------------------------------
// Helper: resolve video source.
// If the wrapper provides a media-asset hook we use it; otherwise fall back to
// staticFile() referencing known Veo assets.
// ---------------------------------------------------------------------------

let _useVisualMediaAssetSrc: ((alias: string) => string | null) | undefined;
try {
  // eslint-disable-next-line @typescript-eslint/no-var-requires
  const shared = require('../_shared/visual-runtime');
  _useVisualMediaAssetSrc = shared.useVisualMediaAssetSrc;
} catch {
  // _shared module not available – will fall back to staticFile() below
}

/** No-op hook placeholder so the call count is always stable. */
const _noopHook = (_alias: string): string | null => null;

/** Resolved hook – always safe to call unconditionally. */
const useVisualMedia = _useVisualMediaAssetSrc ?? _noopHook;

/**
 * Hook that resolves a visual-media alias to a video src path.
 * Calls the runtime hook unconditionally, then falls back to staticFile.
 */
function useMediaSrc(alias: string, fallbackPath: string): string {
  const resolved = useVisualMedia(alias);
  if (resolved) return resolved;
  return staticFile(fallbackPath);
}

// ---------------------------------------------------------------------------
// Default props (empty – component is self-contained)
// ---------------------------------------------------------------------------
export const defaultColdOpen01SplitScreenDarningProps = {};

// ---------------------------------------------------------------------------
// Main component
// ---------------------------------------------------------------------------
export const ColdOpen01SplitScreenDarning: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Resolve video sources ---
  const leftClipA = useMediaSrc('leftSrc', 'veo/developer_cursor_edit.mp4');
  const leftClipB = useMediaSrc(
    'leftRevealSrc',
    'veo/developer_codebase_zoomout.mp4',
  );
  const rightClipA = useMediaSrc('rightSrc', 'veo/grandmother_darning.mp4');
  const rightClipB = useMediaSrc(
    'rightRevealSrc',
    'veo/grandmother_drawer_zoomout.mp4',
  );

  // --- Global fade-in (from black) over the first 15 frames ---
  const globalOpacity = interpolate(
    frame,
    [FADE_IN_START, FADE_IN_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // --- Divider fade-in ---
  const dividerOpacity = interpolate(
    frame,
    [FADE_IN_START, FADE_IN_END],
    [0, DIVIDER_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // --- Label fade-in (slightly after panels) ---
  const labelOpacity = interpolate(frame, [10, 30], [0, LABEL_OPACITY_PRIMARY], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Panel offsets
  const leftPanelLeft = 0;
  const rightPanelLeft = PANEL_WIDTH + DIVIDER_GAP;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: globalOpacity,
      }}
    >
      {/* Left panel – Developer */}
      <SplitPanel
        clipASrc={leftClipA}
        clipBSrc={leftClipB}
        leftOffset={leftPanelLeft}
      />

      {/* Right panel – Grandmother */}
      <SplitPanel
        clipASrc={rightClipA}
        clipBSrc={rightClipB}
        leftOffset={rightPanelLeft}
      />

      {/* Centre divider */}
      <div
        style={{
          position: 'absolute',
          left: PANEL_WIDTH + (DIVIDER_GAP - DIVIDER_THICKNESS) / 2,
          top: 0,
          width: DIVIDER_THICKNESS,
          height: CANVAS_HEIGHT,
          backgroundColor: DIVIDER_COLOR,
          opacity: dividerOpacity,
        }}
      />

      {/* Left label */}
      <div
        style={{
          position: 'absolute',
          bottom: 40,
          left: 0,
          width: PANEL_WIDTH,
          display: 'flex',
          justifyContent: 'center',
          opacity: labelOpacity,
          pointerEvents: 'none',
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: LABEL_FONT_SIZE,
            color: LABEL_COLOR,
            backgroundColor: LABEL_BG_COLOR,
            padding: '6px 18px',
            borderRadius: 6,
            letterSpacing: '0.02em',
          }}
        >
          {LEFT_LABEL}
        </span>
      </div>

      {/* Right label */}
      <div
        style={{
          position: 'absolute',
          bottom: 40,
          left: rightPanelLeft,
          width: PANEL_WIDTH,
          display: 'flex',
          justifyContent: 'center',
          opacity: labelOpacity,
          pointerEvents: 'none',
        }}
      >
        <span
          style={{
            fontFamily: 'Inter, system-ui, sans-serif',
            fontSize: LABEL_FONT_SIZE,
            color: LABEL_COLOR,
            backgroundColor: LABEL_BG_COLOR,
            padding: '6px 18px',
            borderRadius: 6,
            letterSpacing: '0.02em',
          }}
        >
          {RIGHT_LABEL}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenDarning;
