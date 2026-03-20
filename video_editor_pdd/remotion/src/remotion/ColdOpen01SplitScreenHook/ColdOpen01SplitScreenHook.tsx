import React from 'react';
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
  staticFile,
} from 'remotion';
import { SplitPanel } from './SplitPanel';
import { DividerGlow } from './DividerGlow';
import {
  COMP_WIDTH,
  COMP_HEIGHT,
  BG_COLOR,
  DIVIDER_X,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  LEFT_PANEL_WIDTH,
  RIGHT_PANEL_LEFT,
  RIGHT_PANEL_WIDTH,
  LEFT_TINT_COLOR,
  LEFT_TINT_OPACITY,
  LEFT_VIGNETTE_COLOR,
  LEFT_VIGNETTE_OPACITY,
  LEFT_LABEL,
  LEFT_LABEL_X,
  LEFT_LABEL_Y,
  RIGHT_TINT_COLOR,
  RIGHT_TINT_OPACITY,
  RIGHT_VIGNETTE_COLOR,
  RIGHT_VIGNETTE_OPACITY,
  RIGHT_LABEL,
  RIGHT_LABEL_X,
  RIGHT_LABEL_Y,
  FILM_GRAIN_OPACITY,
  FILM_GRAIN_FPS,
  FADE_IN_END,
  GLOW_START,
  GLOW_DURATION,
} from './constants';

export const defaultColdOpen01SplitScreenHookProps = {};

/**
 * Cold Open 01 — Split Screen Hook
 *
 * A vertical split screen comparing a modern developer editing code in Cursor
 * (left, "2025") with a grandmother darning a sock under lamplight
 * (right, "1955"). Both complete their repair tasks in parallel.
 */
export const ColdOpen01SplitScreenHook: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Fade-in: frames 0-15, easeOut(cubic) ──────────────────────────────────
  const fadeInOpacity = interpolate(frame, [0, FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  // Resolve video sources — assets are available in veo/ via staticFile
  const leftVideoSrc = staticFile('veo/developer_cursor_edit.mp4');
  const rightVideoSrc = staticFile('veo/grandmother_darning.mp4');

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: COMP_WIDTH,
        height: COMP_HEIGHT,
      }}
    >
      {/* Fade-in wrapper for entire content */}
      <AbsoluteFill style={{ opacity: fadeInOpacity }}>
        {/* ── Left Panel: Developer / 2025 ───────────────────────────────── */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: 0,
            width: LEFT_PANEL_WIDTH,
            height: COMP_HEIGHT,
            zIndex: 1,
          }}
        >
          <SplitPanel
            width={LEFT_PANEL_WIDTH}
            videoSrc={leftVideoSrc}
            tintColor={LEFT_TINT_COLOR}
            tintOpacity={LEFT_TINT_OPACITY}
            vignetteColor={LEFT_VIGNETTE_COLOR}
            vignetteOpacity={LEFT_VIGNETTE_OPACITY}
            label={LEFT_LABEL}
            labelX={LEFT_LABEL_X}
            labelY={LEFT_LABEL_Y}
          />
        </div>

        {/* ── Vertical Divider ───────────────────────────────────────────── */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: DIVIDER_X - DIVIDER_WIDTH / 2,
            width: DIVIDER_WIDTH,
            height: COMP_HEIGHT,
            backgroundColor: DIVIDER_COLOR,
            opacity: DIVIDER_OPACITY,
            zIndex: 5,
          }}
        />

        {/* ── Right Panel: Grandmother / 1955 ────────────────────────────── */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: RIGHT_PANEL_LEFT,
            width: RIGHT_PANEL_WIDTH,
            height: COMP_HEIGHT,
            zIndex: 1,
          }}
        >
          <SplitPanel
            width={RIGHT_PANEL_WIDTH}
            videoSrc={rightVideoSrc}
            tintColor={RIGHT_TINT_COLOR}
            tintOpacity={RIGHT_TINT_OPACITY}
            vignetteColor={RIGHT_VIGNETTE_COLOR}
            vignetteOpacity={RIGHT_VIGNETTE_OPACITY}
            label={RIGHT_LABEL}
            labelX={RIGHT_LABEL_X}
            labelY={RIGHT_LABEL_Y}
            showFilmGrain
            filmGrainOpacity={FILM_GRAIN_OPACITY}
            filmGrainFps={FILM_GRAIN_FPS}
          />
        </div>

        {/* ── Divider Glow Pulse (frames 180-240) ────────────────────────── */}
        <Sequence from={GLOW_START} durationInFrames={GLOW_DURATION} style={{ zIndex: 6 }}>
          <DividerGlow />
        </Sequence>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default ColdOpen01SplitScreenHook;
