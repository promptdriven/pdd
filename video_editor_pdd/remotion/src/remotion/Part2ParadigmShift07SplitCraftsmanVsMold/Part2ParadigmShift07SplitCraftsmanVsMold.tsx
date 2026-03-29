import React from 'react';
import {
  AbsoluteFill,
  OffthreadVideo,
  interpolate,
  useCurrentFrame,
  Easing,
  staticFile,
} from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PANEL_WIDTH,
  DIVIDER_GAP,
  DIVIDER_WIDTH,
  DIVIDER_COLOR,
  DIVIDER_OPACITY,
  BACKGROUND_COLOR,
  AURA_AMBER,
  AURA_BLUE,
  AURA_INTENSE_AMBER,
  AURA_INTENSE_BLUE,
  AURA_INTENSE_OPACITY,
  LABEL_LEFT,
  LABEL_RIGHT,
  LABEL_FONT_SIZE,
  LABEL_PRIMARY_OPACITY,
  LABEL_APPEAR_FRAME,
  FADE_IN_START,
  FADE_IN_END,
  FADE_OUT_START,
  FADE_OUT_END,
} from './constants';
import AuraGlow from './AuraGlow';
import PartDissolveReappear from './PartDissolveReappear';

// Try to import useVisualMediaAssetSrc; fall back to staticFile if unavailable.
let useVisualMediaAssetSrc: ((alias: string) => string) | undefined;
try {
  // eslint-disable-next-line @typescript-eslint/no-var-requires
  const mod = require('../_shared/visual-runtime');
  useVisualMediaAssetSrc = mod.useVisualMediaAssetSrc;
} catch {
  // Not available — will use staticFile fallback
}

function useMediaSrc(alias: string, fallbackFile: string): string {
  if (useVisualMediaAssetSrc) {
    try {
      // eslint-disable-next-line react-hooks/rules-of-hooks
      const src = useVisualMediaAssetSrc(alias);
      if (src) return src;
    } catch {
      // fall through
    }
  }
  return staticFile(`veo/${fallbackFile}`);
}

export const defaultPart2ParadigmShift07SplitCraftsmanVsMoldProps = {};

export const Part2ParadigmShift07SplitCraftsmanVsMold: React.FC = () => {
  const frame = useCurrentFrame();

  // Global fade in / fade out
  const fadeIn = interpolate(frame, [FADE_IN_START, FADE_IN_END], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const fadeOut = interpolate(frame, [FADE_OUT_START, FADE_OUT_END], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.in(Easing.quad),
  });

  const globalOpacity = Math.min(fadeIn, fadeOut);

  // Divider opacity (fades in with split)
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

  // Label fade in
  const labelOpacity = interpolate(
    frame,
    [LABEL_APPEAR_FRAME, LABEL_APPEAR_FRAME + 30],
    [0, LABEL_PRIMARY_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Resolve media
  const leftSrc = useMediaSrc('leftSrc', 'craftsman_carving.mp4');
  const rightSrc = useMediaSrc('rightSrc', 'mold_plastic_flow.mp4');

  const panelStyle: React.CSSProperties = {
    position: 'absolute',
    top: 0,
    width: PANEL_WIDTH,
    height: '100%',
    overflow: 'hidden',
  };

  const videoStyle: React.CSSProperties = {
    width: '100%',
    height: '100%',
    objectFit: 'cover',
  };

  const labelStyle: React.CSSProperties = {
    position: 'absolute',
    bottom: 36,
    left: 0,
    right: 0,
    textAlign: 'center',
    fontSize: LABEL_FONT_SIZE,
    fontFamily:
      "'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif",
    fontWeight: 600,
    letterSpacing: '0.02em',
    color: '#FFFFFF',
    opacity: labelOpacity,
    textShadow: '0 2px 8px rgba(0,0,0,0.7), 0 1px 3px rgba(0,0,0,0.9)',
    padding: '0 20px',
    pointerEvents: 'none' as const,
  };

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      <AbsoluteFill style={{ opacity: globalOpacity }}>
        {/* ===== LEFT PANEL: Craftsman ===== */}
        <div style={{ ...panelStyle, left: 0 }}>
          <OffthreadVideo
            src={leftSrc}
            style={videoStyle}
            muted
            startFrom={0}
          />

          {/* Amber aura — centered on the object (lower-center where chair is) */}
          <AuraGlow
            color={AURA_AMBER}
            intenseColor={AURA_INTENSE_AMBER}
            intenseOpacity={AURA_INTENSE_OPACITY}
            centerX={0.5}
            centerY={0.55}
          />

          {/* Label */}
          <div style={labelStyle}>{LABEL_LEFT}</div>
        </div>

        {/* ===== CENTER DIVIDER ===== */}
        <div
          style={{
            position: 'absolute',
            top: 0,
            left: PANEL_WIDTH + DIVIDER_GAP / 2 - DIVIDER_WIDTH / 2,
            width: DIVIDER_WIDTH,
            height: '100%',
            backgroundColor: DIVIDER_COLOR,
            opacity: dividerOpacity,
            zIndex: 10,
          }}
        />

        {/* ===== RIGHT PANEL: Injection Mold ===== */}
        <div style={{ ...panelStyle, left: PANEL_WIDTH + DIVIDER_GAP }}>
          <OffthreadVideo
            src={rightSrc}
            style={videoStyle}
            muted
            startFrom={0}
          />

          {/* Blue aura — centered on the mold (upper-center where the mold apparatus is) */}
          <AuraGlow
            color={AURA_BLUE}
            intenseColor={AURA_INTENSE_BLUE}
            intenseOpacity={AURA_INTENSE_OPACITY}
            centerX={0.5}
            centerY={0.4}
          />

          {/* Part dissolve/reappear effect */}
          <PartDissolveReappear />

          {/* Label */}
          <div style={labelStyle}>{LABEL_RIGHT}</div>
        </div>
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift07SplitCraftsmanVsMold;
