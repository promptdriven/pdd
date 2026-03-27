import React from "react";
import { AbsoluteFill, staticFile } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  BACKGROUND_COLOR,
  DIVIDER_COLOR,
  DIVIDER_WIDTH_PX,
  DIVIDER_OPACITY,
  DIVIDER_GAP,
  PANEL_WIDTH,
  DIVIDER_FADE_FRAMES,
  PANEL_FADE_FRAMES,
  LABEL_FONT_SIZE,
  LABEL_COLOR,
  LABEL_OPACITY,
  LABEL_BG_OPACITY,
} from "./constants";
import { SplitDivider } from "./SplitDivider";
import { VideoPanel } from "./VideoPanel";

export const defaultPart1Economics14SplitDeveloperGrandmaProps = {};

// Attempt to import the shared visual-runtime hook.
// If unavailable (standalone usage), we fall back to staticFile.
let useVisualMediaAssetSrc: ((alias: string) => string | null) | null = null;
try {
  const mod = require("../_shared/visual-runtime");
  useVisualMediaAssetSrc = mod.useVisualMediaAssetSrc ?? null;
} catch {
  // Not available — will use staticFile fallback
}

function useMediaSrc(
  alias: string,
  fallbackAsset: string
): string {
  if (useVisualMediaAssetSrc) {
    const resolved = useVisualMediaAssetSrc(alias);
    if (resolved) return resolved;
    // Try defaultSrc as secondary fallback
    const defaultResolved = useVisualMediaAssetSrc("defaultSrc");
    if (defaultResolved) return defaultResolved;
  }
  return staticFile(fallbackAsset);
}

/**
 * Split-screen: Developer with Cursor (left) / Grandmother darning (right).
 * 510 frames @ 30fps (~17s). Respectful comparison of two skilled craftspeople
 * using the best tools of their eras.
 */
export const Part1Economics14SplitDeveloperGrandma: React.FC = () => {
  const leftSrc = useMediaSrc("leftSrc", "veo/developer_cursor_p1.mp4");
  const rightSrc = useMediaSrc("rightSrc", "veo/grandmother_darning_p1.mp4");

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      {/* Left panel: Developer with Cursor */}
      <VideoPanel
        src={leftSrc}
        side="left"
        panelWidth={PANEL_WIDTH}
        canvasHeight={CANVAS_HEIGHT}
        canvasWidth={CANVAS_WIDTH}
        dividerGap={DIVIDER_GAP}
        fadeFrames={PANEL_FADE_FRAMES}
        label="Developer with Cursor"
        labelFontSize={LABEL_FONT_SIZE}
        labelColor={LABEL_COLOR}
        labelOpacity={LABEL_OPACITY}
        labelBgOpacity={LABEL_BG_OPACITY}
      />

      {/* Right panel: Grandmother darning */}
      <VideoPanel
        src={rightSrc}
        side="right"
        panelWidth={PANEL_WIDTH}
        canvasHeight={CANVAS_HEIGHT}
        canvasWidth={CANVAS_WIDTH}
        dividerGap={DIVIDER_GAP}
        fadeFrames={PANEL_FADE_FRAMES}
        label="Grandmother darning"
        labelFontSize={LABEL_FONT_SIZE}
        labelColor={LABEL_COLOR}
        labelOpacity={LABEL_OPACITY}
        labelBgOpacity={LABEL_BG_OPACITY}
      />

      {/* Center divider */}
      <SplitDivider
        canvasWidth={CANVAS_WIDTH}
        canvasHeight={CANVAS_HEIGHT}
        dividerColor={DIVIDER_COLOR}
        dividerWidthPx={DIVIDER_WIDTH_PX}
        dividerOpacity={DIVIDER_OPACITY}
        fadeFrames={DIVIDER_FADE_FRAMES}
      />
    </AbsoluteFill>
  );
};

export default Part1Economics14SplitDeveloperGrandma;
