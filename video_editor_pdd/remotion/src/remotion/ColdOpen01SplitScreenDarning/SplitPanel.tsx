import React from 'react';
import {
  OffthreadVideo,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import {
  CANVAS_HEIGHT,
  PANEL_WIDTH,
  CROSSFADE_START,
  CROSSFADE_DURATION,
  CLIP_A_END,
  CLIP_B_END,
} from './constants';

export interface SplitPanelProps {
  /** Video src for the first clip (frames 0–160) */
  clipASrc: string;
  /** Video src for the second clip (frames 150–270) */
  clipBSrc: string;
  /** CSS `left` offset for panel positioning */
  leftOffset: number;
}

/**
 * Renders one half of the split screen with two video clips
 * that crossfade at the segment boundary.
 */
export const SplitPanel: React.FC<SplitPanelProps> = ({
  clipASrc,
  clipBSrc,
  leftOffset,
}) => {
  const frame = useCurrentFrame();

  // Opacity of clip B during the crossfade region
  const clipBOpacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.42, 0, 0.58, 1), // easeInOut(cubic)
    },
  );

  // Clip A fades out as clip B fades in
  const clipAOpacity = 1 - clipBOpacity;

  // Whether clips should still be rendered (avoid rendering beyond their range)
  const showClipA = frame < CLIP_A_END + CROSSFADE_DURATION;
  const showClipB = frame >= CROSSFADE_START && frame < CLIP_B_END;

  const panelStyle: React.CSSProperties = {
    position: 'absolute',
    left: leftOffset,
    top: 0,
    width: PANEL_WIDTH,
    height: CANVAS_HEIGHT,
    overflow: 'hidden',
  };

  const videoStyle: React.CSSProperties = {
    width: PANEL_WIDTH,
    height: CANVAS_HEIGHT,
    objectFit: 'cover',
  };

  return (
    <div style={panelStyle}>
      {/* Clip A */}
      {showClipA && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            opacity: clipAOpacity,
          }}
        >
          <OffthreadVideo
            src={clipASrc}
            style={videoStyle}
            muted
          />
        </div>
      )}

      {/* Clip B – crossfades in */}
      {showClipB && (
        <div
          style={{
            position: 'absolute',
            inset: 0,
            opacity: clipBOpacity,
          }}
        >
          <OffthreadVideo
            src={clipBSrc}
            style={videoStyle}
            muted
          />
        </div>
      )}
    </div>
  );
};

export default SplitPanel;
