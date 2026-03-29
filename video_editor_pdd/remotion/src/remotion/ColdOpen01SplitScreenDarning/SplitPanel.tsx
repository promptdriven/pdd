import React from 'react';
import {
  AbsoluteFill,
  OffthreadVideo,
  interpolate,
  useCurrentFrame,
  Easing,
} from 'remotion';
import {
  CANVAS_HEIGHT,
  PANEL_WIDTH,
  DIVIDER_GAP,
  CROSSFADE_START,
  CROSSFADE_FRAMES,
} from './constants';

/**
 * Props accepted by SplitPanel.
 * `clip1Src` and `clip2Src` are video paths ready for <OffthreadVideo>.
 * `side` controls whether this panel sits on the left or right of the split.
 */
export interface SplitPanelProps {
  clip1Src: string | null;
  clip2Src: string | null;
  side: 'left' | 'right';
}

const SplitPanel: React.FC<SplitPanelProps> = ({
  clip1Src,
  clip2Src,
  side,
}) => {
  const frame = useCurrentFrame();

  // Clip 2 fades in over CROSSFADE_FRAMES starting at CROSSFADE_START.
  const clip2Opacity = interpolate(
    frame,
    [CROSSFADE_START, CROSSFADE_START + CROSSFADE_FRAMES],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const leftOffset = side === 'left' ? 0 : PANEL_WIDTH + DIVIDER_GAP;

  return (
    <div
      style={{
        position: 'absolute',
        left: leftOffset,
        top: 0,
        width: PANEL_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: 'hidden',
      }}
    >
      {/* Clip 1 — plays from start, hidden once clip2 fully covers */}
      {clip1Src && (
        <AbsoluteFill>
          <OffthreadVideo
            src={clip1Src}
            style={{
              width: '100%',
              height: '100%',
              objectFit: 'cover',
            }}
          />
        </AbsoluteFill>
      )}

      {/* Clip 2 — fades in via crossfade starting at CROSSFADE_START */}
      {clip2Src && frame >= CROSSFADE_START && (
        <AbsoluteFill style={{ opacity: clip2Opacity }}>
          <OffthreadVideo
            src={clip2Src}
            style={{
              width: '100%',
              height: '100%',
              objectFit: 'cover',
            }}
            startFrom={Math.max(0, frame - CROSSFADE_START)}
          />
        </AbsoluteFill>
      )}

      {/* Fallback when no video sources are provided */}
      {!clip1Src && !clip2Src && (
        <AbsoluteFill
          style={{
            backgroundColor: side === 'left' ? '#0F172A' : '#1A0F0A',
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'center',
          }}
        >
          <div
            style={{
              color: '#FFFFFF',
              fontSize: 28,
              fontFamily: 'sans-serif',
              fontWeight: 600,
              opacity: 0.85,
              textAlign: 'center',
              padding: 40,
            }}
          >
            {side === 'left'
              ? 'Developer patching code'
              : 'Grandmother darning socks'}
          </div>
        </AbsoluteFill>
      )}
    </div>
  );
};

export default SplitPanel;
