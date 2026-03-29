import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { BG_COLOR, TOTAL_FRAMES, WALL_COLOR, LABEL_TEXT_COLOR } from './constants';
import { BlueprintGrid } from './BlueprintGrid';
import { MoldCrossSection } from './MoldCrossSection';
import { WallCounter } from './WallCounter';
import { TerminalScroll } from './TerminalScroll';

export const defaultPart3MoldParts06RatchetTimelapseProps = {};

/** Title overlay that fades in then out */
const TitleOverlay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 15, 45, 60], [0.9, 0.9, 0.9, 0], {
    extrapolateRight: 'clamp',
    extrapolateLeft: 'clamp',
  });

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 80,
        bottom: 80,
        opacity,
      }}
    >
      <div
        style={{
          fontFamily: "'Inter', sans-serif",
          fontSize: 14,
          fontWeight: 600,
          color: WALL_COLOR,
          letterSpacing: '0.15em',
          textTransform: 'uppercase',
          marginBottom: 6,
        }}
      >
        Ratchet Effect
      </div>
      <div
        style={{
          fontFamily: "'Inter', sans-serif",
          fontSize: 11,
          color: LABEL_TEXT_COLOR,
          opacity: 0.62,
        }}
      >
        Tests only accumulate — the mold only gets more precise
      </div>
    </div>
  );
};

/** Narration cue text synced to speech */
const NarrationCue: React.FC = () => {
  const frame = useCurrentFrame();

  // Show narration text segments
  const cues: { text: string; startFrame: number; endFrame: number }[] = [
    { text: '"This is the ratchet effect."', startFrame: 0, endFrame: 80 },
    { text: '"Tests only accumulate."', startFrame: 80, endFrame: 150 },
    { text: '"Each wall constrains all future generations."', startFrame: 150, endFrame: 250 },
  ];

  const activeCue = cues.find((c) => frame >= c.startFrame && frame < c.endFrame);
  if (!activeCue) return null;

  const localFrame = frame - activeCue.startFrame;
  const cueOpacity = interpolate(
    localFrame,
    [0, 8, activeCue.endFrame - activeCue.startFrame - 10, activeCue.endFrame - activeCue.startFrame],
    [0, 0.78, 0.78, 0],
    { extrapolateRight: 'clamp', extrapolateLeft: 'clamp' }
  );

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 160,
        left: 0,
        right: 0,
        display: 'flex',
        justifyContent: 'center',
        pointerEvents: 'none',
      }}
    >
      <div
        style={{
          fontFamily: "'Inter', sans-serif",
          fontSize: 20,
          fontWeight: 500,
          color: '#FFFFFF',
          opacity: cueOpacity,
          textAlign: 'center',
          maxWidth: 700,
          lineHeight: 1.4,
          textShadow: '0 2px 8px rgba(0,0,0,0.6)',
        }}
      >
        {activeCue.text}
      </div>
    </div>
  );
};

/** Horizontal rule / progress indicator */
const ProgressBar: React.FC = () => {
  const frame = useCurrentFrame();
  const progress = interpolate(frame, [0, TOTAL_FRAMES], [0, 100], {
    extrapolateRight: 'clamp',
  });

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 0,
        left: 0,
        width: `${progress}%`,
        height: 3,
        backgroundColor: WALL_COLOR,
        opacity: 0.7,
      }}
    />
  );
};

export const Part3MoldParts06RatchetTimelapse: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: 'hidden',
      }}
    >
      {/* Blueprint grid background */}
      <BlueprintGrid />

      {/* Main mold visualization with walls, liquid, flashes */}
      <MoldCrossSection />

      {/* Wall counter (top-right) */}
      <WallCounter />

      {/* Terminal scroll (bottom-right) */}
      <TerminalScroll />

      {/* Title overlay (fades out early) */}
      <TitleOverlay />

      {/* Narration cue text */}
      <NarrationCue />

      {/* Progress bar */}
      <ProgressBar />
    </AbsoluteFill>
  );
};

export default Part3MoldParts06RatchetTimelapse;
