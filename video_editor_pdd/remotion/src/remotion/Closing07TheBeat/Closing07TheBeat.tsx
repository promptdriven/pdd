import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  Sequence,
} from 'remotion';
import { GhostTriangle } from './GhostTriangle';
import { SingleParticle } from './SingleParticle';
import { Vignette } from './Vignette';
import {
  BG_START,
  BG_END,
  BG_DARKEN_DURATION,
  PARTICLE_START_FRAME,
  PARTICLE_DRIFT_DURATION,
} from './constants';

export const defaultClosing07TheBeatProps = {};

/**
 * Section 7.7: The Beat — Dramatic Silence
 *
 * A deliberate dramatic pause. The luminous triangle fades to a ghost state,
 * the background darkens to near-black, and a single particle drifts upward
 * through the triangle center with a brief glint. No narration, no text —
 * the emptiness creates anticipatory weight before the final thesis.
 *
 * Duration: 120 frames (4s @ 30fps)
 */
export const Closing07TheBeat: React.FC = () => {
  const frame = useCurrentFrame();

  // Background darkening: #080E1A → #060A12 over 30 frames with easeInOut(sine)
  const bgProgress = interpolate(frame, [0, BG_DARKEN_DURATION], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.sin),
  });

  // Interpolate RGB channels between start and end background colors
  // #080E1A = rgb(8, 14, 26)
  // #060A12 = rgb(6, 10, 18)
  const r = Math.round(interpolate(bgProgress, [0, 1], [8, 6]));
  const g = Math.round(interpolate(bgProgress, [0, 1], [14, 10]));
  const b = Math.round(interpolate(bgProgress, [0, 1], [26, 18]));
  const bgColor = `rgb(${r}, ${g}, ${b})`;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: bgColor,
      }}
    >
      {/* Ghost triangle — fading from luminous to barely visible */}
      <GhostTriangle />

      {/* Vignette overlay — darkens edges for tunnel-vision effect */}
      <Vignette />

      {/* Single drifting particle — starts at frame 30 */}
      <Sequence from={PARTICLE_START_FRAME} durationInFrames={PARTICLE_DRIFT_DURATION + 10}>
        <SingleParticle />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Closing07TheBeat;
