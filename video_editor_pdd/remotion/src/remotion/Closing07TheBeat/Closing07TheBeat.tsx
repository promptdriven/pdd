import React from 'react';
import { AbsoluteFill, Sequence, useCurrentFrame, interpolate, Easing } from 'remotion';
import { BG_START, BG_END, DURATION_FRAMES } from './constants';
import { GhostTriangle } from './GhostTriangle';
import { SingleParticle } from './SingleParticle';
import { RadialVignette } from './RadialVignette';

export const defaultClosing07TheBeatProps = {};

/**
 * Section 7.7: The Beat — Dramatic Silence
 *
 * A deliberate dramatic pause. The luminous triangle fades to a ghost state,
 * a single particle drifts upward through the center, and the background
 * deepens to near-black. No narration, no text — the emptiness is the point.
 *
 * Duration: 120 frames (4s @ 30fps)
 */
const parseHex = (hex: string): [number, number, number] => [
  parseInt(hex.slice(1, 3), 16),
  parseInt(hex.slice(3, 5), 16),
  parseInt(hex.slice(5, 7), 16),
];

export const Closing07TheBeat: React.FC = () => {
  const frame = useCurrentFrame();

  // Background darkens from BG_START to BG_END over 30 frames
  const bgProgress = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.sin),
  });

  const [sR, sG, sB] = parseHex(BG_START);
  const [eR, eG, eB] = parseHex(BG_END);
  const bgR = Math.round(interpolate(bgProgress, [0, 1], [sR, eR]));
  const bgG = Math.round(interpolate(bgProgress, [0, 1], [sG, eG]));
  const bgB = Math.round(interpolate(bgProgress, [0, 1], [sB, eB]));
  const bgColor = `rgb(${bgR}, ${bgG}, ${bgB})`;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: bgColor,
        overflow: 'hidden',
      }}
    >
      {/* Ghost triangle — visible from frame 0, fading to ghost state */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <GhostTriangle />
      </Sequence>

      {/* Vignette overlay — starts fading in at frame 20 */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <RadialVignette />
      </Sequence>

      {/* Single drifting particle — starts at frame 30, lasts 90 frames */}
      <Sequence from={30} durationInFrames={90}>
        <SingleParticle />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Closing07TheBeat;
