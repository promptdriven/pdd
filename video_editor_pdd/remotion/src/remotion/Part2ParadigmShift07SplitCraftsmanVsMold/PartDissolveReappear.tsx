import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PART_DISSOLVE_START,
  PART_DISSOLVE_END,
  PART_REAPPEAR_BEAT,
  PART_REAPPEAR_END,
} from './constants';

/**
 * Overlay that simulates the plastic part dissolving (fade to semi-transparent white)
 * and then a new identical part appearing. Placed within the right panel.
 */
const PartDissolveReappear: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < PART_DISSOLVE_START) return null;

  // Dissolve: plastic part fades out (overlay fades IN to obscure it)
  const dissolveOpacity = interpolate(
    frame,
    [PART_DISSOLVE_START, PART_DISSOLVE_END],
    [0, 0.85],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.bezier(0.32, 0, 0.67, 0)),
    },
  );

  // Hold dissolved state during beat
  const holdOpacity =
    frame >= PART_DISSOLVE_END && frame < PART_REAPPEAR_BEAT ? 0.85 : 0;

  // Reappear: overlay fades OUT to reveal new part
  const reappearOpacity = interpolate(
    frame,
    [PART_REAPPEAR_BEAT, PART_REAPPEAR_END],
    [0.85, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)),
    },
  );

  let opacity: number;
  if (frame < PART_DISSOLVE_END) {
    opacity = dissolveOpacity;
  } else if (frame < PART_REAPPEAR_BEAT) {
    opacity = holdOpacity || 0.85;
  } else if (frame < PART_REAPPEAR_END) {
    opacity = reappearOpacity;
  } else {
    opacity = 0;
  }

  // Flash effect on reappear
  const flashOpacity =
    frame >= PART_REAPPEAR_BEAT && frame < PART_REAPPEAR_BEAT + 6
      ? interpolate(
          frame,
          [PART_REAPPEAR_BEAT, PART_REAPPEAR_BEAT + 6],
          [0.4, 0],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        )
      : 0;

  return (
    <AbsoluteFill style={{ pointerEvents: 'none' }}>
      {/* Dissolve/reappear mask — covers the lower portion where parts eject */}
      <div
        style={{
          position: 'absolute',
          bottom: 0,
          left: '10%',
          width: '80%',
          height: '55%',
          background: `radial-gradient(ellipse 100% 100% at 50% 70%, rgba(0,0,0,${opacity}) 0%, transparent 85%)`,
        }}
      />
      {/* White flash on reappear */}
      {flashOpacity > 0 && (
        <div
          style={{
            position: 'absolute',
            bottom: 0,
            left: '15%',
            width: '70%',
            height: '45%',
            background: `radial-gradient(ellipse 80% 80% at 50% 70%, rgba(255,255,255,${flashOpacity}) 0%, transparent 80%)`,
          }}
        />
      )}
    </AbsoluteFill>
  );
};

export default PartDissolveReappear;
