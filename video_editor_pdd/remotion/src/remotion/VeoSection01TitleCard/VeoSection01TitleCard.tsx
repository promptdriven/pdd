import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, CANVAS, ANIMATION } from './constants';
import { FilmGrainOverlay } from './FilmGrainOverlay';
import { LightStreak } from './LightStreak';
import { LetterRevealTitle } from './LetterRevealTitle';
import { RadialGlowPulse } from './RadialGlowPulse';

export const VeoSection01TitleCard: React.FC = () => {
  const frame = useCurrentFrame();

  // Background fades in from black over frames 0-10
  const backgroundOpacity = interpolate(
    frame,
    [ANIMATION.backgroundFadeStart, ANIMATION.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: '#00FF00',
      }}
    >
      <AbsoluteFill
        style={{
          opacity: backgroundOpacity,
        }}
      >
        {/* Dark charcoal background with warm radial center highlight */}
        <AbsoluteFill
          style={{
            backgroundColor: COLORS.background,
          }}
        />
        <div
          style={{
            position: 'absolute',
            top: CANVAS.height / 2 - 400,
            left: CANVAS.width / 2 - 400,
            width: 800,
            height: 800,
            borderRadius: '50%',
            background: `radial-gradient(circle, ${COLORS.gradientCenter}90 0%, transparent 65%)`,
            pointerEvents: 'none',
          }}
        />

        {/* Film grain texture overlay at 3% opacity */}
        <FilmGrainOverlay />

        {/* Radial glow pulse behind title */}
        <RadialGlowPulse />

        {/* Amber light streak sweeping left-to-right */}
        <LightStreak />

        {/* Letter-by-letter title reveal */}
        <LetterRevealTitle />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export const defaultVeoSection01TitleCardProps = {};

export default VeoSection01TitleCard;
