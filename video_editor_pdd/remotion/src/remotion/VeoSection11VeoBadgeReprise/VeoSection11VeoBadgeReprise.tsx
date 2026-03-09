import React from 'react';
import { AbsoluteFill, OffthreadVideo, staticFile } from 'remotion';
import { COLORS } from './constants';
import { DimmingOverlay } from './DimmingOverlay';
import { VeoWordmark } from './VeoWordmark';
import { Tagline } from './Tagline';
import { AccentLine } from './AccentLine';
import { ParticleRing } from './ParticleRing';

export const VeoSection11VeoBadgeReprise: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Forest canopy footage background */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile('veo/veo_section.mp4')}
          style={{ width: '100%', height: '100%', objectFit: 'cover' }}
        />
      </AbsoluteFill>

      {/* Dimming overlay fades in over frames 0-10 */}
      <DimmingOverlay />

      {/* Particle ring orbits behind the text */}
      <ParticleRing />

      {/* Veo wordmark scales in */}
      <VeoWordmark />

      {/* Tagline fades in and slides up */}
      <Tagline />

      {/* Accent line expands below tagline */}
      <AccentLine />
    </AbsoluteFill>
  );
};

export const defaultVeoSection11VeoBadgeRepriseProps = {};

export default VeoSection11VeoBadgeReprise;
