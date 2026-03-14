import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from 'remotion';
import { useVisualMediaSrc } from '../_shared/visual-runtime';
import {
  COLORS,
  ANIMATION,
  STAT_BADGES,
  BADGE_LAYOUT,
  resolveWaveOverlayLayout,
} from './constants';
import { GridOverlay } from './GridOverlay';
import { WaveformGraph } from './WaveformGraph';
import { StatBadge } from './StatBadge';

export const VeoSection04WaveDataOverlay: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolveWaveOverlayLayout(width, height);

  // Resolve background video from visual media context
  const backgroundSrc = useVisualMediaSrc('backgroundSrc', 'veo/04_veo_broll.mp4');

  // Dark overlay fades in: opacity 0 → 60% over frames 0–8, easeOutQuad
  // Starts at 10% so content is visible from frame 0
  const overlayOpacity = interpolate(
    frame,
    [ANIMATION.overlayFadeStart, ANIMATION.overlayFadeEnd],
    [0.1, 0.6],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Badge animation timing per spec
  const badgeTimings = [
    { start: ANIMATION.badge1Start, end: ANIMATION.badge1End },
    { start: ANIMATION.badge2Start, end: ANIMATION.badge2End },
    { start: ANIMATION.badge3Start, end: ANIMATION.badge3End },
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: '#00FF00' }}>
      {/* Background Veo footage still */}
      {backgroundSrc ? (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile(backgroundSrc)}
            style={{
              width: '100%',
              height: '100%',
              objectFit: 'cover',
            }}
            startFrom={15}
            muted
          />
        </AbsoluteFill>
      ) : null}

      {/* Semi-transparent dark overlay (#0B1120 fading to 60%) */}
      <AbsoluteFill
        style={{
          backgroundColor: '#00FF00',
          opacity: overlayOpacity,
        }}
      />

      {/* Subtle horizontal grid lines at 25% intervals */}
      <GridOverlay layout={layout} />

      {/* Sinusoidal waveform graph in the lower third */}
      <WaveformGraph layout={layout} />

      {/* Floating stat badges in the upper-right quadrant */}
      {STAT_BADGES.map((badge, i) => (
        <StatBadge
          key={badge.label}
          layout={layout}
          label={badge.label}
          value={badge.value}
          icon={badge.icon}
          y={BADGE_LAYOUT.startY + i * BADGE_LAYOUT.gapY}
          animStart={badgeTimings[i].start}
          animEnd={badgeTimings[i].end}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection04WaveDataOverlayProps = {};

export default VeoSection04WaveDataOverlay;
