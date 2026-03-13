import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  useVideoConfig,
  interpolate,
  Easing,
  Img,
  staticFile,
  OffthreadVideo,
} from 'remotion';
import { useVisualMediaSrc } from '../_shared/visual-runtime';
import {
  COLORS,
  ANIMATION,
  DIMENSIONS,
  STAT_BADGES,
  resolveWaveOverlayLayout,
} from './constants';
import { GridLines } from './GridLines';
import { ChartAxes } from './ChartAxes';
import { SineWaveLine } from './SineWaveLine';
import { StatCallout } from './StatCallout';

export const VeoSection04WaveDataOverlay: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();
  const layout = resolveWaveOverlayLayout(width, height);

  // Resolve background video source via visual media hook
  const backgroundSrc = useVisualMediaSrc('backgroundSrc', 'veo/04_veo_broll.mp4');

  // Background fades in over first 8 frames, starting at 0.4 so content is visible at frame 0
  const bgOpacity = interpolate(
    frame,
    [ANIMATION.gridDrawStart, ANIMATION.gridDrawEnd],
    [0.4, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Title opacity matches grid draw, starts at 0.3 for frame-0 visibility
  const titleOpacity = interpolate(
    frame,
    [ANIMATION.gridDrawStart, ANIMATION.gridDrawEnd],
    [0.3, 0.9],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
      {/* Blurred background video still with dark overlay */}
      {backgroundSrc ? (
        <AbsoluteFill style={{ opacity: bgOpacity }}>
          <OffthreadVideo
            src={staticFile(backgroundSrc)}
            style={{
              width: '100%',
              height: '100%',
              objectFit: 'cover',
              filter: 'blur(6px) brightness(0.5)',
            }}
            startFrom={15}
            muted
          />
          {/* Dark overlay */}
          <AbsoluteFill style={{ backgroundColor: COLORS.background }} />
        </AbsoluteFill>
      ) : (
        <AbsoluteFill style={{ backgroundColor: '#0A1628', opacity: bgOpacity }} />
      )}

      {/* Chart title: "WAVE ANALYSIS" */}
      <div
        style={{
          position: 'absolute',
          left: DIMENSIONS.titleX * layout.scaleX,
          top: DIMENSIONS.titleY * layout.scaleY,
          fontFamily: layout.typography.chartTitle.fontFamily,
          fontSize: layout.typography.chartTitle.fontSize,
          fontWeight: layout.typography.chartTitle.fontWeight,
          letterSpacing: layout.typography.chartTitle.letterSpacing,
          color: COLORS.titleText,
          opacity: titleOpacity,
        }}
      >
        WAVE ANALYSIS
      </div>

      {/* Grid lines */}
      <GridLines layout={layout} />

      {/* Chart axes with labels */}
      <ChartAxes layout={layout} />

      {/* Animated sine wave line with fill */}
      <SineWaveLine layout={layout} />

      {/* Floating stat callout badges */}
      {STAT_BADGES.map((badge, i) => (
        <StatCallout
          key={badge.label}
          layout={layout}
          label={badge.label}
          value={badge.value}
          x={badge.x}
          y={badge.y}
          delayFrames={i * ANIMATION.badgeStagger}
        />
      ))}
    </AbsoluteFill>
  );
};

export const defaultVeoSection04WaveDataOverlayProps = {};

export default VeoSection04WaveDataOverlay;
