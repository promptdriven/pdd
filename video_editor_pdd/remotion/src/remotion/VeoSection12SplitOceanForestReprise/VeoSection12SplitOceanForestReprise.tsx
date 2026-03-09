import React from 'react';
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from 'remotion';
import { CANVAS, COLORS, ANIMATION } from './constants';
import { WipeEdge } from './WipeEdge';
import { ProgressBar } from './ProgressBar';

export const defaultVeoSection12SplitOceanForestRepriseProps = {};

export const VeoSection12SplitOceanForestReprise: React.FC = () => {
  const frame = useCurrentFrame();

  // Calculate wipe X position across three phases:
  // Phase 1 (0-30): easeOutQuad from 0 to 960
  // Phase 2 (30-60): hold at 960
  // Phase 3 (60-85): easeInQuad from 960 to 1920
  let wipeX: number;
  if (frame <= ANIMATION.wipeInEnd) {
    wipeX = interpolate(
      frame,
      [ANIMATION.wipeInStart, ANIMATION.wipeInEnd],
      [0, CANVAS.width / 2],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.poly(2)),
      }
    );
  } else if (frame <= ANIMATION.holdEnd) {
    wipeX = CANVAS.width / 2;
  } else {
    wipeX = interpolate(
      frame,
      [ANIMATION.wipeOutStart, ANIMATION.wipeOutEnd],
      [CANVAS.width / 2, CANVAS.width],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.poly(2)),
      }
    );
  }

  // Progress bar tracks wipe position as 0-1
  const progress = wipeX / CANVAS.width;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Base layer: Ocean wave sunset (full frame, behind) */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.width,
          height: CANVAS.height,
          zIndex: 1,
        }}
      >
        <OffthreadVideo
          src={staticFile('veo/veo_section.mp4')}
          style={{
            width: CANVAS.width,
            height: CANVAS.height,
            objectFit: 'cover',
          }}
        />
      </div>

      {/* Reveal layer: Forest canopy aerial, clipped by wipe position */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: CANVAS.width,
          height: CANVAS.height,
          clipPath: `inset(0 ${CANVAS.width - wipeX}px 0 0)`,
          zIndex: 2,
        }}
      >
        <OffthreadVideo
          src={staticFile('veo/veo_section.mp4')}
          style={{
            width: CANVAS.width,
            height: CANVAS.height,
            objectFit: 'cover',
            // Slight color shift to differentiate "forest" from "ocean"
            filter: 'hue-rotate(90deg) saturate(1.2)',
          }}
        />
      </div>

      {/* Wipe edge with glow */}
      <WipeEdge wipeX={wipeX} />

      {/* Bottom progress bar */}
      <ProgressBar progress={progress} />
    </AbsoluteFill>
  );
};

export default VeoSection12SplitOceanForestReprise;
