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
import { useVisualMediaSrc } from '../_shared/visual-runtime';

export const defaultVeoSection12SplitOceanForestRepriseProps = {};

export const VeoSection12SplitOceanForestReprise: React.FC = () => {
  const frame = useCurrentFrame();
  const baseSrc = useVisualMediaSrc('baseSrc', 'veo/veo_section.mp4');
  const revealSrc = useVisualMediaSrc('revealSrc', baseSrc ?? 'veo/veo_section.mp4');

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
      {/* Base layer: Forest canopy aerial (full frame, behind) */}
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
        {baseSrc ? (
          <OffthreadVideo
            src={staticFile(baseSrc)}
            style={{
              width: CANVAS.width,
              height: CANVAS.height,
              objectFit: 'cover',
            }}
          />
        ) : null}
      </div>

      {/* Reveal layer: Ocean wave sunset, clipped by wipe position */}
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
        {revealSrc ? (
          <OffthreadVideo
            src={staticFile(revealSrc)}
            style={{
              width: CANVAS.width,
              height: CANVAS.height,
              objectFit: 'cover',
            }}
          />
        ) : null}
      </div>

      {/* Wipe edge with glow */}
      <WipeEdge wipeX={wipeX} />

      {/* Bottom progress bar */}
      <ProgressBar progress={progress} />
    </AbsoluteFill>
  );
};

export default VeoSection12SplitOceanForestReprise;
