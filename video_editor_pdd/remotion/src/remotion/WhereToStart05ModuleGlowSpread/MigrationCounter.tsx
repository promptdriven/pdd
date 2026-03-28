import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  COUNTER_X,
  COUNTER_Y,
  COUNTER_FONT_SIZE,
  MIGRATED_GLOW_COLOR,
  COUNTER_MILESTONES,
} from './constants';

const TOTAL_MODULES = 12;

const MigrationCounter: React.FC = () => {
  const frame = useCurrentFrame();

  // Determine current count based on milestones
  let currentCount = COUNTER_MILESTONES[0].count;
  for (let i = 0; i < COUNTER_MILESTONES.length; i++) {
    const milestone = COUNTER_MILESTONES[i];
    if (frame >= milestone.frame) {
      if (i < COUNTER_MILESTONES.length - 1) {
        const next = COUNTER_MILESTONES[i + 1];
        if (frame >= next.frame) {
          currentCount = next.count;
        } else {
          // Animate between milestones
          const progress = interpolate(
            frame,
            [milestone.frame, milestone.frame + 10],
            [0, 1],
            {
              extrapolateLeft: 'clamp',
              extrapolateRight: 'clamp',
              easing: Easing.out(Easing.quad),
            }
          );
          currentCount =
            progress >= 1 ? milestone.count : milestone.count;
        }
      } else {
        currentCount = milestone.count;
      }
    }
  }

  // Find the actual displayed count: step through milestones
  let displayCount = COUNTER_MILESTONES[0].count;
  for (const milestone of COUNTER_MILESTONES) {
    if (frame >= milestone.frame) {
      displayCount = milestone.count;
    }
  }

  // Subtle pulse after frame 270 (hold phase)
  const pulseOpacity =
    frame >= 270
      ? interpolate(Math.sin(frame * 0.08), [-1, 1], [0.85, 1])
      : 1;

  // Scale bump when counter changes
  let counterScale = 1;
  for (const milestone of COUNTER_MILESTONES) {
    if (frame >= milestone.frame && frame < milestone.frame + 12) {
      counterScale = interpolate(
        frame,
        [milestone.frame, milestone.frame + 6, milestone.frame + 12],
        [1, 1.15, 1],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        }
      );
      break;
    }
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: COUNTER_X,
        top: COUNTER_Y,
        transform: `translate(-50%, -50%) scale(${counterScale})`,
        fontFamily: 'Inter, sans-serif',
        fontSize: COUNTER_FONT_SIZE,
        fontWeight: 600,
        color: MIGRATED_GLOW_COLOR,
        opacity: pulseOpacity,
        whiteSpace: 'nowrap',
      }}
    >
      {displayCount} / {TOTAL_MODULES} modules migrated
    </div>
  );
};

export default MigrationCounter;
