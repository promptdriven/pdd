import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import { COLORS, TRACK, MILESTONES, ANIMATION_TIMING } from './constants';
import { TimelineTrack } from './TimelineTrack';
import { MilestoneDot } from './MilestoneDot';
import { Playhead } from './Playhead';

export const AnimationSection05AnimationTimeline: React.FC = () => {
  const frame = useCurrentFrame();

  // Playhead position: linear sweep from startX to endX (frame 40-120)
  const playheadX = interpolate(
    frame,
    [ANIMATION_TIMING.playheadStart, ANIMATION_TIMING.playheadEnd],
    [TRACK.startX, TRACK.endX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Horizontal timeline track */}
      <TimelineTrack />

      {/* Milestone dots with labels */}
      {MILESTONES.map((milestone, index) => (
        <MilestoneDot
          key={milestone.label}
          x={milestone.x}
          y={TRACK.y}
          color={milestone.color}
          label={milestone.label}
          index={index}
          playheadX={playheadX}
        />
      ))}

      {/* Sweeping playhead */}
      <Playhead currentX={playheadX} />
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05AnimationTimelineProps = {};

export default AnimationSection05AnimationTimeline;
