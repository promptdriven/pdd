import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { PULSE, COLORS, ARROWS } from './constants';

interface DataPulseProps {
  startFrame: number;
  endFrame: number;
}

export const DataPulse: React.FC<DataPulseProps> = ({ startFrame, endFrame }) => {
  const frame = useCurrentFrame();

  if (frame < startFrame || frame > endFrame) {
    return null;
  }

  // Build a waypoint path: arrow1 start -> arrow1 end, arrow2 start -> arrow2 end
  const waypoints = [
    { x: ARROWS[0].fromX, y: ARROWS[0].fromY },
    { x: ARROWS[0].toX, y: ARROWS[0].toY },
    { x: ARROWS[1].fromX, y: ARROWS[1].fromY },
    { x: ARROWS[1].toX, y: ARROWS[1].toY },
  ];

  // Compute segment lengths
  const segments: number[] = [];
  let totalLength = 0;
  for (let i = 0; i < waypoints.length - 1; i++) {
    const dx = waypoints[i + 1].x - waypoints[i].x;
    const dy = waypoints[i + 1].y - waypoints[i].y;
    const len = Math.sqrt(dx * dx + dy * dy);
    segments.push(len);
    totalLength += len;
  }

  // Linear progress along entire path
  const progress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const distanceTraveled = progress * totalLength;

  // Find current position along the path
  let accumulated = 0;
  let pulseX = waypoints[0].x;
  let pulseY = waypoints[0].y;

  for (let i = 0; i < segments.length; i++) {
    if (accumulated + segments[i] >= distanceTraveled) {
      const segProgress = (distanceTraveled - accumulated) / segments[i];
      pulseX = waypoints[i].x + (waypoints[i + 1].x - waypoints[i].x) * segProgress;
      pulseY = waypoints[i].y + (waypoints[i + 1].y - waypoints[i].y) * segProgress;
      break;
    }
    accumulated += segments[i];
  }

  // If we've traveled past all segments, snap to end
  if (distanceTraveled >= totalLength) {
    pulseX = waypoints[waypoints.length - 1].x;
    pulseY = waypoints[waypoints.length - 1].y;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: pulseX - PULSE.radius / 2,
        top: pulseY - PULSE.radius / 2,
        width: PULSE.radius,
        height: PULSE.radius,
        borderRadius: '50%',
        backgroundColor: COLORS.pulseGlow,
        boxShadow: `0 0 ${PULSE.blur}px ${COLORS.pulseGlow}, 0 0 ${PULSE.blur * 2}px ${COLORS.pulseGlow}80`,
      }}
    />
  );
};
