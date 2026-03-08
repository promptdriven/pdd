/**
 * WorkflowStep - Individual step card in the workflow
 */

import React from 'react';
import { useCurrentFrame, interpolate, spring } from 'remotion';

interface WorkflowStepProps {
  icon: string;
  name: string;
  duration: string;
  x: number;
  y: number;
  startFrame: number;
  width: number;
  height: number;
  iconSize: number;
  backgroundColor: string;
  borderColor: string;
  glow?: boolean;
  status?: 'complete' | 'in-progress';
}

export const WorkflowStep: React.FC<WorkflowStepProps> = ({
  icon,
  name,
  duration,
  x,
  y,
  startFrame,
  width,
  height,
  iconSize,
  backgroundColor,
  borderColor,
  glow = false,
  status,
}) => {
  const frame = useCurrentFrame();

  const scale = spring({
    frame: frame - startFrame,
    fps: 30,
    config: {
      damping: 18,
      stiffness: 180,
    },
  });

  const opacity = interpolate(
    frame - startFrame,
    [0, 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const glowIntensity = glow
    ? interpolate(
        Math.sin((frame - startFrame) * 0.1),
        [-1, 1],
        [0.3, 0.8]
      )
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - width / 2,
        top: y,
        width,
        height,
        backgroundColor,
        border: `1px solid ${borderColor}`,
        borderRadius: 8,
        display: 'flex',
        alignItems: 'center',
        padding: '0 20px',
        opacity: opacity * scale,
        transform: `scale(${scale})`,
        boxShadow: glow
          ? `0 0 ${20 * glowIntensity}px ${borderColor}${Math.floor(glowIntensity * 255).toString(16).padStart(2, '0')}`
          : 'none',
      }}
    >
      {/* Icon */}
      <div
        style={{
          fontSize: iconSize,
          marginRight: 16,
        }}
      >
        {icon}
      </div>

      {/* Step name */}
      <div
        style={{
          flex: 1,
          fontFamily: 'Inter, sans-serif',
          fontWeight: 600,
          fontSize: 22,
          color: '#E0E6ED',
        }}
      >
        {name}
      </div>

      {/* Duration */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontWeight: 500,
          fontSize: 18,
          color: '#9CA3AF',
        }}
      >
        {duration}
      </div>

      {/* Status indicator */}
      {status === 'in-progress' && (
        <div
          style={{
            marginLeft: 12,
            fontSize: 18,
          }}
        >
          ⏳
        </div>
      )}
      {status === 'complete' && (
        <div
          style={{
            marginLeft: 12,
            fontSize: 18,
          }}
        >
          ✓
        </div>
      )}
    </div>
  );
};
