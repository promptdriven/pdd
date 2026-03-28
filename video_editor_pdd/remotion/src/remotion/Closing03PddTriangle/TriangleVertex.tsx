import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  VERTEX_DOT_RADIUS,
  VERTEX_GLOW_RADIUS,
  VERTEX_GLOW_OPACITY,
  LABEL_FONT_SIZE,
  LABEL_FONT_FAMILY,
  LABEL_FONT_WEIGHT,
} from './constants';

interface TriangleVertexProps {
  x: number;
  y: number;
  label: string;
  color: string;
  fadeStart: number;
  fadeDuration: number;
  pulseActive: boolean;
  pulseCycleFrames: number;
}

const TriangleVertex: React.FC<TriangleVertexProps> = ({
  x,
  y,
  label,
  color,
  fadeStart,
  fadeDuration,
  pulseActive,
  pulseCycleFrames,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeStart + fadeDuration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Glow pulse when active
  let glowScale = 1;
  let glowOpacity = VERTEX_GLOW_OPACITY;
  if (pulseActive && frame >= 130) {
    const pulseFrame = (frame - 130) % pulseCycleFrames;
    const pulseProgress = pulseFrame / pulseCycleFrames;
    const sineVal = Math.sin(pulseProgress * Math.PI * 2);
    glowScale = 1 + sineVal * 0.15;
    glowOpacity = VERTEX_GLOW_OPACITY + sineVal * 0.1;
  }

  // Label position: above for top vertex, below for bottom vertices
  const isTop = y < 400;
  const labelY = isTop ? y - 30 : y + 35;

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: '100%', height: '100%', opacity }}>
      {/* Glow */}
      <div
        style={{
          position: 'absolute',
          left: x - VERTEX_GLOW_RADIUS,
          top: y - VERTEX_GLOW_RADIUS,
          width: VERTEX_GLOW_RADIUS * 2,
          height: VERTEX_GLOW_RADIUS * 2,
          borderRadius: '50%',
          background: `radial-gradient(circle, ${color}${Math.round(glowOpacity * 255).toString(16).padStart(2, '0')} 0%, transparent 70%)`,
          transform: `scale(${glowScale})`,
        }}
      />
      {/* Dot */}
      <div
        style={{
          position: 'absolute',
          left: x - VERTEX_DOT_RADIUS,
          top: y - VERTEX_DOT_RADIUS,
          width: VERTEX_DOT_RADIUS * 2,
          height: VERTEX_DOT_RADIUS * 2,
          borderRadius: '50%',
          backgroundColor: color,
          boxShadow: `0 0 20px ${color}`,
        }}
      />
      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: labelY,
          transform: 'translateX(-50%)',
          fontSize: LABEL_FONT_SIZE,
          fontFamily: LABEL_FONT_FAMILY,
          fontWeight: LABEL_FONT_WEIGHT,
          color,
          textAlign: 'center',
          letterSpacing: '2px',
          textShadow: `0 0 12px ${color}`,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </div>
    </div>
  );
};

export default TriangleVertex;
