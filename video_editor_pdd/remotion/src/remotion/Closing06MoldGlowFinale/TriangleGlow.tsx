import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import {
  TRIANGLE_VERTICES,
  EDGE_COLOR_FROM,
  EDGE_COLOR_TO,
  EDGE_WIDTH_FROM,
  EDGE_WIDTH_TO,
  EDGE_OPACITY_FROM,
  EDGE_OPACITY_TO,
  GLOW_LAYERS,
  DURATION_FRAMES,
} from './constants';

function verticesPath(verts: [number, number][]): string {
  return `M ${verts[0][0]},${verts[0][1]} L ${verts[1][0]},${verts[1][1]} L ${verts[2][0]},${verts[2][1]} Z`;
}

export const TriangleGlow: React.FC = () => {
  const frame = useCurrentFrame();
  const path = verticesPath(TRIANGLE_VERTICES);

  // Edge intensification over frames 0-90
  const edgeProgress = interpolate(frame, [0, 90], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const edgeColor = interpolateColors(
    edgeProgress,
    [0, 1],
    [EDGE_COLOR_FROM, EDGE_COLOR_TO]
  );

  const edgeWidth = interpolate(
    edgeProgress,
    [0, 1],
    [EDGE_WIDTH_FROM, EDGE_WIDTH_TO]
  );

  const edgeOpacity = interpolate(
    edgeProgress,
    [0, 1],
    [EDGE_OPACITY_FROM, EDGE_OPACITY_TO]
  );

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        {GLOW_LAYERS.map((layer, i) => (
          <filter key={i} id={`edgeGlow${i}`} x="-100%" y="-100%" width="300%" height="300%">
            <feGaussianBlur stdDeviation={layer.blur} />
          </filter>
        ))}
      </defs>

      {/* Glow layers (rendered behind the main edge) */}
      {GLOW_LAYERS.map((layer, i) => {
        const glowProgress = interpolate(
          frame,
          [layer.delay, layer.delay + 60],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
        );

        return (
          <path
            key={`glow-${i}`}
            d={path}
            fill="none"
            stroke={layer.color}
            strokeWidth={edgeWidth + layer.blur}
            opacity={layer.opacity * glowProgress}
            filter={`url(#edgeGlow${i})`}
          />
        );
      })}

      {/* Main triangle edge */}
      <path
        d={path}
        fill="none"
        stroke={edgeColor}
        strokeWidth={edgeWidth}
        opacity={edgeOpacity}
        strokeLinejoin="round"
      />
    </svg>
  );
};
