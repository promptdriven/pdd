import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PURPLE_ACCENT,
  CONNECTOR_ORIGINS,
  PROVEN_WALL_TARGETS,
  CONNECTORS_START,
  CONNECTORS_END,
  PANEL_SLIDE_OUT_START,
  PANEL_SLIDE_OUT_END,
} from './constants';

/**
 * Animated dashed connector lines from the annotation panel to proven mold walls.
 * Lines draw progressively from origin to target, then fade out with the panel.
 */
export const ConnectorLines: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [CONNECTORS_START, CONNECTORS_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const fadeOut = interpolate(
    frame,
    [PANEL_SLIDE_OUT_START, PANEL_SLIDE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  if (frame < CONNECTORS_START) return null;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        pointerEvents: 'none',
        opacity: fadeOut,
      }}
    >
      <defs>
        <filter id="connectorGlow">
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {PROVEN_WALL_TARGETS.map((target, i) => {
        const ox = CONNECTOR_ORIGINS.x;
        const oy = CONNECTOR_ORIGINS.y + i * 40 - 20;
        const tx = target.x;
        const ty = target.y;

        // Curved path via a control point
        const midX = (ox + tx) / 2;
        const midY = oy + (ty - oy) * 0.3;
        const t = drawProgress;

        // Quadratic bezier point at parameter t
        const bx =
          (1 - t) * (1 - t) * ox + 2 * (1 - t) * t * midX + t * t * tx;
        const by =
          (1 - t) * (1 - t) * oy + 2 * (1 - t) * t * midY + t * t * ty;

        // Build partial path
        const pathSegments = 20;
        let d = `M ${ox} ${oy}`;
        for (let s = 1; s <= pathSegments; s++) {
          const st = (s / pathSegments) * t;
          const px =
            (1 - st) * (1 - st) * ox +
            2 * (1 - st) * st * midX +
            st * st * tx;
          const py =
            (1 - st) * (1 - st) * oy +
            2 * (1 - st) * st * midY +
            st * st * ty;
          d += ` L ${px} ${py}`;
        }

        // Small target circle
        const circleOpacity = drawProgress > 0.8 ? (drawProgress - 0.8) / 0.2 : 0;

        return (
          <g key={i} filter="url(#connectorGlow)">
            <path
              d={d}
              fill="none"
              stroke={PURPLE_ACCENT}
              strokeWidth={2}
              strokeDasharray="8 4"
              opacity={0.3}
            />
            <circle
              cx={bx}
              cy={by}
              r={6}
              fill={PURPLE_ACCENT}
              opacity={circleOpacity * 0.5}
            />
          </g>
        );
      })}
    </svg>
  );
};
