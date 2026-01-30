import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import { COLORS, TEST_WALLS, BEATS } from "./constants";

/**
 * Renders the four test walls that form a container around the code.
 * Each wall fades in at its designated frame.
 * Walls gain an amber glow during the final state (frame 360+).
 */
export const TestWalls: React.FC = () => {
  const frame = useCurrentFrame();

  // Final glow boost for walls (frame 360+)
  const finalGlowIntensity = interpolate(
    frame,
    [BEATS.FINAL_START, BEATS.FINAL_START + 40],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <svg
      width="1920"
      height="1080"
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <defs>
        {/* Amber glow filter for test walls */}
        <filter
          id="amberGlow"
          x="-50%"
          y="-50%"
          width="200%"
          height="200%"
        >
          <feGaussianBlur in="SourceGraphic" stdDeviation="6" result="blur" />
          <feFlood floodColor={COLORS.TEST_AMBER} floodOpacity="0.6" />
          <feComposite in2="blur" operator="in" result="glowColor" />
          <feMerge>
            <feMergeNode in="glowColor" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {TEST_WALLS.map((wall, i) => {
        // Wall fade-in over 30 frames from its appear time
        const wallOpacity = interpolate(
          frame,
          [wall.appearFrame, wall.appearFrame + 30],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          },
        );

        if (wallOpacity <= 0) return null;

        // Is this wall vertical? (height > width)
        const isVertical = wall.height > wall.width;

        // Label positioning
        const labelX = isVertical
          ? wall.x + (i === 1 ? 20 : -12)
          : wall.x + wall.width / 2;
        const labelY = isVertical
          ? wall.y + wall.height / 2
          : wall.y + (i === 0 ? -12 : 24);
        const labelAnchor = isVertical ? "middle" : "middle";

        // For vertical labels, rotate text
        const labelTransform = isVertical
          ? `rotate(${i === 1 ? 90 : -90}, ${labelX}, ${labelY})`
          : undefined;

        // Apply glow filter only during final state
        const useGlow = finalGlowIntensity > 0.1;

        return (
          <g key={`wall-${i}`} opacity={wallOpacity}>
            {/* Wall bar */}
            <rect
              x={wall.x}
              y={wall.y}
              width={wall.width}
              height={wall.height}
              rx={2}
              fill={COLORS.TEST_AMBER}
              filter={useGlow ? "url(#amberGlow)" : undefined}
            />

            {/* Wall label */}
            <text
              x={labelX}
              y={labelY}
              textAnchor={labelAnchor}
              dominantBaseline="central"
              transform={labelTransform}
              style={{
                fontSize: 12,
                fontFamily:
                  "'JetBrains Mono', 'Fira Code', 'Courier New', monospace",
                fontWeight: 500,
                fill: COLORS.WHITE,
                opacity: 0.85,
              }}
            >
              {wall.label}
            </text>
          </g>
        );
      })}
    </svg>
  );
};
