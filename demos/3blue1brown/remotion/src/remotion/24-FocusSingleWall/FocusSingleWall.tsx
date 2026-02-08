import React, { useMemo } from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, FOCUS_TEST, FocusSingleWallPropsType } from "./constants";

export const FocusSingleWall: React.FC<FocusSingleWallPropsType> = ({
  testInput = "null",
  testOutput = "None",
}) => {
  const frame = useCurrentFrame();

  // Wall visibility
  const wallOpacity = interpolate(
    frame,
    [BEATS.WALL_VISIBLE_START, BEATS.WALL_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Zoom progress
  const zoomScale = interpolate(
    frame,
    [BEATS.ZOOM_START, BEATS.ZOOM_END],
    [1, 2.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Liquid position: approaches wall from left, stops at wall edge
  const liquidX = interpolate(
    frame,
    [BEATS.LIQUID_APPROACH_START, BEATS.LIQUID_APPROACH_END],
    [300, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  // Impact glow on wall (peaks at impact, holds at moderate)
  const impactGlow = interpolate(
    frame,
    [BEATS.IMPACT_FRAME, BEATS.IMPACT_FRAME + 10, BEATS.IMPACT_FRAME + 60],
    [0, 1, 0.4],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Liquid compression effect at impact
  const liquidCompression = frame >= BEATS.IMPACT_FRAME
    ? interpolate(
        frame,
        [BEATS.IMPACT_FRAME, BEATS.IMPACT_FRAME + 8, BEATS.IMPACT_FRAME + 30],
        [0, 0.15, 0],
        { extrapolateRight: "clamp" }
      )
    : 0;

  // Splash particles
  const splashProgress = frame >= BEATS.IMPACT_FRAME
    ? interpolate(
        frame,
        [BEATS.IMPACT_FRAME, BEATS.SPLASH_END],
        [0, 1],
        { extrapolateRight: "clamp" }
      )
    : -1;

  // Highlight glow (for label glow)
  const highlightGlow = interpolate(
    frame,
    [BEATS.HIGHLIGHT_START, BEATS.HIGHLIGHT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Explanation text
  const explanationOpacity = interpolate(
    frame,
    [BEATS.EXPLANATION_START, BEATS.EXPLANATION_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Generate deterministic splash particles
  const splashParticles = useMemo(() => {
    const particles: Array<{ angle: number; speed: number; size: number }> = [];
    for (let i = 0; i < 12; i++) {
      // Splash outward from impact point (mostly upward and downward from wall face)
      const angle = -90 + (Math.random() - 0.5) * 160; // Spread in left-facing semicircle
      particles.push({
        angle: (angle * Math.PI) / 180,
        speed: 30 + Math.random() * 60,
        size: 3 + Math.random() * 5,
      });
    }
    return particles;
  }, []);

  // Wall dimensions
  const wallWidth = 200;
  const wallHeight = 300;
  const wallCenterX = 960;
  const wallCenterY = 540;

  // Liquid body dimensions
  const liquidWidth = 180;
  const liquidHeight = 200;
  const liquidBaseX = wallCenterX - wallWidth / 2 - liquidX;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Zooming container */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: `translate(-50%, -50%) scale(${zoomScale})`,
          opacity: wallOpacity,
        }}
      >
        <svg
          width={1920}
          height={1080}
          viewBox="0 0 1920 1080"
          style={{ position: "absolute", top: -540, left: -960 }}
        >
          {/* Approaching liquid body */}
          {frame >= BEATS.LIQUID_APPROACH_START && (
            <g>
              {/* Main liquid mass */}
              <rect
                x={liquidBaseX - liquidWidth}
                y={wallCenterY - liquidHeight / 2}
                width={liquidWidth + (liquidCompression > 0 ? liquidCompression * 40 : 0)}
                height={liquidHeight}
                rx={8}
                fill={COLORS.LIQUID_BLUE}
                opacity={0.6}
                style={{
                  filter: `drop-shadow(0 0 8px ${COLORS.LIQUID_BLUE})`,
                }}
              />
              {/* Liquid leading edge (brighter) */}
              <rect
                x={liquidBaseX - 15}
                y={wallCenterY - liquidHeight / 2 + 10}
                width={15 + (liquidCompression > 0 ? liquidCompression * 30 : 0)}
                height={liquidHeight - 20}
                rx={4}
                fill={COLORS.LIQUID_BLUE}
                opacity={0.8}
              />
              {/* Code-like texture lines inside liquid */}
              {[0, 1, 2, 3, 4].map((lineIdx) => {
                const lineY = wallCenterY - liquidHeight / 2 + 30 + lineIdx * 35;
                const lineW = 60 + (lineIdx % 3) * 30;
                return (
                  <rect
                    key={lineIdx}
                    x={liquidBaseX - liquidWidth + 20}
                    y={lineY}
                    width={lineW}
                    height={3}
                    rx={1.5}
                    fill="rgba(255,255,255,0.15)"
                  />
                );
              })}
            </g>
          )}

          {/* Splash particles at impact */}
          {splashProgress >= 0 && splashProgress < 1 && (
            <g>
              {splashParticles.map((p, i) => {
                const px = wallCenterX - wallWidth / 2 + Math.cos(p.angle) * p.speed * splashProgress;
                const py = wallCenterY + Math.sin(p.angle) * p.speed * splashProgress;
                const particleOpacity = 1 - splashProgress;
                const particleSize = p.size * (1 - splashProgress * 0.6);
                return (
                  <circle
                    key={i}
                    cx={px}
                    cy={py}
                    r={particleSize}
                    fill={COLORS.LIQUID_BLUE}
                    opacity={particleOpacity * 0.8}
                  />
                );
              })}
            </g>
          )}

          {/* Ripple ring at impact on wall */}
          {splashProgress >= 0 && splashProgress < 1 && (
            <ellipse
              cx={wallCenterX - wallWidth / 2}
              cy={wallCenterY}
              rx={10 + splashProgress * 50}
              ry={10 + splashProgress * 80}
              fill="none"
              stroke={COLORS.IMPACT_AMBER}
              strokeWidth={2}
              opacity={(1 - splashProgress) * 0.7}
            />
          )}

          {/* Wall segment */}
          <rect
            x={wallCenterX - wallWidth / 2}
            y={wallCenterY - wallHeight / 2}
            width={wallWidth}
            height={wallHeight}
            rx={8}
            fill={`rgba(217, 148, 74, ${0.3 + 0.4 * impactGlow})`}
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={3}
            style={{
              filter: impactGlow > 0
                ? `drop-shadow(0 0 ${40 * impactGlow}px ${COLORS.WALLS_AMBER})`
                : "none",
            }}
          />

          {/* Test label on wall */}
          <text
            x={wallCenterX}
            y={wallCenterY - 20}
            textAnchor="middle"
            fill={COLORS.WALLS_AMBER}
            fontSize={24}
            fontFamily="JetBrains Mono, monospace"
            style={{
              textShadow: `0 0 ${10 * highlightGlow}px ${COLORS.WALLS_AMBER}`,
            }}
          >
            {testInput}
          </text>
          <text
            x={wallCenterX}
            y={wallCenterY + 8}
            textAnchor="middle"
            fill={COLORS.LABEL_WHITE}
            fontSize={28}
          >
            {"\u2192"}
          </text>
          <text
            x={wallCenterX}
            y={wallCenterY + 38}
            textAnchor="middle"
            fill={COLORS.WALLS_AMBER}
            fontSize={24}
            fontFamily="JetBrains Mono, monospace"
            style={{
              textShadow: `0 0 ${10 * highlightGlow}px ${COLORS.WALLS_AMBER}`,
            }}
          >
            {testOutput}
          </text>
        </svg>
      </div>

      {/* Explanation panel */}
      {explanationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: explanationOpacity,
          }}
        >
          <div
            style={{
              display: "inline-block",
              background: "rgba(30, 30, 46, 0.9)",
              padding: "20px 40px",
              borderRadius: 12,
              border: `1px solid ${COLORS.WALLS_AMBER}`,
            }}
          >
            <div
              style={{
                fontSize: 22,
                color: COLORS.LABEL_WHITE,
                fontFamily: "sans-serif",
                marginBottom: 12,
              }}
            >
              {FOCUS_TEST.description}
            </div>
            <div
              style={{
                fontSize: 16,
                color: COLORS.LABEL_GRAY,
                fontFamily: "sans-serif",
              }}
            >
              The code literally cannot violate this constraint.
            </div>
          </div>
        </div>
      )}

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: wallOpacity,
        }}
      >
        <span
          style={{
            fontSize: 20,
            fontFamily: "sans-serif",
            color: COLORS.WALLS_AMBER,
          }}
        >
          Focusing on a single constraint...
        </span>
      </div>
    </AbsoluteFill>
  );
};
