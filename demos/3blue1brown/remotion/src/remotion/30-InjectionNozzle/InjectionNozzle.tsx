import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, CONCEPT_LABELS, InjectionNozzlePropsType } from "./constants";

export const InjectionNozzle: React.FC<InjectionNozzlePropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Mold cross-section visibility
  const moldOpacity = interpolate(
    frame,
    [BEATS.MOLD_START, BEATS.MOLD_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Wall dimming (from full to 40%)
  const wallOpacity = interpolate(
    frame,
    [BEATS.WALL_DIM_START, BEATS.WALL_DIM_END],
    [1, 0.4],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Nozzle glow intensity
  const glowIntensity = interpolate(
    frame,
    [BEATS.NOZZLE_GLOW_START, BEATS.NOZZLE_GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Pulse animation (scale oscillation)
  const pulseScale = 1 + Math.sin(frame * 0.1) * 0.05;

  // Section title opacity
  const titleOpacity = interpolate(
    frame,
    [BEATS.TITLE_START, BEATS.TITLE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Nozzle dimensions
  const nozzle = {
    width: 200,
    height: 300,
    topWidth: 280,
    centerX: 960,
    centerY: 450,
  };

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      <svg width="100%" height="100%" viewBox="0 0 1920 1080">
        {/* Defs for filters and gradients */}
        <defs>
          <linearGradient id="nozzleGradient" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={COLORS.NOZZLE_BLUE} stopOpacity={0.8} />
            <stop offset="100%" stopColor={COLORS.NOZZLE_BLUE} stopOpacity={0.4} />
          </linearGradient>
          <filter id="nozzleGlow" x="-50%" y="-50%" width="200%" height="200%">
            <feGaussianBlur stdDeviation={15 * glowIntensity} result="blur" />
            <feMerge>
              <feMergeNode in="blur" />
              <feMergeNode in="SourceGraphic" />
            </feMerge>
          </filter>
        </defs>

        {/* Mold cross-section walls (dimmed) */}
        <g opacity={moldOpacity * wallOpacity}>
          {/* Left wall */}
          <rect
            x={nozzle.centerX - 400}
            y={nozzle.centerY - 200}
            width={20}
            height={500}
            fill="rgba(217, 148, 74, 0.3)"
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
          />
          {/* Right wall */}
          <rect
            x={nozzle.centerX + 380}
            y={nozzle.centerY - 200}
            width={20}
            height={500}
            fill="rgba(217, 148, 74, 0.3)"
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
          />
          {/* Bottom wall */}
          <rect
            x={nozzle.centerX - 400}
            y={nozzle.centerY + 300}
            width={820}
            height={20}
            fill="rgba(217, 148, 74, 0.3)"
            stroke={COLORS.WALLS_AMBER}
            strokeWidth={2}
          />
        </g>

        {/* Nozzle with glow and pulse */}
        <g
          transform={`translate(${nozzle.centerX}, ${nozzle.centerY}) scale(${pulseScale})`}
          opacity={moldOpacity}
        >
          {/* Main nozzle body */}
          <path
            d={`
              M ${-nozzle.topWidth / 2} ${-nozzle.height / 2}
              L ${nozzle.topWidth / 2} ${-nozzle.height / 2}
              L ${nozzle.width / 2} ${nozzle.height / 2}
              L ${-nozzle.width / 2} ${nozzle.height / 2}
              Z
            `}
            fill="url(#nozzleGradient)"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth={3}
            filter={glowIntensity > 0 ? "url(#nozzleGlow)" : "none"}
          />

          {/* Nozzle opening */}
          <ellipse
            cx={0}
            cy={nozzle.height / 2}
            rx={nozzle.width / 2}
            ry={20}
            fill="rgba(74, 144, 217, 0.6)"
            stroke={COLORS.NOZZLE_BLUE}
            strokeWidth={2}
          />

          {/* Flow lines inside nozzle */}
          {[...Array(5)].map((_, i) => {
            const offset = (i - 2) * 30;
            return (
              <line
                key={i}
                x1={offset * 1.4}
                y1={-nozzle.height / 2 + 30}
                x2={offset}
                y2={nozzle.height / 2 - 30}
                stroke={COLORS.NOZZLE_BLUE}
                strokeWidth={1}
                opacity={0.5}
                strokeDasharray="8 4"
              />
            );
          })}
        </g>

        {/* Connection lines from labels to nozzle */}
        {showLabels && CONCEPT_LABELS.map((label, i) => {
          const opacity = interpolate(
            frame,
            [label.startFrame, label.startFrame + BEATS.LABEL_FADE_DURATION],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          if (opacity <= 0) return null;
          return (
            <line
              key={`line-${i}`}
              x1={nozzle.centerX + label.position.x}
              y1={nozzle.centerY + label.position.y}
              x2={nozzle.centerX}
              y2={nozzle.centerY}
              stroke={COLORS.NOZZLE_BLUE}
              strokeWidth={2}
              opacity={opacity * 0.5}
              strokeDasharray="4 4"
            />
          );
        })}
      </svg>

      {/* Concept Labels (intent, requirements, constraints) */}
      {showLabels && CONCEPT_LABELS.map((label, i) => {
        const opacity = interpolate(
          frame,
          [label.startFrame, label.startFrame + BEATS.LABEL_FADE_DURATION],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
        );
        if (opacity <= 0) return null;
        return (
          <div
            key={i}
            style={{
              position: "absolute",
              left: nozzle.centerX + label.position.x,
              top: nozzle.centerY + label.position.y,
              opacity,
              transform: "translate(-50%, -50%)",
            }}
          >
            {/* Circle background */}
            <div
              style={{
                width: 100,
                height: 100,
                borderRadius: "50%",
                background: `rgba(74, 144, 217, 0.15)`,
                border: `2px solid ${COLORS.NOZZLE_BLUE}`,
                display: "flex",
                flexDirection: "column",
                alignItems: "center",
                justifyContent: "center",
                padding: 8,
              }}
            >
              <div
                style={{
                  fontSize: 16,
                  fontWeight: "bold",
                  color: COLORS.NOZZLE_BLUE,
                  fontFamily: "sans-serif",
                  marginBottom: 4,
                }}
              >
                {label.text}
              </div>
              <div
                style={{
                  fontSize: 11,
                  color: COLORS.LABEL_GRAY,
                  fontFamily: "sans-serif",
                  textAlign: "center",
                }}
              >
                {label.description}
              </div>
            </div>
          </div>
        );
      })}

      {/* Section Title */}
      {titleOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 100,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: titleOpacity,
          }}
        >
          <div
            style={{
              fontSize: 32,
              fontWeight: "bold",
              color: COLORS.NOZZLE_BLUE,
              fontFamily: "sans-serif",
              marginBottom: 12,
              letterSpacing: 2,
            }}
          >
            PROMPT CAPITAL
          </div>
          <div
            style={{
              fontSize: 20,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
            }}
          >
            The Specification
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
