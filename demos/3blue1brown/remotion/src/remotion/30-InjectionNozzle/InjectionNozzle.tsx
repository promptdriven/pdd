import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, InjectionNozzlePropsType } from "./constants";

export const InjectionNozzle: React.FC<InjectionNozzlePropsType> = ({
  showLabels = true,
}) => {
  const frame = useCurrentFrame();

  // Nozzle visibility
  const nozzleOpacity = interpolate(
    frame,
    [BEATS.NOZZLE_START, BEATS.NOZZLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Glow intensity
  const glowIntensity = interpolate(
    frame,
    [BEATS.GLOW_START, BEATS.GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Label opacity
  const labelOpacity = showLabels
    ? interpolate(
        frame,
        [BEATS.LABEL_START, BEATS.LABEL_END],
        [0, 1],
        { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
      )
    : 0;

  // Explanation opacity
  const explanationOpacity = interpolate(
    frame,
    [BEATS.EXPLANATION_START, BEATS.EXPLANATION_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
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
      <svg width="100%" height="100%" viewBox="0 0 1920 1080" style={{ opacity: nozzleOpacity }}>
        {/* Nozzle shape - funnel-like */}
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

        {/* Main nozzle body */}
        <path
          d={`
            M ${nozzle.centerX - nozzle.topWidth / 2} ${nozzle.centerY - nozzle.height / 2}
            L ${nozzle.centerX + nozzle.topWidth / 2} ${nozzle.centerY - nozzle.height / 2}
            L ${nozzle.centerX + nozzle.width / 2} ${nozzle.centerY + nozzle.height / 2}
            L ${nozzle.centerX - nozzle.width / 2} ${nozzle.centerY + nozzle.height / 2}
            Z
          `}
          fill="url(#nozzleGradient)"
          stroke={COLORS.NOZZLE_BLUE}
          strokeWidth={3}
          filter={glowIntensity > 0 ? "url(#nozzleGlow)" : "none"}
        />

        {/* Nozzle opening */}
        <ellipse
          cx={nozzle.centerX}
          cy={nozzle.centerY + nozzle.height / 2}
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
              x1={nozzle.centerX + offset * 1.4}
              y1={nozzle.centerY - nozzle.height / 2 + 30}
              x2={nozzle.centerX + offset}
              y2={nozzle.centerY + nozzle.height / 2 - 30}
              stroke={COLORS.NOZZLE_BLUE}
              strokeWidth={1}
              opacity={0.5}
              strokeDasharray="8 4"
            />
          );
        })}
      </svg>

      {/* Labels */}
      {labelOpacity > 0 && (
        <div style={{ opacity: labelOpacity }}>
          {/* Main label */}
          <div
            style={{
              position: "absolute",
              left: nozzle.centerX + nozzle.topWidth / 2 + 40,
              top: nozzle.centerY - nozzle.height / 2 + 20,
              fontSize: 24,
              fontWeight: "bold",
              color: COLORS.NOZZLE_BLUE,
              fontFamily: "sans-serif",
            }}
          >
            PROMPT
          </div>
          <div
            style={{
              position: "absolute",
              left: nozzle.centerX + nozzle.topWidth / 2 + 40,
              top: nozzle.centerY - nozzle.height / 2 + 50,
              fontSize: 16,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
            }}
          >
            The Injection Nozzle
          </div>

          {/* Sublabel */}
          <div
            style={{
              position: "absolute",
              left: nozzle.centerX + nozzle.topWidth / 2 + 40,
              top: nozzle.centerY - nozzle.height / 2 + 90,
              fontSize: 14,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
              maxWidth: 300,
              lineHeight: 1.5,
            }}
          >
            Intent flows in through the prompt.
            <br />
            Defines WHAT the code should do.
          </div>
        </div>
      )}

      {/* Explanation */}
      {explanationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 100,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: explanationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 24,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
              marginBottom: 12,
            }}
          >
            Second: the prompt
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_GRAY,
              fontFamily: "sans-serif",
            }}
          >
            Natural language intent that guides what code gets generated
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
