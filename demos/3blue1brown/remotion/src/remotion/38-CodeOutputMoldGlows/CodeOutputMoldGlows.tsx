import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, CodeOutputMoldGlowsPropsType } from "./constants";

// MoldInterior component showing three colored bars representing the mold components
const MoldInterior: React.FC<{ glowIntensity: number }> = ({ glowIntensity }) => {
  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 8, padding: 20 }}>
      {/* Prompt layer - blue */}
      <div
        style={{
          height: 6,
          backgroundColor: `rgba(74, 144, 217, ${0.4 * glowIntensity})`,
          borderRadius: 3,
          width: "80%",
          boxShadow: `0 0 8px rgba(74, 144, 217, ${0.3 * glowIntensity})`,
        }}
      />
      {/* Test layers - amber */}
      <div
        style={{
          height: 6,
          backgroundColor: `rgba(217, 148, 74, ${0.4 * glowIntensity})`,
          borderRadius: 3,
          width: "90%",
          boxShadow: `0 0 8px rgba(217, 148, 74, ${0.3 * glowIntensity})`,
        }}
      />
      <div
        style={{
          height: 6,
          backgroundColor: `rgba(217, 148, 74, ${0.4 * glowIntensity})`,
          borderRadius: 3,
          width: "70%",
          boxShadow: `0 0 8px rgba(217, 148, 74, ${0.3 * glowIntensity})`,
        }}
      />
      {/* Grounding layer - green */}
      <div
        style={{
          height: 6,
          backgroundColor: `rgba(90, 170, 110, ${0.4 * glowIntensity})`,
          borderRadius: 3,
          width: "60%",
          boxShadow: `0 0 8px rgba(90, 170, 110, ${0.3 * glowIntensity})`,
        }}
      />
    </div>
  );
};

export const CodeOutputMoldGlows: React.FC<CodeOutputMoldGlowsPropsType> = ({
  showMessages = true,
}) => {
  const frame = useCurrentFrame();

  // Breathing animation - sinusoidal oscillation
  const breathCycle = Math.sin(frame * 0.035) * 0.1 + 0.9;

  // Mold glow (increases over time)
  const baseMoldGlow = interpolate(
    frame,
    [0, 60],
    [0.4, 1.0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Apply breathing to mold glow
  const moldGlow = baseMoldGlow * breathCycle;

  // Mold appearance
  const moldOpacity = interpolate(
    frame,
    [0, 45],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Plastic appearance
  const plasticOpacity = interpolate(
    frame,
    [15, 50],
    [0, 0.4],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // First text: "The code is just plastic."
  const text1Opacity = interpolate(
    frame,
    [120, 160],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Second text: "The mold is what matters."
  const text2Opacity = interpolate(
    frame,
    [210, 250],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Glow boost when second message appears
  const finalGlowBoost = interpolate(
    frame,
    [210, 270],
    [1.0, 1.4],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Final combined glow intensity
  const finalGlowIntensity = moldGlow * finalGlowBoost;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* The Mold - UNIFIED GLOWING SHAPE */}
      <div
        style={{
          position: "absolute",
          left: 350,
          top: 280,
          width: 240,
          height: 200,
          opacity: moldOpacity,
        }}
      >
        {/* Multi-layer glow - three separate layers with different blur radii */}
        <div
          style={{
            position: "absolute",
            inset: -20,
            borderRadius: 20,
            background: `radial-gradient(ellipse, rgba(74, 144, 217, ${0.15 * finalGlowIntensity}), transparent)`,
            filter: `blur(${15 * finalGlowIntensity}px)`,
          }}
        />
        <div
          style={{
            position: "absolute",
            inset: -15,
            borderRadius: 20,
            background: `radial-gradient(ellipse, rgba(217, 148, 74, ${0.12 * finalGlowIntensity}), transparent)`,
            filter: `blur(${12 * finalGlowIntensity}px)`,
          }}
        />
        <div
          style={{
            position: "absolute",
            inset: -10,
            borderRadius: 20,
            background: `radial-gradient(ellipse, rgba(90, 170, 110, ${0.10 * finalGlowIntensity}), transparent)`,
            filter: `blur(${10 * finalGlowIntensity}px)`,
          }}
        />

        {/* Mold shape container */}
        <div
          style={{
            position: "relative",
            width: "100%",
            height: "100%",
            borderRadius: 16,
            border: "2px solid rgba(255, 255, 255, 0.3)",
            backgroundColor: "rgba(255, 255, 255, 0.05)",
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: `
              0 0 ${30 * finalGlowIntensity}px rgba(74, 144, 217, 0.3),
              0 0 ${25 * finalGlowIntensity}px rgba(217, 148, 74, 0.2),
              0 0 ${20 * finalGlowIntensity}px rgba(90, 170, 110, 0.2)
            `,
          }}
        >
          {/* Mold interior with colored bars */}
          <MoldInterior glowIntensity={finalGlowIntensity} />
        </div>
      </div>

      {/* The Plastic Part - ABSTRACT GEOMETRIC FORM */}
      <div
        style={{
          position: "absolute",
          left: 700,
          top: 310,
          width: 160,
          height: 140,
          opacity: plasticOpacity,
          borderRadius: 12,
          backgroundColor: "rgba(136, 136, 136, 0.15)",
          border: "1px solid rgba(136, 136, 136, 0.2)",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        {/* Abstract code lines - simple bars of varying widths */}
        <div style={{ padding: 16, width: "100%" }}>
          {[70, 55, 80, 45, 65].map((w, i) => (
            <div
              key={i}
              style={{
                height: 4,
                backgroundColor: "rgba(136, 136, 136, 0.25)",
                marginBottom: 4,
                borderRadius: 2,
                width: `${w}%`,
              }}
            />
          ))}
        </div>
      </div>

      {/* Text container */}
      <div
        style={{
          position: "absolute",
          bottom: 140,
          left: 0,
          right: 0,
          textAlign: "center",
        }}
      >
        {/* First line: understated */}
        <div
          style={{
            fontSize: 32,
            color: "#888888",
            fontWeight: 400,
            opacity: text1Opacity,
            marginBottom: 24,
          }}
        >
          The code is just plastic.
        </div>

        {/* Second line: emphasized */}
        <div
          style={{
            fontSize: 36,
            color: "#FFFFFF",
            fontWeight: 600,
            opacity: text2Opacity,
            textShadow: `
              0 0 30px rgba(74, 144, 217, 0.4),
              0 0 30px rgba(217, 148, 74, 0.3),
              0 0 30px rgba(90, 170, 110, 0.3)
            `,
          }}
        >
          The mold is what matters.
        </div>
      </div>
    </AbsoluteFill>
  );
};
