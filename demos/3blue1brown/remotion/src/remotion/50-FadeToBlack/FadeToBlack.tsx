import React from "react";
import { AbsoluteFill, Easing, interpolate, useCurrentFrame } from "remotion";
import { BEATS, FadeToBlackPropsType } from "./constants";

export const FadeToBlack: React.FC<FadeToBlackPropsType> = ({
  showInstall = true,
}) => {
  const frame = useCurrentFrame();

  // Background transition: #1a1a2e -> #000000
  // Spec: Fade to black uses easeInQuad
  const bgDarkness = interpolate(
    frame,
    [BEATS.FADE_START, BEATS.FADE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.in(Easing.quad) }
  );

  const r = Math.round(interpolate(bgDarkness, [0, 1], [26, 0]));
  const g = Math.round(interpolate(bgDarkness, [0, 1], [26, 0]));
  const b = Math.round(interpolate(bgDarkness, [0, 1], [46, 0]));

  // Title opacity
  // Spec: Title uses easeOutCubic
  const titleOpacity = interpolate(
    frame,
    [BEATS.TITLE_START, BEATS.TITLE_END],
    [0, 0.9],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // URL opacity
  // Spec: URL uses easeOutCubic
  const urlOpacity = interpolate(
    frame,
    [BEATS.URL_START, BEATS.URL_END],
    [0, 0.5],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Install command opacity
  // Spec: Install command uses easeOutCubic
  const installOpacity = interpolate(
    frame,
    [BEATS.INSTALL_START, BEATS.INSTALL_END],
    [0, 0.3],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: `rgb(${r}, ${g}, ${b})`,
      }}
    >
      {/* Title: "Prompt-Driven Development" */}
      <div
        style={{
          position: "absolute",
          top: "38%",
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: titleOpacity,
        }}
      >
        <div
          style={{
            fontSize: 48,
            fontWeight: 600,
            color: "rgba(255, 255, 255, 0.9)",
            letterSpacing: 2,
            fontFamily: "Inter, Helvetica Neue, sans-serif",
          }}
        >
          Prompt-Driven Development
        </div>
      </div>

      {/* URL */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: urlOpacity,
        }}
      >
        <div
          style={{
            fontSize: 18,
            fontFamily: "JetBrains Mono, monospace",
            color: "rgba(255, 255, 255, 0.5)",
          }}
        >
          github.com/pdd-dev/pdd
        </div>
      </div>

      {/* Install command (subtle) */}
      {showInstall && (
        <div
          style={{
            position: "absolute",
            top: "56%",
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: installOpacity,
          }}
        >
          <div
            style={{
              fontSize: 16,
              fontFamily: "JetBrains Mono, monospace",
              color: "rgba(255, 255, 255, 0.3)",
            }}
          >
            <span style={{ color: "rgba(255, 255, 255, 0.2)" }}>$ </span>
            uv tool install pdd-cli
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
