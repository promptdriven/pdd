import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, STYLE_SWATCHES, GroundingPanelPropsType } from "./constants";

const PatternVisualization: React.FC<{ pattern: string; color: string }> = ({ pattern, color }) => {
  switch (pattern) {
    case "grid":
      return (
        <svg width="120" height="100" viewBox="0 0 120 100">
          <rect x="5" y="5" width="45" height="35" stroke={color} fill="none" strokeWidth="2" />
          <rect x="60" y="5" width="45" height="35" stroke={color} fill="none" strokeWidth="2" />
          <rect x="5" y="50" width="45" height="35" stroke={color} fill="none" strokeWidth="2" />
          <rect x="60" y="50" width="45" height="35" stroke={color} fill="none" strokeWidth="2" />
          <line x1="50" y1="22" x2="60" y2="22" stroke={color} strokeWidth="1" />
          <line x1="50" y1="67" x2="60" y2="67" stroke={color} strokeWidth="1" />
        </svg>
      );
    case "flow":
      return (
        <svg width="120" height="100" viewBox="0 0 120 100">
          <path d="M5,25 Q60,10 115,25" stroke={color} fill="none" strokeWidth="2" />
          <path d="M5,50 Q60,35 115,50" stroke={color} fill="none" strokeWidth="2" />
          <path d="M5,75 Q60,60 115,75" stroke={color} fill="none" strokeWidth="2" />
          <circle cx="115" cy="25" r="4" fill={color} />
          <circle cx="115" cy="50" r="4" fill={color} />
          <circle cx="115" cy="75" r="4" fill={color} />
        </svg>
      );
    case "custom":
      return (
        <svg width="120" height="100" viewBox="0 0 120 100">
          <path d="M5,20 C25,10 45,30 60,20 S95,10 115,20" stroke={color} fill="none" strokeWidth="2" />
          <path d="M5,50 C25,40 45,60 60,50 S95,40 115,50" stroke={color} fill="none" strokeWidth="2" />
          <path d="M5,80 C25,70 45,90 60,80 S95,70 115,80" stroke={color} fill="none" strokeWidth="2" />
          <circle cx="60" cy="95" r="6" fill={color} opacity="0.6" />
        </svg>
      );
    default:
      return null;
  }
};

export const GroundingPanel: React.FC<GroundingPanelPropsType> = ({
  showSwatches = true,
}) => {
  const frame = useCurrentFrame();

  // Panel entrance
  const panelY = interpolate(
    frame,
    [BEATS.PANEL_START, BEATS.PANEL_END],
    [100, 0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const panelOpacity = interpolate(
    frame,
    [BEATS.PANEL_START, BEATS.PANEL_END],
    [0, 1],
    { extrapolateRight: "clamp" }
  );

  // Swatch opacities
  const swatchOpacities = [
    interpolate(frame, [BEATS.OOP_START, BEATS.OOP_END], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
    interpolate(frame, [BEATS.FUNCTIONAL_START, BEATS.FUNCTIONAL_END], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
    interpolate(frame, [BEATS.TEAM_START, BEATS.TEAM_END], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
  ];

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Main panel */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: `translate(-50%, calc(-50% + ${panelY}px))`,
          opacity: panelOpacity,
        }}
      >
        {/* Header */}
        <div
          style={{
            textAlign: "center",
            marginBottom: 40,
          }}
        >
          <div
            style={{
              fontSize: 28,
              fontWeight: "bold",
              color: COLORS.GROUNDING_GREEN,
              marginBottom: 8,
            }}
          >
            GROUNDING CAPITAL
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_GRAY,
            }}
          >
            The Material
          </div>
        </div>

        {/* Style swatches */}
        {showSwatches && (
          <div
            style={{
              display: "flex",
              gap: 40,
              justifyContent: "center",
            }}
          >
            {STYLE_SWATCHES.map((swatch, i) => {
              const isTeamStyle = swatch.label === "Your Team's Style";
              return (
                <div
                  key={i}
                  style={{
                    opacity: swatchOpacities[i],
                    width: 180,
                    background: "#1E1E2E",
                    border: `2px solid ${isTeamStyle ? COLORS.GROUNDING_GREEN : "#444"}`,
                    borderRadius: 12,
                    padding: 20,
                    boxShadow: isTeamStyle ? `0 0 20px rgba(90, 170, 110, 0.3)` : "none",
                  }}
                >
                  <div style={{ marginBottom: 16 }}>
                    <PatternVisualization pattern={swatch.pattern} color={swatch.color} />
                  </div>
                  <div
                    style={{
                      textAlign: "center",
                      fontSize: 14,
                      color: isTeamStyle ? COLORS.GROUNDING_GREEN : COLORS.LABEL_GRAY,
                      fontWeight: isTeamStyle ? "bold" : "normal",
                    }}
                  >
                    {swatch.label}
                  </div>
                </div>
              );
            })}
          </div>
        )}

        {/* Description */}
        <div
          style={{
            textAlign: "center",
            marginTop: 40,
            opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
          }}
        >
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_WHITE,
              fontFamily: "sans-serif",
            }}
          >
            Determines the properties of what fills the mold
          </div>
        </div>
      </div>

      {/* Section header */}
      <div
        style={{
          position: "absolute",
          top: 60,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: panelOpacity,
        }}
      >
        <span
          style={{
            fontSize: 24,
            fontFamily: "sans-serif",
            color: COLORS.GROUNDING_GREEN,
            fontWeight: "bold",
          }}
        >
          Third: grounding
        </span>
      </div>
    </AbsoluteFill>
  );
};
