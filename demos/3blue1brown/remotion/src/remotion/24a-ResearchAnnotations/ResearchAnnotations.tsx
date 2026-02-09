import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, CITATIONS, LAYOUT, ResearchAnnotationsPropsType } from "./constants";

export const ResearchAnnotations: React.FC<ResearchAnnotationsPropsType> = ({
  showOverlay = true,
}) => {
  const frame = useCurrentFrame();

  // Citation 1 fade-in
  const citation1Opacity = interpolate(
    frame,
    [BEATS.CITATION1_START, BEATS.CITATION1_END],
    [0, 0.7],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // "1.7x" emphasis flash
  const emphasisFlash = interpolate(
    frame,
    [BEATS.EMPHASIS_FLASH_START, BEATS.EMPHASIS_FLASH_PEAK, BEATS.EMPHASIS_FLASH_END],
    [0.7, 1, 0.7],
    { extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
  );

  // Citation 2 fade-in
  const citation2Opacity = interpolate(
    frame,
    [BEATS.CITATION2_START, BEATS.CITATION2_END],
    [0, 0.7],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Wall glow intensification
  const wallGlow = interpolate(
    frame,
    [BEATS.WALL_GLOW_START, BEATS.WALL_GLOW_END],
    [0.4, 1.0],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Brief pulse at peak
  const wallPulse =
    frame > BEATS.WALL_PULSE_START && frame < BEATS.WALL_PULSE_END
      ? 1.0 + Math.sin((frame - BEATS.WALL_PULSE_START) * 0.2) * 0.15
      : 1.0;

  // Connector line progress
  const connectorOpacity = citation1Opacity;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Mold walls (simplified representation) */}
      <div
        style={{
          position: "absolute",
          left: LAYOUT.WALL_X - LAYOUT.WALL_WIDTH / 2,
          top: LAYOUT.WALL_Y - LAYOUT.WALL_HEIGHT / 2,
          width: LAYOUT.WALL_WIDTH,
          height: LAYOUT.WALL_HEIGHT,
        }}
      >
        {/* Vertical wall segments */}
        {[0, 1, 2].map((i) => (
          <div
            key={i}
            style={{
              position: "absolute",
              left: i * 150 + 50,
              top: 50,
              width: 60,
              height: 400,
              background: COLORS.WALLS_AMBER,
              borderRadius: 4,
              boxShadow: `0 0 ${30 * wallGlow * wallPulse}px ${COLORS.WALLS_GLOW}`,
              opacity: wallGlow * 0.8 + 0.2,
            }}
          />
        ))}

        {/* Wall labels (faint) */}
        <div
          style={{
            position: "absolute",
            left: 50,
            top: 20,
            fontSize: 14,
            color: COLORS.WALLS_AMBER,
            fontFamily: "JetBrains Mono, monospace",
            opacity: 0.3,
          }}
        >
          null → None
        </div>
      </div>

      {/* Citation 1: CodeRabbit */}
      {citation1Opacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: LAYOUT.CITATION_X,
            top: LAYOUT.CITATION1_Y,
            opacity: citation1Opacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              fontFamily: "Inter, sans-serif",
              color: COLORS.CITATION_MUTED,
              lineHeight: 1.5,
              letterSpacing: 0.3,
              maxWidth: 500,
            }}
          >
            {CITATIONS.CODERABBIT.MAIN.split(CITATIONS.CODERABBIT.EMPHASIS).map((part, i, arr) => (
              <React.Fragment key={i}>
                {part}
                {i < arr.length - 1 && (
                  <span
                    style={{
                      color: COLORS.CITATION_EMPHASIS,
                      fontWeight: 600,
                      opacity: frame >= BEATS.EMPHASIS_FLASH_START ? emphasisFlash : citation1Opacity,
                    }}
                  >
                    {CITATIONS.CODERABBIT.EMPHASIS}
                  </span>
                )}
              </React.Fragment>
            ))}
          </div>
          <div
            style={{
              fontSize: 18,
              fontFamily: "Inter, sans-serif",
              color: COLORS.CITATION_MUTED,
              marginTop: 8,
              opacity: 0.6,
            }}
          >
            {CITATIONS.CODERABBIT.SOURCE}
          </div>

          {/* Dotted connector line to walls */}
          <div
            style={{
              position: "absolute",
              left: -80,
              top: 12,
              width: 80,
              height: 2,
              borderTop: `2px dotted ${COLORS.CITATION_MUTED}`,
              opacity: connectorOpacity * 0.4,
            }}
          />
        </div>
      )}

      {/* Citation 2: DORA */}
      {citation2Opacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: LAYOUT.CITATION_X,
            top: LAYOUT.CITATION2_Y,
            opacity: citation2Opacity,
          }}
        >
          <div
            style={{
              fontSize: 20,
              fontFamily: "Inter, sans-serif",
              color: COLORS.CITATION_MUTED,
              lineHeight: 1.5,
              letterSpacing: 0.3,
              maxWidth: 500,
            }}
          >
            AI +{" "}
            <span
              style={{
                color: COLORS.WALLS_AMBER,
                fontWeight: 600,
              }}
            >
              {CITATIONS.DORA.EMPHASIS}
            </span>{" "}
            = amplified delivery
          </div>
          <div
            style={{
              fontSize: 18,
              fontFamily: "Inter, sans-serif",
              color: COLORS.CITATION_MUTED,
              marginTop: 8,
              opacity: 0.6,
            }}
          >
            {CITATIONS.DORA.SOURCE}
          </div>

          {/* Connector bracket to "strong tests" */}
          <div
            style={{
              position: "absolute",
              left: -60,
              top: 8,
              width: 60,
              height: 30,
              borderLeft: `2px dotted ${COLORS.WALLS_AMBER}`,
              borderBottom: `2px dotted ${COLORS.WALLS_AMBER}`,
              opacity: citation2Opacity * 0.5,
            }}
          />
        </div>
      )}

      {/* Section header */}
      {showOverlay && (
        <div
          style={{
            position: "absolute",
            top: 40,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: citation1Opacity,
          }}
        >
          <span
            style={{
              fontSize: 24,
              fontFamily: "sans-serif",
              color: COLORS.WALLS_AMBER,
              fontWeight: "bold",
            }}
          >
            Research Validates the Walls
          </span>
        </div>
      )}

      {/* Subtle visual cue at peak glow */}
      {wallGlow > 0.8 && showOverlay && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: (wallGlow - 0.8) * 5,
          }}
        >
          <div
            style={{
              fontSize: 18,
              color: COLORS.CITATION_MUTED,
              fontFamily: "sans-serif",
              fontStyle: "italic",
            }}
          >
            The walls matter more than you'd think
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
