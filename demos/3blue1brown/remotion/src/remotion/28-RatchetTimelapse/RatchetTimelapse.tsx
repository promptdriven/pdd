import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, spring } from "remotion";
import { COLORS, BEATS, ACCUMULATING_TESTS, RatchetTimelapsePropsType, RATCHET_FPS } from "./constants";

export const RatchetTimelapse: React.FC<RatchetTimelapsePropsType> = ({
  maxWalls = 15,
}) => {
  const frame = useCurrentFrame();

  // Initial walls visibility
  const initialOpacity = interpolate(
    frame,
    [BEATS.INITIAL_WALLS_START, BEATS.INITIAL_WALLS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Calculate how many walls are visible during timelapse
  const wallCount = frame < BEATS.TIMELAPSE_START
    ? 5 // Start with 5 walls
    : Math.min(
        5 + Math.floor((frame - BEATS.TIMELAPSE_START) / BEATS.WALL_ACCUMULATION_RATE),
        maxWalls
      );

  // Counter visibility
  const counterOpacity = interpolate(
    frame,
    [BEATS.COUNTER_START, BEATS.COUNTER_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Insight text
  const insightOpacity = interpolate(
    frame,
    [BEATS.INSIGHT_START, BEATS.INSIGHT_START + 40],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Wall layout configuration
  const columns = 3;
  const wallWidth = 180;
  const wallHeight = 50;
  const gap = 12;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Wall grid */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: "translate(-50%, -50%)",
          display: "grid",
          gridTemplateColumns: `repeat(${columns}, ${wallWidth}px)`,
          gap: gap,
          opacity: initialOpacity,
        }}
      >
        {ACCUMULATING_TESTS.slice(0, wallCount).map((test, i) => {
          // Spring animation for each new wall
          const wallAppearFrame = i < 3
            ? 0
            : BEATS.TIMELAPSE_START + (i - 3) * BEATS.WALL_ACCUMULATION_RATE;

          const wallScale = spring({
            frame: frame - wallAppearFrame,
            fps: RATCHET_FPS,
            config: {
              damping: 15,
              stiffness: 120,
              mass: 0.5,
            },
          });

          const isNewWall = frame - wallAppearFrame < 30;

          return (
            <div
              key={i}
              style={{
                width: wallWidth,
                height: wallHeight,
                background: `rgba(217, 148, 74, ${isNewWall ? 0.5 : 0.3})`,
                border: `2px solid ${COLORS.WALLS_AMBER}`,
                borderRadius: 6,
                display: "flex",
                alignItems: "center",
                justifyContent: "center",
                fontSize: 11,
                fontFamily: "JetBrains Mono, monospace",
                color: COLORS.WALLS_AMBER,
                transform: `scale(${Math.min(wallScale, 1)})`,
                boxShadow: isNewWall
                  ? `0 0 20px ${COLORS.WALLS_AMBER}`
                  : "none",
                opacity: wallScale > 0 ? 1 : 0,
              }}
            >
              {test}
            </div>
          );
        })}
      </div>

      {/* Counter */}
      {counterOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 100,
            right: 100,
            opacity: counterOpacity,
            textAlign: "right",
          }}
        >
          <div
            style={{
              fontSize: 48,
              fontWeight: "bold",
              color: COLORS.COUNTER_BLUE,
              fontFamily: "sans-serif",
            }}
          >
            {wallCount}
          </div>
          <div
            style={{
              fontSize: 16,
              color: COLORS.LABEL_GRAY,
            }}
          >
            test constraints
          </div>
        </div>
      )}

      {/* Ratchet indicator */}
      {frame >= BEATS.TIMELAPSE_START && frame < BEATS.TIMELAPSE_END && (
        <div
          style={{
            position: "absolute",
            bottom: 200,
            left: "50%",
            transform: "translateX(-50%)",
            fontSize: 24,
            color: COLORS.LABEL_GRAY,
            fontFamily: "sans-serif",
            opacity: 0.7,
          }}
        >
          🔧 Click... click... click...
        </div>
      )}

      {/* Insight text */}
      {insightOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 80,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: insightOpacity,
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
            Each bug caught becomes a permanent constraint.
          </div>
          <div
            style={{
              fontSize: 18,
              color: COLORS.LABEL_GRAY,
            }}
          >
            The mold can only get more precise over time.
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
          opacity: initialOpacity,
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
          The Ratchet Effect
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          Time-lapse: walls accumulating over development
        </div>
      </div>
    </AbsoluteFill>
  );
};
