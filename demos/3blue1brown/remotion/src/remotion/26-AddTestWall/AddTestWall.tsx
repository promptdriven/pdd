import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing, spring } from "remotion";
import { COLORS, BEATS, EXISTING_TESTS, NEW_TEST, AddTestWallPropsType } from "./constants";
import { ADD_TEST_WALL_FPS } from "./constants";

export const AddTestWall: React.FC<AddTestWallPropsType> = ({
  showNewTest = true,
}) => {
  const frame = useCurrentFrame();

  // Walls visibility
  const wallsOpacity = interpolate(
    frame,
    [BEATS.WALLS_VISIBLE_START, BEATS.WALLS_VISIBLE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // New wall spring animation
  const newWallProgress = spring({
    frame: frame - BEATS.NEW_WALL_START,
    fps: ADD_TEST_WALL_FPS,
    config: {
      damping: 12,
      stiffness: 100,
      mass: 0.8,
    },
  });

  // New wall scale (materializes from nothing)
  const newWallScale = frame >= BEATS.NEW_WALL_START ? newWallProgress : 0;

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_START, BEATS.LABEL_START + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Glow intensity
  const glowIntensity = interpolate(
    frame,
    [BEATS.GLOW_START, BEATS.GLOW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Wall dimensions
  const wallConfig = {
    width: 200,
    height: 60,
    gap: 20,
    startY: 250,
  };

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Existing walls */}
      <div
        style={{
          position: "absolute",
          top: "50%",
          left: "50%",
          transform: "translate(-50%, -50%)",
          opacity: wallsOpacity,
        }}
      >
        {EXISTING_TESTS.map((test, i) => (
          <div
            key={i}
            style={{
              width: wallConfig.width,
              height: wallConfig.height,
              background: "rgba(217, 148, 74, 0.3)",
              border: `2px solid ${COLORS.WALLS_AMBER}`,
              borderRadius: 8,
              marginBottom: wallConfig.gap,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              fontSize: 14,
              fontFamily: "JetBrains Mono, monospace",
              color: COLORS.WALLS_AMBER,
            }}
          >
            {test}
          </div>
        ))}

        {/* New wall materializing */}
        {showNewTest && newWallScale > 0 && (
          <div
            style={{
              width: wallConfig.width,
              height: wallConfig.height,
              background: `rgba(217, 148, 74, ${0.3 + 0.3 * glowIntensity})`,
              border: `2px solid ${glowIntensity > 0 ? COLORS.NEW_WALL_GLOW : COLORS.WALLS_AMBER}`,
              borderRadius: 8,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              fontSize: 14,
              fontFamily: "JetBrains Mono, monospace",
              color: glowIntensity > 0 ? COLORS.NEW_WALL_GLOW : COLORS.WALLS_AMBER,
              transform: `scale(${newWallScale})`,
              boxShadow: glowIntensity > 0
                ? `0 0 ${30 * glowIntensity}px ${COLORS.NEW_WALL_GLOW}`
                : "none",
              opacity: labelOpacity > 0 ? 1 : 0.7,
            }}
          >
            <span style={{ opacity: labelOpacity }}>{NEW_TEST}</span>
          </div>
        )}
      </div>

      {/* Click indicator */}
      {frame >= BEATS.CLICK_SOUND - 5 && frame <= BEATS.CLICK_SOUND + 15 && (
        <div
          style={{
            position: "absolute",
            top: "50%",
            left: "50%",
            transform: "translate(-50%, 80px)",
            fontSize: 32,
            opacity: interpolate(
              frame,
              [BEATS.CLICK_SOUND - 5, BEATS.CLICK_SOUND, BEATS.CLICK_SOUND + 15],
              [0, 1, 0]
            ),
          }}
        >
          🔧
        </div>
      )}

      {/* Explanation text */}
      <div
        style={{
          position: "absolute",
          bottom: 100,
          left: 0,
          right: 0,
          textAlign: "center",
          opacity: interpolate(frame, [BEATS.HOLD_START, BEATS.HOLD_START + 30], [0, 1], { extrapolateLeft: "clamp", extrapolateRight: "clamp" }),
        }}
      >
        <div
          style={{
            fontSize: 22,
            color: COLORS.LABEL_WHITE,
            fontFamily: "sans-serif",
          }}
        >
          New test added. The mold is refined. Future code must pass this constraint.
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
          opacity: wallsOpacity,
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
          Adding a Test Wall
        </span>
        <div
          style={{
            fontSize: 16,
            color: COLORS.LABEL_GRAY,
            marginTop: 8,
          }}
        >
          The ratchet clicks forward
        </div>
      </div>
    </AbsoluteFill>
  );
};
