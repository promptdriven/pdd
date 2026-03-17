import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLUE,
  AMBER,
  GREEN,
  DIM_BORDER,
  DARK_FILL,
  LINE_COLOR,
} from "./constants";

/**
 * Step 1: Document icon with horizontal lines (prompt document)
 */
export const PromptDocIcon: React.FC<{ progress: number }> = ({ progress }) => {
  const scale = interpolate(progress, [0, 1], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        width: 50,
        height: 65,
        border: `1.5px solid ${BLUE}`,
        borderRadius: 4,
        backgroundColor: DARK_FILL,
        opacity: 0.9,
        transform: `scale(${scale})`,
        display: "flex",
        flexDirection: "column",
        justifyContent: "center",
        alignItems: "center",
        gap: 6,
        padding: "8px 6px",
      }}
    >
      {[0, 1, 2, 3].map((i) => (
        <div
          key={i}
          style={{
            width: "80%",
            height: 2,
            backgroundColor: LINE_COLOR,
            opacity: 0.3,
            borderRadius: 1,
          }}
        />
      ))}
    </div>
  );
};

/**
 * Step 2: Amber wall rectangles (test walls)
 */
export const WallIcons: React.FC<{ frame: number }> = ({ frame }) => {
  return (
    <div style={{ display: "flex", gap: 5, alignItems: "flex-end" }}>
      {[0, 1, 2].map((i) => {
        const delay = i * 4;
        const localProgress = interpolate(frame - delay, [0, 10], [0, 1], {
          easing: Easing.out(Easing.cubic),
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        });

        return (
          <div
            key={i}
            style={{
              width: 8,
              height: 30,
              backgroundColor: AMBER,
              opacity: 0.5 * localProgress,
              borderRadius: 2,
              transform: `scaleY(${localProgress})`,
              transformOrigin: "bottom",
            }}
          />
        );
      })}
    </div>
  );
};

/**
 * Step 3: Terminal icon with "pdd generate" text and particles
 */
export const TerminalIcon: React.FC<{ progress: number; frame: number }> = ({
  progress,
  frame,
}) => {
  const scale = interpolate(progress, [0, 1], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div style={{ position: "relative" }}>
      <div
        style={{
          width: 55,
          height: 45,
          border: `1.5px solid ${DIM_BORDER}`,
          borderRadius: 4,
          backgroundColor: DARK_FILL,
          transform: `scale(${scale})`,
          display: "flex",
          flexDirection: "column",
          overflow: "hidden",
        }}
      >
        {/* Title bar */}
        <div
          style={{
            height: 10,
            backgroundColor: DIM_BORDER,
            display: "flex",
            alignItems: "center",
            paddingLeft: 4,
            gap: 2,
          }}
        >
          {[0, 1, 2].map((i) => (
            <div
              key={i}
              style={{
                width: 3,
                height: 3,
                borderRadius: "50%",
                backgroundColor: i === 0 ? "#EF4444" : i === 1 ? "#F59E0B" : "#22C55E",
                opacity: 0.6,
              }}
            />
          ))}
        </div>
        {/* Terminal body */}
        <div
          style={{
            flex: 1,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            padding: 3,
          }}
        >
          <span
            style={{
              fontFamily: "JetBrains Mono, monospace",
              fontSize: 7,
              color: GREEN,
              opacity: 0.4,
              whiteSpace: "nowrap",
            }}
          >
            pdd generate
          </span>
        </div>
      </div>

      {/* Particle burst */}
      {scale > 0.5 &&
        [0, 1, 2, 3, 4].map((i) => {
          const angle = -60 + i * 30; // spread downward
          const rad = (angle * Math.PI) / 180;
          const dist = interpolate(frame, [0, 20], [0, 25 + i * 5], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          });
          const particleOpacity = interpolate(frame, [0, 10, 25], [0, 0.3, 0], {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
          });

          return (
            <div
              key={i}
              style={{
                position: "absolute",
                left: 27 + Math.cos(rad) * dist,
                top: 45 + Math.sin(rad) * Math.abs(dist),
                width: 4,
                height: 4,
                borderRadius: "50%",
                backgroundColor: BLUE,
                opacity: particleOpacity,
              }}
            />
          );
        })}
    </div>
  );
};

/**
 * Step 4: Split diff view with checkmarks
 */
export const DiffViewIcon: React.FC<{ progress: number; frame: number }> = ({
  progress,
  frame,
}) => {
  const scale = interpolate(progress, [0, 1], [0, 1], {
    easing: Easing.out(Easing.cubic),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Checkmark appears after 8 frames with back easing (overshoot)
  const checkScale = interpolate(frame - 8, [0, 8], [0, 1], {
    easing: Easing.out(Easing.back(1.7)),
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div style={{ position: "relative" }}>
      <div
        style={{
          width: 60,
          height: 45,
          borderRadius: 4,
          border: `1.5px solid ${DIM_BORDER}`,
          backgroundColor: DARK_FILL,
          transform: `scale(${scale})`,
          display: "flex",
          overflow: "hidden",
        }}
      >
        {/* Left half - original (gray lines) */}
        <div
          style={{
            flex: 1,
            display: "flex",
            flexDirection: "column",
            justifyContent: "center",
            gap: 4,
            padding: "6px 4px",
            borderRight: `1px solid ${DIM_BORDER}`,
          }}
        >
          {[0, 1, 2].map((i) => (
            <div
              key={i}
              style={{
                width: `${60 + i * 10}%`,
                height: 2,
                backgroundColor: "#64748B",
                opacity: 0.3,
                borderRadius: 1,
              }}
            />
          ))}
        </div>
        {/* Right half - regenerated (blue lines) */}
        <div
          style={{
            flex: 1,
            display: "flex",
            flexDirection: "column",
            justifyContent: "center",
            gap: 4,
            padding: "6px 4px",
          }}
        >
          {[0, 1, 2].map((i) => (
            <div
              key={i}
              style={{
                width: `${60 + i * 10}%`,
                height: 2,
                backgroundColor: BLUE,
                opacity: 0.3,
                borderRadius: 1,
              }}
            />
          ))}
        </div>
      </div>

      {/* Green checkmarks */}
      {checkScale > 0 && (
        <>
          <svg
            style={{
              position: "absolute",
              left: 6,
              top: -2,
              transform: `scale(${checkScale})`,
              transformOrigin: "center",
            }}
            width="12"
            height="12"
            viewBox="0 0 12 12"
          >
            <path
              d="M2 6 L5 9 L10 3"
              stroke={GREEN}
              strokeWidth="2"
              fill="none"
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={0.7}
            />
          </svg>
          <svg
            style={{
              position: "absolute",
              right: 6,
              top: -2,
              transform: `scale(${checkScale})`,
              transformOrigin: "center",
            }}
            width="12"
            height="12"
            viewBox="0 0 12 12"
          >
            <path
              d="M2 6 L5 9 L10 3"
              stroke={GREEN}
              strokeWidth="2"
              fill="none"
              strokeLinecap="round"
              strokeLinejoin="round"
              opacity={0.7}
            />
          </svg>
        </>
      )}
    </div>
  );
};
