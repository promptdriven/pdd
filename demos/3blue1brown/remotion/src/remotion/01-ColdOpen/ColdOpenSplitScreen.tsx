import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { LeftPanel } from "./LeftPanel";
import { RightPanel } from "./RightPanel";
import { COLORS, BEATS, secondsToFrames, ColdOpenPropsType } from "./constants";

export const ColdOpenSplitScreen: React.FC<ColdOpenPropsType> = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  // Vignette darkens during zoom out
  const zoomStart = secondsToFrames(BEATS.ZOOM_OUT_START);
  const zoomEnd = secondsToFrames(BEATS.ZOOM_OUT_END);

  const vignetteOpacity = interpolate(frame, [zoomStart, zoomEnd], [0, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Slight desaturation during zoom out
  const saturation = interpolate(frame, [zoomStart, zoomEnd], [100, 85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <AbsoluteFill
      style={{
        filter: `saturate(${saturation}%)`,
      }}
    >
      {/* Left Panel - Developer/Cursor */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: width / 2,
          height: height,
          overflow: "hidden",
        }}
      >
        <LeftPanel />
      </div>

      {/* Right Panel - Grandmother/Darning */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: width / 2,
          height: height,
          overflow: "hidden",
        }}
      >
        <RightPanel />
      </div>

      {/* Center divider line */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 0,
          width: 2,
          height: "100%",
          backgroundColor: COLORS.DIVIDER,
          transform: "translateX(-50%)",
          boxShadow: "0 0 10px rgba(255,255,255,0.3)",
        }}
      />

      {/* Vignette overlay (increases during zoom out) */}
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          right: 0,
          bottom: 0,
          background: `radial-gradient(ellipse at center, transparent 40%, rgba(0,0,0,${vignetteOpacity}) 100%)`,
          pointerEvents: "none",
        }}
      />

      {/* Narrator text area — fades in at 0:32, fades out by 0:35 to let visual speak */}
      {frame >= secondsToFrames(32) && frame <= secondsToFrames(36) && (
        <div
          style={{
            position: "absolute",
            bottom: 60,
            left: "50%",
            transform: "translateX(-50%)",
            opacity: interpolate(
              frame,
              [secondsToFrames(32), secondsToFrames(32.5), secondsToFrames(34.5), secondsToFrames(35.5)],
              [0, 1, 1, 0],
              { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
            ),
            textAlign: "center",
          }}
        >
          <p
            style={{
              fontFamily: "Georgia, serif",
              fontSize: 28,
              color: "#ffffff",
              textShadow: "0 2px 10px rgba(0,0,0,0.8)",
              fontStyle: "italic",
              maxWidth: 800,
              lineHeight: 1.5,
            }}
          >
            "But here's what your great-grandmother figured out sixty years ago."
          </p>
        </div>
      )}
    </AbsoluteFill>
  );
};
