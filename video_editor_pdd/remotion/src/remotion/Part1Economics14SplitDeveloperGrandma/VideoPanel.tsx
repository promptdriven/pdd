import React from "react";
import { OffthreadVideo, interpolate, useCurrentFrame, Easing } from "remotion";

interface VideoPanelProps {
  src: string | null;
  side: "left" | "right";
  panelWidth: number;
  canvasHeight: number;
  canvasWidth: number;
  dividerGap: number;
  fadeFrames: number;
  label: string;
  labelFontSize: number;
  labelColor: string;
  labelOpacity: number;
  labelBgOpacity: number;
}

export const VideoPanel: React.FC<VideoPanelProps> = ({
  src,
  side,
  panelWidth,
  canvasHeight,
  canvasWidth,
  dividerGap,
  fadeFrames,
  label,
  labelFontSize,
  labelColor,
  labelOpacity,
  labelBgOpacity,
}) => {
  const frame = useCurrentFrame();

  const panelOpacity = interpolate(frame, [0, fadeFrames], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const leftPos = side === "left" ? 0 : canvasWidth / 2 + dividerGap / 2;

  // Placeholder gradient for when no video is available
  const placeholderGradient =
    side === "left"
      ? "linear-gradient(135deg, #0A1628 0%, #1E3A5F 50%, #0D2240 100%)"
      : "linear-gradient(135deg, #2A1A0A 0%, #5F3A1E 50%, #40280D 100%)";

  return (
    <div
      style={{
        position: "absolute",
        left: leftPos,
        top: 0,
        width: panelWidth,
        height: canvasHeight,
        overflow: "hidden",
        opacity: panelOpacity,
      }}
    >
      {src ? (
        <OffthreadVideo
          src={src}
          style={{
            width: panelWidth,
            height: canvasHeight,
            objectFit: "cover",
          }}
        />
      ) : (
        <div
          style={{
            width: panelWidth,
            height: canvasHeight,
            background: placeholderGradient,
          }}
        />
      )}

      {/* Panel label overlay at bottom */}
      <div
        style={{
          position: "absolute",
          bottom: 32,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          zIndex: 5,
        }}
      >
        <div
          style={{
            backgroundColor: `rgba(0, 0, 0, ${labelBgOpacity})`,
            borderRadius: 8,
            padding: "8px 20px",
          }}
        >
          <span
            style={{
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: labelFontSize,
              fontWeight: 600,
              color: labelColor,
              opacity: labelOpacity,
              letterSpacing: "0.02em",
            }}
          >
            {label}
          </span>
        </div>
      </div>
    </div>
  );
};

export default VideoPanel;
