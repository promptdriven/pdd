import React from "react";
import { useCurrentFrame, interpolate, Easing, OffthreadVideo } from "remotion";

const PANEL_FADE_DURATION = 30;
const HEIGHT = 1080;
const PANEL_WIDTH = 940;
const LABEL_FONT_SIZE = 20;
const LABEL_OPACITY = 0.78;
const LABEL_PADDING_BOTTOM = 32;
const LABEL_COLOR = "#FFFFFF";

interface VideoPanelProps {
  src: string | null;
  side: "left" | "right";
  label: string;
  fallbackGradient: string;
}

export const VideoPanel: React.FC<VideoPanelProps> = ({
  src,
  side,
  label,
  fallbackGradient,
}) => {
  const frame = useCurrentFrame();

  const panelOpacity = interpolate(frame, [0, PANEL_FADE_DURATION], [0, 1], {
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const left = side === "left" ? 0 : PANEL_WIDTH + 40;

  return (
    <div
      style={{
        position: "absolute",
        left,
        top: 0,
        width: PANEL_WIDTH,
        height: HEIGHT,
        overflow: "hidden",
        opacity: panelOpacity,
      }}
    >
      {/* Video or gradient fallback */}
      {src ? (
        <OffthreadVideo
          src={src}
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: PANEL_WIDTH,
            height: HEIGHT,
            objectFit: "cover",
          }}
          muted
        />
      ) : (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: PANEL_WIDTH,
            height: HEIGHT,
            background: fallbackGradient,
          }}
        />
      )}

      {/* Bottom label with gradient scrim */}
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 0,
          width: PANEL_WIDTH,
          height: 100,
          background:
            "linear-gradient(to top, rgba(0,0,0,0.6) 0%, rgba(0,0,0,0) 100%)",
          display: "flex",
          alignItems: "flex-end",
          justifyContent: "center",
          paddingBottom: LABEL_PADDING_BOTTOM,
        }}
      >
        <span
          style={{
            color: LABEL_COLOR,
            fontSize: LABEL_FONT_SIZE,
            fontFamily: "Inter, Helvetica, Arial, sans-serif",
            fontWeight: 500,
            opacity: LABEL_OPACITY,
            letterSpacing: "0.04em",
            textTransform: "uppercase",
          }}
        >
          {label}
        </span>
      </div>
    </div>
  );
};

export default VideoPanel;
