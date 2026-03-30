import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
  OffthreadVideo,
  staticFile,
} from "remotion";

// ─── Constants ───────────────────────────────────────────────────────────
const DURATION_FRAMES = 510;
const FPS = 30;
const WIDTH = 1920;
const HEIGHT = 1080;
const PANEL_WIDTH = 940;
const DIVIDER_GAP = 40;
const DIVIDER_THICKNESS = 2;
const BACKGROUND_COLOR = "#000000";
const DIVIDER_COLOR = "#FFFFFF";
const DIVIDER_OPACITY = 0.6;
const LABEL_COLOR = "#FFFFFF";
const LABEL_FONT_SIZE = 20;
const LABEL_OPACITY = 0.78;
const LABEL_PADDING_BOTTOM = 32;
const PANEL_FADE_DURATION = 30;
const DIVIDER_FADE_DURATION = 15;

// Fallback gradients when video is unavailable
const LEFT_FALLBACK_GRADIENT =
  "linear-gradient(135deg, #0B1A2E 0%, #1A3A5C 50%, #0D2240 100%)";
const RIGHT_FALLBACK_GRADIENT =
  "linear-gradient(135deg, #3D2B1F 0%, #5C3D2E 50%, #2C1A0E 100%)";

// ─── Props ───────────────────────────────────────────────────────────────

export const defaultPart1Economics14SplitDeveloperGrandmaProps = {};

// ─── Sub-component: Divider ──────────────────────────────────────────────

const SplitDivider: React.FC<{ frame: number }> = ({ frame }) => {
  const opacity = interpolate(
    frame,
    [0, DIVIDER_FADE_DURATION],
    [0, DIVIDER_OPACITY],
    {
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const drawProgress = interpolate(
    frame,
    [0, DIVIDER_FADE_DURATION],
    [0, 1],
    {
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const lineHeight = HEIGHT * drawProgress;
  const yOffset = (HEIGHT - lineHeight) / 2;

  return (
    <div
      style={{
        position: "absolute",
        left: "50%",
        top: 0,
        width: DIVIDER_GAP,
        height: HEIGHT,
        transform: "translateX(-50%)",
        display: "flex",
        alignItems: "center",
        justifyContent: "center",
        zIndex: 10,
      }}
    >
      <div
        style={{
          position: "absolute",
          top: yOffset,
          width: DIVIDER_THICKNESS,
          height: lineHeight,
          backgroundColor: DIVIDER_COLOR,
          opacity,
          borderRadius: 1,
        }}
      />
    </div>
  );
};

// ─── Sub-component: Video Panel ──────────────────────────────────────────

interface VideoPanelProps {
  src: string;
  side: "left" | "right";
  label: string;
  fallbackGradient: string;
  frame: number;
}

const VideoPanel: React.FC<VideoPanelProps> = ({
  src,
  side,
  label,
  fallbackGradient,
  frame,
}) => {
  const panelOpacity = interpolate(
    frame,
    [0, PANEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const left = side === "left" ? 0 : PANEL_WIDTH + DIVIDER_GAP;

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
      {/* Video layer */}
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

      {/* Bottom label with gradient scrim for readability */}
      <div
        style={{
          position: "absolute",
          bottom: 0,
          left: 0,
          width: PANEL_WIDTH,
          height: 120,
          background:
            "linear-gradient(to top, rgba(0,0,0,0.65) 0%, rgba(0,0,0,0) 100%)",
          display: "flex",
          alignItems: "flex-end",
          justifyContent: "center",
          paddingBottom: LABEL_PADDING_BOTTOM,
          zIndex: 5,
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
            textTransform: "uppercase" as const,
          }}
        >
          {label}
        </span>
      </div>
    </div>
  );
};

// ─── Main Component ──────────────────────────────────────────────────────

export const Part1Economics14SplitDeveloperGrandma: React.FC = () => {
  const frame = useCurrentFrame();

  // Resolve video sources — use staticFile for the known Veo assets
  const leftSrc = staticFile("veo/developer_cursor_p1.mp4");
  const rightSrc = staticFile("veo/grandmother_darning_p1.mp4");

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BACKGROUND_COLOR,
        width: WIDTH,
        height: HEIGHT,
      }}
    >
      {/* Left panel: Developer with Cursor */}
      <VideoPanel
        src={leftSrc}
        side="left"
        label="Developer with Cursor"
        fallbackGradient={LEFT_FALLBACK_GRADIENT}
        frame={frame}
      />

      {/* Right panel: Grandmother darning */}
      <VideoPanel
        src={rightSrc}
        side="right"
        label="Grandmother darning"
        fallbackGradient={RIGHT_FALLBACK_GRADIENT}
        frame={frame}
      />

      {/* Center divider */}
      <SplitDivider frame={frame} />
    </AbsoluteFill>
  );
};

export default Part1Economics14SplitDeveloperGrandma;
