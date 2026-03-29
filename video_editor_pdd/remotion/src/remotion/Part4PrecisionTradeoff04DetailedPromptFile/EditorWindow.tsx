import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  EDITOR_WIDTH,
  EDITOR_HEIGHT,
  EDITOR_X,
  EDITOR_Y,
  TITLE_BAR_HEIGHT,
  TITLE_BAR_COLOR,
  WINDOW_FRAME_COLOR,
  ACCENT_AMBER,
  FILENAME_COLOR,
  CORNER_RADIUS,
  MONO_FONT,
  SANS_FONT,
  CODE_FONT_SIZE,
  BADGE_FONT_SIZE,
  BADGE_START,
  BADGE_SCALE_DURATION,
} from "./constants";

/** Traffic-light dots (decorative) */
const TrafficLights: React.FC = () => (
  <div style={{ display: "flex", gap: 6, marginLeft: 14, alignItems: "center" }}>
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "#EF4444",
        opacity: 0.6,
      }}
    />
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "#EAB308",
        opacity: 0.6,
      }}
    />
    <div
      style={{
        width: 10,
        height: 10,
        borderRadius: "50%",
        backgroundColor: "#22C55E",
        opacity: 0.6,
      }}
    />
  </div>
);

/** Line count badge with scale-in animation */
const LineCountBadge: React.FC = () => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame,
    [BADGE_START, BADGE_START + BADGE_SCALE_DURATION],
    [0.8, 1.0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const badgeOpacity = interpolate(
    frame,
    [BADGE_START, BADGE_START + 8],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <div
      style={{
        transform: `scale(${scale})`,
        opacity: badgeOpacity,
        backgroundColor: `rgba(217, 148, 74, 0.15)`,
        color: ACCENT_AMBER,
        fontFamily: SANS_FONT,
        fontSize: BADGE_FONT_SIZE,
        fontWeight: 600,
        padding: "2px 10px",
        borderRadius: 10,
        marginLeft: 12,
        whiteSpace: "nowrap",
      }}
    >
      50 lines
    </div>
  );
};

export interface EditorWindowProps {
  children: React.ReactNode;
}

export const EditorWindow: React.FC<EditorWindowProps> = ({ children }) => {
  return (
    <div
      style={{
        position: "absolute",
        left: EDITOR_X,
        top: EDITOR_Y,
        width: EDITOR_WIDTH,
        height: EDITOR_HEIGHT,
        borderRadius: CORNER_RADIUS,
        border: `1px solid ${WINDOW_FRAME_COLOR}`,
        overflow: "hidden",
        // Amber glow
        boxShadow: `0 0 12px rgba(217, 148, 74, 0.08)`,
        display: "flex",
        flexDirection: "column",
      }}
    >
      {/* Title bar */}
      <div
        style={{
          height: TITLE_BAR_HEIGHT,
          backgroundColor: TITLE_BAR_COLOR,
          display: "flex",
          alignItems: "center",
          flexShrink: 0,
          borderBottom: `1px solid ${WINDOW_FRAME_COLOR}`,
        }}
      >
        <TrafficLights />
        <div
          style={{
            fontFamily: MONO_FONT,
            fontSize: CODE_FONT_SIZE,
            color: FILENAME_COLOR,
            marginLeft: 16,
          }}
        >
          parser_v1.prompt
        </div>
        <LineCountBadge />
      </div>

      {/* Content area */}
      <div
        style={{
          flex: 1,
          backgroundColor: "#0D1321",
          position: "relative",
          overflow: "hidden",
        }}
      >
        {children}
      </div>
    </div>
  );
};
