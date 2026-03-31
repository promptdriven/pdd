import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  PANEL_BG,
  PANEL_BORDER,
  TEXT_PRIMARY,
  TEXT_MUTED,
  ACCENT_BLUE,
  ACCENT_GREEN,
  MONO_FONT,
  PROMPT_PANEL,
  PROMPT_FADE_END,
  PROMPT_LINES,
} from "./constants";

export const PromptFileDisplay: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, PROMPT_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const translateY = interpolate(frame, [0, PROMPT_FADE_END], [12, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: "absolute",
        left: PROMPT_PANEL.x,
        top: PROMPT_PANEL.y,
        width: PROMPT_PANEL.width,
        height: PROMPT_PANEL.height,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {/* File label */}
      <div
        style={{
          display: "flex",
          alignItems: "center",
          gap: 8,
          marginBottom: 10,
        }}
      >
        {/* Document icon */}
        <svg
          width="16"
          height="20"
          viewBox="0 0 16 20"
          fill="none"
          style={{ flexShrink: 0 }}
        >
          <path
            d="M0 2C0 0.9 0.9 0 2 0H10L16 6V18C16 19.1 15.1 20 14 20H2C0.9 20 0 19.1 0 18V2Z"
            fill={ACCENT_BLUE}
            fillOpacity={0.2}
          />
          <path
            d="M10 0L16 6H12C10.9 6 10 5.1 10 4V0Z"
            fill={ACCENT_BLUE}
            fillOpacity={0.4}
          />
          <path
            d="M4 10H12M4 13H10M4 16H8"
            stroke={ACCENT_BLUE}
            strokeWidth={1.2}
            strokeLinecap="round"
          />
        </svg>
        <span
          style={{
            fontFamily: MONO_FONT,
            fontSize: 13,
            color: TEXT_MUTED,
            letterSpacing: 0.3,
          }}
        >
          email_validator.prompt
        </span>
      </div>

      {/* Content area */}
      <div
        style={{
          background: PANEL_BG,
          borderRadius: 8,
          border: `1px solid ${PANEL_BORDER}`,
          padding: "16px 20px",
          height: PROMPT_PANEL.height - 40,
          overflow: "hidden",
        }}
      >
        {PROMPT_LINES.map((line, i) => {
          const lineDelay = i * 0.8;
          const lineOpacity = interpolate(
            frame,
            [lineDelay, lineDelay + 8],
            [0, 1],
            {
              extrapolateLeft: "clamp",
              extrapolateRight: "clamp",
            }
          );

          if (line.text === "") {
            return (
              <div
                key={i}
                style={{ height: 10, opacity: lineOpacity }}
              />
            );
          }

          return (
            <div
              key={i}
              style={{
                fontFamily: MONO_FONT,
                fontSize: 13,
                lineHeight: "28px",
                color: line.highlighted ? ACCENT_GREEN : TEXT_PRIMARY,
                opacity: lineOpacity,
                whiteSpace: "pre",
              }}
            >
              {line.text}
            </div>
          );
        })}
      </div>
    </div>
  );
};

export default PromptFileDisplay;
