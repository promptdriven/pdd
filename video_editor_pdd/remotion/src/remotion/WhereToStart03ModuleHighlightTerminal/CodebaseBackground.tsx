import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CODEBASE_MODULES,
  CODEBASE_DIM,
  CODE_LINES,
  HIGHLIGHT_START,
  HIGHLIGHT_DURATION,
} from "./constants";

/**
 * Renders a zoomed-out faded codebase of module rectangles.
 * All modules dim to 0.15 opacity as the highlight module appears.
 */
export const CodebaseBackground: React.FC = () => {
  const frame = useCurrentFrame();

  const dimOpacity = interpolate(
    frame,
    [HIGHLIGHT_START, HIGHLIGHT_START + HIGHLIGHT_DURATION],
    [0.3, 0.15],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div style={{ position: "absolute", inset: 0, opacity: dimOpacity }}>
      {CODEBASE_MODULES.map((mod, i) => (
        <div
          key={i}
          style={{
            position: "absolute",
            left: mod.x,
            top: mod.y,
            width: mod.w,
            height: mod.h,
            borderRadius: 4,
            border: `1px solid ${CODEBASE_DIM}`,
            backgroundColor: "rgba(148, 163, 184, 0.05)",
            overflow: "hidden",
            padding: 8,
          }}
        >
          {/* Module label */}
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 10,
              fontWeight: 600,
              color: CODEBASE_DIM,
              marginBottom: 6,
            }}
          >
            {mod.label}
          </div>
          {/* Fake code lines */}
          {CODE_LINES.slice(0, Math.floor(mod.h / 14)).map((line, j) => (
            <div
              key={j}
              style={{
                height: 3,
                width: `${line.width * 60}%`,
                marginLeft: line.indent * 12,
                marginBottom: 5,
                backgroundColor: CODEBASE_DIM,
                opacity: 0.3,
                borderRadius: 1,
              }}
            />
          ))}
        </div>
      ))}
    </div>
  );
};

export default CodebaseBackground;
