import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CLEAN_FUNCTION_CODE,
  CODE_BG_OPACITY,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * Renders the regenerated code as a faint background texture.
 * Uses a simple styled <pre> block — no external CodeEditor dependency.
 */
export const BackgroundCode: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        opacity: CODE_BG_OPACITY,
        padding: 80,
        overflow: "hidden",
      }}
    >
      <pre
        style={{
          fontFamily: "'Fira Code', 'Cascadia Code', 'JetBrains Mono', monospace",
          fontSize: 15,
          lineHeight: 1.6,
          color: "#A6ADC8",
          margin: 0,
          whiteSpace: "pre",
          width: CANVAS_WIDTH - 160,
          height: CANVAS_HEIGHT - 160,
          overflow: "hidden",
        }}
      >
        {CLEAN_FUNCTION_CODE}
      </pre>
    </AbsoluteFill>
  );
};

export default BackgroundCode;
