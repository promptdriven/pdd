import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  useCurrentFrame,
} from "remotion";
import {
  BG_COLOR,
  CANVAS_HEIGHT,
  CANVAS_WIDTH,
  CODE_LINES,
  FADE_IN_DURATION,
} from "./constants";
import { CodeLine } from "./CodeLine";
import { BlinkingCursor } from "./BlinkingCursor";

export const defaultColdOpen07CodeCursorBlinkProps = {};

export const ColdOpen07CodeCursorBlink: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over first 10 frames using easeOut(quad)
  const opacity = interpolate(frame, [0, FADE_IN_DURATION], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
      }}
    >
      <div
        style={{
          position: "absolute",
          top: 0,
          left: 0,
          width: "100%",
          height: "100%",
          opacity,
        }}
      >
        {/* Render all 40 lines of code */}
        {CODE_LINES.map((tokens, index) => (
          <CodeLine key={index} lineNumber={index + 1} tokens={tokens} />
        ))}

        {/* Blinking cursor at line 23, column 4 */}
        <BlinkingCursor line={23} column={4} startFrame={FADE_IN_DURATION} />
      </div>
    </AbsoluteFill>
  );
};

export default ColdOpen07CodeCursorBlink;
