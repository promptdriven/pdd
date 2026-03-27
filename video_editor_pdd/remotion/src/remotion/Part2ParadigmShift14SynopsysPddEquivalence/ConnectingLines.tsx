import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  LINE1_Y,
  LINE2_Y,
  LINE_FONT_SIZE,
  CONNECTING_LINE_COLOR,
  CONNECTING_LINE_OPACITY,
} from "./constants";

/**
 * Draws animated dashed connecting lines between equivalent words
 * in Line 1 and Line 2.
 *
 * Layout reference (centered text):
 *   Line 1: "Synopsys: specification in → verified hardware out."
 *   Line 2: "PDD: prompt in → verified software out."
 *
 * We approximate word positions based on a ~17.6px per character average
 * for Inter 32px. Both lines are center-aligned at x=960.
 */

// Line 1 full text: "Synopsys: specification in → verified hardware out."
// Line 2 full text: "PDD: prompt in → verified software out."

const LINE1_TEXT = "Synopsys: specification in → verified hardware out.";
const LINE2_TEXT = "PDD: prompt in → verified software out.";

const CHAR_WIDTH = 17.6; // approximate for Inter 32px

function getWordCenter(fullText: string, word: string): number {
  const lineWidth = fullText.length * CHAR_WIDTH;
  const lineStartX = (WIDTH - lineWidth) / 2;
  const wordStart = fullText.indexOf(word);
  const wordCenterChar = wordStart + word.length / 2;
  return lineStartX + wordCenterChar * CHAR_WIDTH;
}

// Precompute positions
const specX = getWordCenter(LINE1_TEXT, "specification");
const promptX = getWordCenter(LINE2_TEXT, "prompt");
const hardwareX = getWordCenter(LINE1_TEXT, "hardware");
const softwareX = getWordCenter(LINE2_TEXT, "software");

const LINE_BOTTOM = LINE_FONT_SIZE * 0.35; // offset below baseline

interface ConnectingLinesProps {
  startFrame: number;
  drawDuration: number;
}

export const ConnectingLines: React.FC<ConnectingLinesProps> = ({
  startFrame,
  drawDuration,
}) => {
  const frame = useCurrentFrame();
  const elapsed = frame - startFrame;

  if (elapsed < 0) return null;

  const progress = interpolate(elapsed, [0, drawDuration], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* specification → prompt */}
      <DashedConnector
        x1={specX}
        y1={LINE1_Y + LINE_BOTTOM + 18}
        x2={promptX}
        y2={LINE2_Y - 6}
        progress={progress}
      />
      {/* hardware → software */}
      <DashedConnector
        x1={hardwareX}
        y1={LINE1_Y + LINE_BOTTOM + 18}
        x2={softwareX}
        y2={LINE2_Y - 6}
        progress={progress}
      />
    </svg>
  );
};

interface DashedConnectorProps {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  progress: number;
}

const DashedConnector: React.FC<DashedConnectorProps> = ({
  x1,
  y1,
  x2,
  y2,
  progress,
}) => {
  return (
    <line
      x1={x1}
      y1={y1}
      x2={x1 + (x2 - x1) * progress}
      y2={y1 + (y2 - y1) * progress}
      stroke={CONNECTING_LINE_COLOR}
      strokeOpacity={CONNECTING_LINE_OPACITY}
      strokeWidth={1.5}
      strokeDasharray="6 4"
      strokeLinecap="round"
      style={{
        strokeDashoffset: 0,
      }}
    />
  );
};
