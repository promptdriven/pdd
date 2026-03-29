import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CONNECTING_LINE_COLOR,
  CONNECTING_LINE_OPACITY,
  CONNECTING_START,
  LINE1_Y,
  LINE2_Y,
  MAIN_FONT_SIZE,
} from "./constants";

/**
 * Draws dashed connecting lines between equivalent words:
 *   "specification" (line1) ↔ "prompt" (line2)
 *   "hardware" (line1) ↔ "software" (line2)
 *
 * Horizontal positions are estimated from ~17px average char width at 32px Inter.
 */

// Approximate character width for Inter at 32px
const CHAR_W = 17;

// Line 1: "Synopsys: specification in → verified hardware out."
// Indices: S(0) y(1) n(2) o(3) p(4) s(5) y(6) s(7) :(8) (9)
//   s(10)p(11)e(12)c(13)i(14)f(15)i(16)c(17)a(18)t(19)i(20)o(21)n(22)
//   (23)i(24)n(25) (26)→(27) (28)v(29)e(30)r(31)i(32)f(33)i(34)e(35)d(36)
//   (37)h(38)a(39)r(40)d(41)w(42)a(43)r(44)e(45) (46)o(47)u(48)t(49).(50)
const LINE1_TOTAL = 51;
const LINE1_LEFT = (CANVAS_WIDTH - LINE1_TOTAL * CHAR_W) / 2;

// "specification" starts at index 10, length 13
const SPEC_CENTER_X = LINE1_LEFT + (10 + 13 / 2) * CHAR_W;
// "hardware" starts at index 38, length 8
const HW_CENTER_X = LINE1_LEFT + (38 + 8 / 2) * CHAR_W;

// Line 2: "PDD: prompt in → verified software out."
// P(0) D(1) D(2) :(3) _(4) p(5) r(6) o(7) m(8) p(9) t(10) _(11) i(12) n(13)
// _(14) →(15) _(16) v(17) e(18) r(19) i(20) f(21) i(22) e(23) d(24)
// _(25) s(26) o(27) f(28) t(29) w(30) a(31) r(32) e(33) _(34) o(35) u(36) t(37) .(38)
const LINE2_TOTAL = 39;
const LINE2_LEFT = (CANVAS_WIDTH - LINE2_TOTAL * CHAR_W) / 2;

// "prompt" starts at index 5, length 6
const PROMPT_CENTER_X = LINE2_LEFT + (5 + 6 / 2) * CHAR_W;
// "software" starts at index 26, length 8
const SW_CENTER_X = LINE2_LEFT + (26 + 8 / 2) * CHAR_W;

const LINE_TOP = LINE1_Y + MAIN_FONT_SIZE + 4;
const LINE_BOTTOM = LINE2_Y - 4;

interface DashedConnectorProps {
  x1: number;
  x2: number;
  y1: number;
  y2: number;
  progress: number;
}

const DashedConnector: React.FC<DashedConnectorProps> = ({
  x1,
  x2,
  y1,
  y2,
  progress,
}) => {
  const dx = x2 - x1;
  const dy = y2 - y1;
  const length = Math.sqrt(dx * dx + dy * dy);
  const visibleLength = length * progress;

  return (
    <line
      x1={x1}
      y1={y1}
      x2={x1 + (dx * visibleLength) / length}
      y2={y1 + (dy * visibleLength) / length}
      stroke={CONNECTING_LINE_COLOR}
      strokeWidth={1}
      strokeDasharray="6 4"
      opacity={CONNECTING_LINE_OPACITY}
    />
  );
};

export const ConnectingLines: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [CONNECTING_START, CONNECTING_START + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.ease),
    }
  );

  if (drawProgress <= 0) return null;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      {/* specification ↔ prompt */}
      <DashedConnector
        x1={SPEC_CENTER_X}
        y1={LINE_TOP}
        x2={PROMPT_CENTER_X}
        y2={LINE_BOTTOM}
        progress={drawProgress}
      />
      {/* hardware ↔ software */}
      <DashedConnector
        x1={HW_CENTER_X}
        y1={LINE_TOP}
        x2={SW_CENTER_X}
        y2={LINE_BOTTOM}
        progress={drawProgress}
      />
    </svg>
  );
};
