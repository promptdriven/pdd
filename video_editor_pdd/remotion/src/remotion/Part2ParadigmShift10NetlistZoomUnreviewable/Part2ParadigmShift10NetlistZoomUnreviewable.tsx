import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ChipLayoutMosaic } from "./ChipLayoutMosaic";
import { ScrollingCodeDiff } from "./ScrollingCodeDiff";
import {
  BG_COLOR,
  WIDTH,
  HEIGHT,
  CODE_FONT,
  COUNTER_FONT_SIZE,
  COUNTER_COLOR,
  COUNTER_OPACITY,
  GATE_COUNT_COLOR,
  GATE_COUNT_OPACITY,
  GATE_COUNT_FONT_SIZE,
  TOTAL_LINES_CHANGED,
  ZOOM_START,
  ZOOM_END,
  MORPH_START,
  MORPH_DURATION,
  DIFF_START,
  INITIAL_SCROLL_SPEED,
  MAX_SCROLL_SPEED,
  TOTAL_FRAMES,
} from "./constants";

export const defaultPart2ParadigmShift10NetlistZoomUnreviewableProps = {};

/**
 * Netlist Zoom — Unreviewable at Scale
 *
 * Phase 1 (0–240): Chip layout mosaic with dramatic infinite zoom (1x→8x).
 * Phase 2 (240–480): Scrolling code diff that accelerates to blur speed.
 * Morph transition at frames 200–240 crossfades between phases.
 */
export const Part2ParadigmShift10NetlistZoomUnreviewable: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Phase 1: Chip zoom ───────────────────────────────────────
  // Zoom from 1x to 8x over frames 30–150, using easeInOut cubic
  const zoom = interpolate(frame, [ZOOM_START, ZOOM_END], [1, 8], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Chip layout opacity: fully visible from frame 0, fades out during morph
  const chipOpacity = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [1, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Gate count label: fades in at frame 30, fades out during morph
  const gateCountOpacity = interpolate(
    frame,
    [30, 45, MORPH_START, MORPH_START + MORPH_DURATION],
    [0, GATE_COUNT_OPACITY, GATE_COUNT_OPACITY, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // ─── Morph transition ────────────────────────────────────────
  // Code diff fades in during morph (frames 200–240)
  const diffOpacity = interpolate(
    frame,
    [MORPH_START, MORPH_START + MORPH_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // ─── Phase 2: Code diff scroll ────────────────────────────────
  // Scroll offset: accelerate from 2px/frame to 30px/frame over 120 frames (240–360)
  // Then decelerate from 30px/frame to 0 over 60 frames (420–480)
  const diffFrame = Math.max(0, frame - DIFF_START);
  const scrollOffset = computeScrollOffset(diffFrame);

  // Line counter: counts from 0 to 10,247 over frames 240–420
  const counterRaw = interpolate(
    frame,
    [DIFF_START, DIFF_START + 180],
    [0, TOTAL_LINES_CHANGED],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );
  const counterValue = Math.round(counterRaw);

  // Counter opacity: appears with the diff, stays visible
  const counterOpacity = interpolate(
    frame,
    [DIFF_START, DIFF_START + 20],
    [0, COUNTER_OPACITY],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: WIDTH,
        height: HEIGHT,
        overflow: "hidden",
      }}
    >
      {/* Phase 1: Chip layout mosaic with zoom */}
      {chipOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 0,
            left: 0,
            width: WIDTH,
            height: HEIGHT,
            opacity: chipOpacity,
          }}
        >
          <ChipLayoutMosaic zoom={zoom} />
        </div>
      )}

      {/* Gate count label — upper right */}
      {gateCountOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 50,
            right: 80,
            fontFamily: CODE_FONT,
            fontSize: GATE_COUNT_FONT_SIZE,
            color: GATE_COUNT_COLOR,
            opacity: gateCountOpacity,
            zIndex: 10,
            letterSpacing: 0.5,
          }}
        >
          ~2.4 billion gates
        </div>
      )}

      {/* Phase 2: Scrolling code diff */}
      {diffOpacity > 0 && (
        <ScrollingCodeDiff scrollOffset={scrollOffset} opacity={diffOpacity} />
      )}

      {/* Line counter — upper right */}
      {counterOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            top: 50,
            right: 80,
            fontFamily: CODE_FONT,
            fontSize: COUNTER_FONT_SIZE,
            color: COUNTER_COLOR,
            opacity: counterOpacity,
            zIndex: 20,
            letterSpacing: 0.5,
            fontWeight: 600,
          }}
        >
          {counterValue.toLocaleString()} lines changed
        </div>
      )}
    </AbsoluteFill>
  );
};

/**
 * Compute cumulative scroll offset given a frame relative to diff start.
 *
 * Phase A (0–120): Accelerate from INITIAL_SCROLL_SPEED to MAX_SCROLL_SPEED
 * Phase B (120–180): Hold at MAX_SCROLL_SPEED
 * Phase C (180–240): Decelerate from MAX_SCROLL_SPEED to 0
 *
 * We integrate the speed function to get position.
 */
function computeScrollOffset(f: number): number {
  if (f <= 0) return 0;

  const accelEnd = 120;
  const holdEnd = 180;
  const decelEnd = 240;

  let offset = 0;

  if (f <= accelEnd) {
    // Accelerating: easeIn(quad) from initial to max speed
    // Speed at frame t: lerp(initial, max, easeIn(t/accelEnd))
    // Integrate numerically for accuracy
    for (let t = 0; t < f; t++) {
      const progress = t / accelEnd;
      const eased = progress * progress; // easeIn quad
      const speed =
        INITIAL_SCROLL_SPEED +
        (MAX_SCROLL_SPEED - INITIAL_SCROLL_SPEED) * eased;
      offset += speed;
    }
    return offset;
  }

  // Full acceleration phase
  for (let t = 0; t < accelEnd; t++) {
    const progress = t / accelEnd;
    const eased = progress * progress;
    const speed =
      INITIAL_SCROLL_SPEED + (MAX_SCROLL_SPEED - INITIAL_SCROLL_SPEED) * eased;
    offset += speed;
  }

  if (f <= holdEnd) {
    // Holding at max speed
    offset += MAX_SCROLL_SPEED * (f - accelEnd);
    return offset;
  }

  // Full hold phase
  offset += MAX_SCROLL_SPEED * (holdEnd - accelEnd);

  if (f <= decelEnd) {
    // Decelerating: easeOut(cubic) from max speed to 0
    const decelDuration = decelEnd - holdEnd;
    for (let t = 0; t < f - holdEnd; t++) {
      const progress = t / decelDuration;
      // easeOut cubic: 1 - (1-t)^3 → speed = max * (1-t)^3
      const remaining = 1 - progress;
      const speed = MAX_SCROLL_SPEED * remaining * remaining * remaining;
      offset += speed;
    }
    return offset;
  }

  // Full deceleration phase (if past end, hold position)
  const decelDuration = decelEnd - holdEnd;
  for (let t = 0; t < decelDuration; t++) {
    const progress = t / decelDuration;
    const remaining = 1 - progress;
    const speed = MAX_SCROLL_SPEED * remaining * remaining * remaining;
    offset += speed;
  }

  return offset;
}

export default Part2ParadigmShift10NetlistZoomUnreviewable;
