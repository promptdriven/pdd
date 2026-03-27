import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  INSET_X,
  INSET_Y,
  INSET_WIDTH,
  INSET_HEIGHT,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PHASE_INSET_FADEOUT_START,
  PHASE_INSET_FADEOUT_END,
} from "./constants";
import { CodeBlockGrid } from "./CodeBlockGrid";
import { InsetChart } from "./InsetChart";
import { AnimatedLine } from "./AnimatedLine";
import { DebtAreaChart } from "./DebtAreaChart";

export const defaultPart1Economics08PerformanceVsContextProps = {};

/**
 * Section 1.8: Performance vs. Context Length — EMNLP Study Inset
 *
 * Duration: ~49s (1470 frames @ 30fps)
 *
 * Animation phases:
 *  0-60:    Grid dims to 30%, inset border draws in
 *  60-90:   Inset background fills, title types in
 *  90-210:  Axes draw, line animates (declining performance)
 *  210-360: Hold on inset, labels appear
 *  360-600: Hold (narration covers EMNLP study)
 *  600-720: Inset fades out, transition to debt chart
 *  720-900: Context Rot pulse + "Faster patching…" annotation
 *  900-1470: Final hold with pulsing debt area
 */
export const Part1Economics08PerformanceVsContext: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Inset chart opacity (visible 0–720, fades out 600–720) ─────────
  const insetOpacity = interpolate(
    frame,
    [0, 1, PHASE_INSET_FADEOUT_START, PHASE_INSET_FADEOUT_END],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Inset position: center-right area ──────────────────────────────
  // Spec says (1350, 680) but we position the top-left of the inset so
  // it appears in lower-right. Adjust for anchor = center of inset.
  const insetLeft = INSET_X - INSET_WIDTH / 2;
  const insetTop = INSET_Y - INSET_HEIGHT / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        overflow: "hidden",
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* ─── Background: Dimmed code block grid ──────────────────────── */}
      <CodeBlockGrid />

      {/* ─── Inset chart (frames 0–720) ──────────────────────────────── */}
      <Sequence from={0} durationInFrames={PHASE_INSET_FADEOUT_END}>
        <div
          style={{
            position: "absolute",
            left: insetLeft,
            top: insetTop,
            width: INSET_WIDTH,
            height: INSET_HEIGHT,
            opacity: insetOpacity,
          }}
        >
          <InsetChart localFrame={frame}>
            <AnimatedLine localFrame={frame} />
          </InsetChart>
        </div>
      </Sequence>

      {/* ─── Debt area chart with Context Rot pulse (frames 600+) ──── */}
      <Sequence from={PHASE_INSET_FADEOUT_START}>
        <DebtAreaChart localFrame={frame - PHASE_INSET_FADEOUT_START} />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics08PerformanceVsContext;
