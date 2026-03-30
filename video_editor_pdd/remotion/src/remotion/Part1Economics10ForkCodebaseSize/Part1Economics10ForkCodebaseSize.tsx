import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { BG_COLOR, TOTAL_FRAMES, FONT_FAMILY } from "./constants";
import { ChartAxes } from "./ChartAxes";
import { ForkingLines } from "./ForkingLines";
import { Annotations } from "./Annotations";
import { TrapArrow } from "./TrapArrow";

export const defaultPart1Economics10ForkCodebaseSizeProps = {};

/**
 * Section 1.10: Fork by Codebase Size — The Trap
 *
 * The patch cost line forks at ~2020 into two diverging paths:
 * - Small codebase (green): AI patching is transformative
 * - Large codebase (red): experienced devs are actually 19% slower
 *
 * Duration: ~46s (1380 frames @ 30fps)
 */
export const Part1Economics10ForkCodebaseSize: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        fontFamily: FONT_FAMILY,
      }}
    >
      {/* Title */}
      <div
        style={{
          position: "absolute",
          top: 36,
          left: 0,
          right: 0,
          textAlign: "center",
          color: "#E2E8F0",
          fontSize: 22,
          fontWeight: 600,
          fontFamily: FONT_FAMILY,
          letterSpacing: "0.02em",
          opacity: 0.9,
        }}
      >
        Code Cost per Feature: Generate vs. Patch
      </div>

      {/* Chart axes & grid — visible from frame 0 */}
      <ChartAxes />

      {/* Lines: generate baseline, patch, and forking paths */}
      <ForkingLines />

      {/* Annotations: context label, METR stats, perception gap */}
      <Annotations />

      {/* Trap arrow: "Every patch adds code." */}
      <TrapArrow />
    </AbsoluteFill>
  );
};

export default Part1Economics10ForkCodebaseSize;
