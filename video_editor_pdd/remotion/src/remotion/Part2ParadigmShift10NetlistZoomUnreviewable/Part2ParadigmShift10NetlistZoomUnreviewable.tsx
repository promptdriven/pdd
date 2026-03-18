import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { BG_COLOR, PHASE, LABEL_COLOR } from "./constants";
import { ChipLayoutMosaic } from "./ChipLayoutMosaic";
import { ScrollingCodeDiff } from "./ScrollingCodeDiff";

export const defaultPart2ParadigmShift10NetlistZoomUnreviewableProps = {};

export const Part2ParadigmShift10NetlistZoomUnreviewable: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 label: "Modern chip — ~2.4 billion gates."
  // Visible frames 0-30, fades in instantly
  const chipLabelOpacity = interpolate(
    frame,
    [0, 5, PHASE.chipZoomStart, PHASE.chipZoomStart + 30],
    [0.8, 0.8, 0.8, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Morph transition overlay — a brief flash/glow during transformation
  const morphGlowOpacity = interpolate(
    frame,
    [PHASE.morphStart, PHASE.morphStart + 20, PHASE.morphEnd],
    [0, 0.08, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Show chip layout for Phase 1 (with morph-out handled internally)
  const showChip = frame < PHASE.morphEnd;

  // Show code diff for Phase 2 (with morph-in handled internally)
  const showDiff = frame >= PHASE.morphStart;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Phase 1: Chip Layout Mosaic with infinite zoom */}
      {showChip && <ChipLayoutMosaic />}

      {/* Phase 2: Scrolling Code Diff */}
      {showDiff && <ScrollingCodeDiff />}

      {/* Morph transition glow overlay */}
      {morphGlowOpacity > 0 && (
        <AbsoluteFill
          style={{
            backgroundColor: "#4A90D9",
            opacity: morphGlowOpacity,
            pointerEvents: "none",
          }}
        />
      )}

      {/* Initial label: "Modern chip — ~2.4 billion gates." */}
      {chipLabelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            left: 0,
            right: 0,
            bottom: 80,
            textAlign: "center",
            fontFamily: "JetBrains Mono, monospace",
            fontSize: 18,
            color: LABEL_COLOR,
            opacity: chipLabelOpacity,
            letterSpacing: 0.5,
          }}
        >
          Modern chip — ~2.4 billion gates.
        </div>
      )}

      {/* Subtle vignette overlay for depth */}
      <div
        style={{
          position: "absolute",
          inset: 0,
          background:
            "radial-gradient(ellipse at center, transparent 50%, rgba(10, 15, 26, 0.4) 100%)",
          pointerEvents: "none",
        }}
      />
    </AbsoluteFill>
  );
};

export default Part2ParadigmShift10NetlistZoomUnreviewable;
