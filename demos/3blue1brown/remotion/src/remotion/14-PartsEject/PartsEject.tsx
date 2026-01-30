import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { MoldAndParts } from "./MoldAndParts";
import { PartCounter } from "./PartCounter";
import { COLORS, BEATS, PartsEjectPropsType } from "./constants";

export const PartsEject: React.FC<PartsEjectPropsType> = ({
  showNarration = true,
}) => {
  const frame = useCurrentFrame();

  // Narration fade-in during hold phase
  const narrationOpacity = showNarration
    ? interpolate(frame, [BEATS.NARRATION_START, BEATS.NARRATION_START + 30], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
        easing: Easing.out(Easing.cubic),
      })
    : 0;

  return (
    <AbsoluteFill
      style={{
        background: `linear-gradient(180deg, ${COLORS.BACKGROUND} 0%, ${COLORS.BACKGROUND_GRADIENT_END} 100%)`,
      }}
    >
      {/* Mold cross-section + ejected parts + stream */}
      <MoldAndParts />

      {/* Counter display */}
      <PartCounter />

      {/* Narration overlay */}
      {narrationOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: 120,
            left: 0,
            right: 0,
            textAlign: "center",
            opacity: narrationOpacity,
          }}
        >
          <div
            style={{
              fontSize: 32,
              fontFamily: "sans-serif",
              fontWeight: 400,
              color: "rgba(255, 255, 255, 0.95)",
              lineHeight: 1.6,
              maxWidth: 900,
              margin: "0 auto",
              letterSpacing: 0.5,
            }}
          >
            Make the mold once, produce unlimited identical parts.
            <br />
            Refine the mold once, every future part improves automatically.
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
