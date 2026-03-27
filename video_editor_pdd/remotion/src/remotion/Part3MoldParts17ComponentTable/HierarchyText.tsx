import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";

const TESTS_BLUE = "#4A90D9";
const TEXT_COLOR = "#E2E8F0";
const SUBTEXT_COLOR = "#94A3B8";
const PULSE_CYCLE = 30;

export const HierarchyText: React.FC = () => {
  const frame = useCurrentFrame();

  // ─── Main hierarchy line (starts at frame 180) ───
  const hierLocal = frame - 180;
  const hierOpacity = interpolate(hierLocal, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Pulsing glow for the hierarchy line
  const pulsePhase = hierLocal > 20 ? (hierLocal - 20) % PULSE_CYCLE : 0;
  const pulseGlow = hierLocal > 20
    ? interpolate(
        pulsePhase,
        [0, PULSE_CYCLE / 2, PULSE_CYCLE - 1],
        [0.08, 0.15, 0.08],
        {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.inOut(Easing.sin),
        }
      )
    : 0;

  // ─── Subtext line (starts at frame 240) ───
  const subLocal = frame - 240;
  const subOpacity = interpolate(subLocal, [0, 20], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <>
      {/* Main hierarchy line */}
      {hierLocal >= 0 && (
        <div
          style={{
            position: "absolute",
            top: 620,
            left: 0,
            width: 1920,
            display: "flex",
            justifyContent: "center",
            opacity: hierOpacity,
          }}
        >
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 18,
              fontWeight: 600,
              color: TEXT_COLOR,
              textShadow: `0 0 10px rgba(74, 144, 217, ${pulseGlow})`,
              textAlign: "center",
            }}
          >
            <span>When these conflict, </span>
            <span
              style={{
                fontWeight: 700,
                color: TESTS_BLUE,
              }}
            >
              tests win
            </span>
            <span>. </span>
            <span
              style={{
                fontWeight: 700,
                color: TESTS_BLUE,
              }}
            >
              Always
            </span>
            <span>.</span>
          </div>
        </div>
      )}

      {/* Subtext */}
      {subLocal >= 0 && (
        <div
          style={{
            position: "absolute",
            top: 660,
            left: 0,
            width: 1920,
            display: "flex",
            justifyContent: "center",
            opacity: subOpacity,
          }}
        >
          <div
            style={{
              fontFamily: "Inter, sans-serif",
              fontSize: 14,
              fontWeight: 400,
              color: SUBTEXT_COLOR,
              textAlign: "center",
            }}
          >
            The walls override the specification. The specification overrides the
            style.
          </div>
        </div>
      )}
    </>
  );
};

export default HierarchyText;
