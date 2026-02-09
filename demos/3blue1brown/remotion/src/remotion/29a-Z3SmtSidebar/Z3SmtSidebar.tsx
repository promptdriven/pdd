import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TEXT, LAYOUT, Z3SmtSidebarPropsType } from "./constants";

export const Z3SmtSidebar: React.FC<Z3SmtSidebarPropsType> = ({
  showOverlay = true,
}) => {
  const frame = useCurrentFrame();

  // Synopsys icon fade-in
  const synopsysOpacity = interpolate(
    frame,
    [BEATS.SYNOPSYS_START, BEATS.SYNOPSYS_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Z3 icon fade-in
  const z3Opacity = interpolate(
    frame,
    [BEATS.Z3_START, BEATS.Z3_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Bridge line draw progress (0 to 1)
  const bridgeProgress = interpolate(
    frame,
    [BEATS.BRIDGE_START, BEATS.BRIDGE_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Text lines staggered
  const line1Opacity = interpolate(
    frame,
    [BEATS.LINE1_START, BEATS.LINE1_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const line2Opacity = interpolate(
    frame,
    [BEATS.LINE2_START, BEATS.LINE2_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const line3Opacity = interpolate(
    frame,
    [BEATS.LINE3_START, BEATS.LINE3_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // "Same math." pulse
  const sameMathPulse =
    frame > BEATS.PULSE_START
      ? 1.0 + Math.sin((frame - BEATS.PULSE_START) * 0.08) * 0.1
      : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Sidebar accent lines (top and bottom) */}
      {showOverlay && (
        <>
          <div
            style={{
              position: "absolute",
              top: 80,
              left: 120,
              right: 120,
              height: 1,
              background: COLORS.TEAL,
              opacity: 0.3,
            }}
          />
          <div
            style={{
              position: "absolute",
              bottom: 80,
              left: 120,
              right: 120,
              height: 1,
              background: COLORS.TEAL,
              opacity: 0.3,
            }}
          />
        </>
      )}

      {/* Logo row */}
      <div
        style={{
          display: "flex",
          justifyContent: "center",
          alignItems: "center",
          gap: LAYOUT.BRIDGE_WIDTH,
          position: "absolute",
          top: LAYOUT.LOGO_Y,
          left: 0,
          right: 0,
        }}
      >
        {/* Synopsys Formality */}
        <div
          style={{
            opacity: synopsysOpacity,
            textAlign: "center",
          }}
        >
          {/* Synopsys icon (checkmark) */}
          <div
            style={{
              width: 100,
              height: 100,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              margin: "0 auto",
            }}
          >
            <svg width="80" height="80" viewBox="0 0 80 80">
              <path
                d="M 15 40 L 32 60 L 65 20"
                stroke={COLORS.TEAL}
                strokeWidth="6"
                fill="none"
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            </svg>
          </div>
          <div
            style={{
              marginTop: 16,
              fontSize: 16,
              color: COLORS.TEAL,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.SYNOPSYS_LABEL}
          </div>
        </div>

        {/* Bridge line */}
        <div
          style={{
            position: "relative",
            width: LAYOUT.BRIDGE_WIDTH,
            height: 2,
          }}
        >
          {/* Line */}
          <div
            style={{
              width: `${bridgeProgress * 100}%`,
              height: 2,
              backgroundColor: COLORS.TEAL,
              boxShadow: `0 0 8px ${COLORS.TEAL}`,
            }}
          />
          {/* Center equivalence symbol */}
          {bridgeProgress > 0.5 && (
            <div
              style={{
                position: "absolute",
                top: -14,
                left: "50%",
                transform: "translateX(-50%)",
                fontSize: 20,
                color: COLORS.TEAL,
                opacity: (bridgeProgress - 0.5) * 2,
              }}
            >
              =
            </div>
          )}
        </div>

        {/* Z3 */}
        <div
          style={{
            opacity: z3Opacity,
            textAlign: "center",
          }}
        >
          {/* Z3 icon */}
          <div
            style={{
              width: 100,
              height: 100,
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              margin: "0 auto",
            }}
          >
            <div
              style={{
                fontSize: 48,
                fontWeight: "bold",
                color: COLORS.TEAL,
                fontFamily: "JetBrains Mono, monospace",
              }}
            >
              Z3
            </div>
          </div>
          <div
            style={{
              marginTop: 16,
              fontSize: 16,
              color: COLORS.TEAL,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.Z3_LABEL}
          </div>
        </div>
      </div>

      {/* Comparison text */}
      <div
        style={{
          position: "absolute",
          bottom: LAYOUT.TEXT_BOTTOM,
          width: "100%",
          textAlign: "center",
        }}
      >
        <div
          style={{
            fontSize: 24,
            color: COLORS.MUTED_WHITE,
            opacity: line1Opacity,
            fontFamily: "Inter, sans-serif",
            marginBottom: 12,
          }}
        >
          {TEXT.LINE1}
        </div>
        <div
          style={{
            fontSize: 24,
            color: COLORS.MUTED_WHITE,
            opacity: line2Opacity,
            fontFamily: "Inter, sans-serif",
            marginBottom: 20,
          }}
        >
          {TEXT.LINE2}
        </div>
        <div
          style={{
            fontSize: 32,
            color: COLORS.BRIGHT_WHITE,
            opacity: line3Opacity,
            fontWeight: 700,
            fontFamily: "Inter, sans-serif",
            transform: `scale(${sameMathPulse})`,
          }}
        >
          {TEXT.LINE3}
        </div>
      </div>
    </AbsoluteFill>
  );
};
