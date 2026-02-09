import React from "react";
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from "remotion";
import { COLORS, BEATS, TEXT, LAYOUT, FormalVerificationPropsType } from "./constants";

export const FormalVerification: React.FC<FormalVerificationPropsType> = ({
  showOverlay = true,
}) => {
  const frame = useCurrentFrame();

  // Divider line draw
  const dividerHeight = interpolate(
    frame,
    [BEATS.DIVIDER_START, BEATS.DIVIDER_END],
    [0, 100],
    { extrapolateRight: "clamp", easing: Easing.inOut(Easing.quad) }
  );

  // Left panel
  const leftHeaderOpacity = interpolate(
    frame,
    [BEATS.LEFT_HEADER_START, BEATS.LEFT_HEADER_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const leftTextOpacity = interpolate(
    frame,
    [BEATS.LEFT_TEXT_START, BEATS.LEFT_TEXT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Right panel
  const rightHeaderOpacity = interpolate(
    frame,
    [BEATS.RIGHT_HEADER_START, BEATS.RIGHT_HEADER_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const rightTextOpacity = interpolate(
    frame,
    [BEATS.RIGHT_TEXT_START, BEATS.RIGHT_TEXT_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Mathematical notation
  const mathOpacity = interpolate(
    frame,
    [BEATS.MATH_START, BEATS.MATH_END],
    [0, 0.6],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Shared bottom label
  const labelOpacity = interpolate(
    frame,
    [BEATS.LABEL_START, BEATS.LABEL_END],
    [0, 1],
    { extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Gentle pulse on bottom label
  const labelPulse =
    frame > BEATS.PULSE_START ? 1.0 + Math.sin((frame - BEATS.PULSE_START) * 0.06) * 0.05 : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.BACKGROUND }}>
      {/* Center divider */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: LAYOUT.DIVIDER_TOP,
          width: 1,
          height: `${(dividerHeight / 100) * LAYOUT.DIVIDER_HEIGHT}px`,
          backgroundColor: COLORS.TEAL,
          opacity: 0.3,
        }}
      />

      {/* Left Panel: Synopsys Formality */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: "50%",
          height: "100%",
          padding: `${LAYOUT.PANEL_PADDING_V}px ${LAYOUT.PANEL_PADDING_H}px`,
        }}
      >
        {/* Header */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: COLORS.TEAL,
            fontFamily: "Inter, sans-serif",
            opacity: leftHeaderOpacity,
            textAlign: "center",
            marginBottom: 40,
          }}
        >
          {TEXT.LEFT_HEADER}
        </div>

        {/* Circuit icon */}
        <div
          style={{
            opacity: leftHeaderOpacity,
            display: "flex",
            justifyContent: "center",
            marginBottom: 40,
          }}
        >
          <svg width={LAYOUT.ICON_SIZE} height={LAYOUT.ICON_SIZE} viewBox="0 0 80 80">
            <circle cx="20" cy="40" r="8" stroke={COLORS.TEAL} strokeWidth="2" fill="none" />
            <circle cx="60" cy="40" r="8" stroke={COLORS.TEAL} strokeWidth="2" fill="none" />
            <line x1="28" y1="40" x2="52" y2="40" stroke={COLORS.TEAL} strokeWidth="2" />
            <circle cx="40" cy="40" r="4" fill={COLORS.TEAL} />
          </svg>
        </div>

        {/* Proof description */}
        <div style={{ opacity: leftTextOpacity, textAlign: "center" }}>
          <div
            style={{
              fontSize: 22,
              color: COLORS.MUTED_WHITE,
              marginBottom: 8,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.LEFT_PREFIX}
          </div>
          <div
            style={{
              fontSize: 28,
              color: COLORS.BRIGHT_WHITE,
              fontWeight: 600,
              marginBottom: 8,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.LEFT_RELATION}
          </div>
          <div
            style={{
              fontSize: 22,
              color: COLORS.MUTED_WHITE,
              fontStyle: "italic",
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.LEFT_QUALIFIER}
          </div>
        </div>

        {/* Math notation */}
        {mathOpacity > 0 && (
          <div
            style={{
              opacity: mathOpacity,
              marginTop: 40,
              fontSize: 18,
              fontFamily: "Georgia, serif",
              fontStyle: "italic",
              color: COLORS.MATH_GRAY,
              letterSpacing: 1,
              textAlign: "center",
            }}
          >
            {TEXT.LEFT_MATH}
          </div>
        )}
      </div>

      {/* Right Panel: PDD + Z3 */}
      <div
        style={{
          position: "absolute",
          right: 0,
          top: 0,
          width: "50%",
          height: "100%",
          padding: `${LAYOUT.PANEL_PADDING_V}px ${LAYOUT.PANEL_PADDING_H}px`,
        }}
      >
        {/* Header */}
        <div
          style={{
            fontSize: 28,
            fontWeight: 600,
            color: COLORS.TEAL,
            fontFamily: "Inter, sans-serif",
            opacity: rightHeaderOpacity,
            textAlign: "center",
            marginBottom: 40,
          }}
        >
          {TEXT.RIGHT_HEADER}
        </div>

        {/* Code/prompt icon */}
        <div
          style={{
            opacity: rightHeaderOpacity,
            display: "flex",
            justifyContent: "center",
            marginBottom: 40,
          }}
        >
          <svg width={LAYOUT.ICON_SIZE} height={LAYOUT.ICON_SIZE} viewBox="0 0 80 80">
            <path
              d="M 20 20 L 30 40 L 20 60"
              stroke={COLORS.TEAL}
              strokeWidth="4"
              fill="none"
              strokeLinecap="round"
              strokeLinejoin="round"
            />
            <path
              d="M 60 20 L 50 40 L 60 60"
              stroke={COLORS.TEAL}
              strokeWidth="4"
              fill="none"
              strokeLinecap="round"
              strokeLinejoin="round"
            />
            <line x1="45" y1="25" x2="35" y2="55" stroke={COLORS.TEAL} strokeWidth="3" />
          </svg>
        </div>

        {/* Proof description */}
        <div style={{ opacity: rightTextOpacity, textAlign: "center" }}>
          <div
            style={{
              fontSize: 22,
              color: COLORS.MUTED_WHITE,
              marginBottom: 8,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.RIGHT_PREFIX}
          </div>
          <div
            style={{
              fontSize: 28,
              color: COLORS.BRIGHT_WHITE,
              fontWeight: 600,
              marginBottom: 8,
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.RIGHT_RELATION}
          </div>
          <div
            style={{
              fontSize: 22,
              color: COLORS.MUTED_WHITE,
              fontStyle: "italic",
              fontFamily: "Inter, sans-serif",
            }}
          >
            {TEXT.RIGHT_QUALIFIER}
          </div>
        </div>

        {/* Math notation */}
        {mathOpacity > 0 && (
          <div
            style={{
              opacity: mathOpacity,
              marginTop: 40,
              fontSize: 18,
              fontFamily: "Georgia, serif",
              fontStyle: "italic",
              color: COLORS.MATH_GRAY,
              letterSpacing: 1,
              textAlign: "center",
            }}
          >
            {TEXT.RIGHT_MATH}
          </div>
        )}
      </div>

      {/* Shared bottom label */}
      {labelOpacity > 0 && (
        <div
          style={{
            position: "absolute",
            bottom: LAYOUT.BOTTOM_LABEL_Y,
            width: "100%",
            textAlign: "center",
            opacity: labelOpacity,
            transform: `scale(${labelPulse})`,
          }}
        >
          <div
            style={{
              display: "flex",
              justifyContent: "center",
              alignItems: "center",
              gap: 20,
            }}
          >
            {/* Left checkmark */}
            <svg width="28" height="28" viewBox="0 0 28 28">
              <path
                d="M 4 14 L 10 20 L 24 6"
                stroke={COLORS.GREEN_CHECK}
                strokeWidth="3"
                fill="none"
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            </svg>

            <span
              style={{
                fontSize: 30,
                fontWeight: 700,
                color: COLORS.BRIGHT_WHITE,
                fontFamily: "Inter, sans-serif",
              }}
            >
              {TEXT.BOTTOM_LABEL}
            </span>

            {/* Right checkmark */}
            <svg width="28" height="28" viewBox="0 0 28 28">
              <path
                d="M 4 14 L 10 20 L 24 6"
                stroke={COLORS.GREEN_CHECK}
                strokeWidth="3"
                fill="none"
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            </svg>
          </div>
        </div>
      )}
    </AbsoluteFill>
  );
};
