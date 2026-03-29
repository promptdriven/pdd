import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  DOC_BG,
  DOC_BORDER,
  DOC_WIDTH,
  DOC_HEIGHT,
  DOC_X,
  DOC_Y,
  DOC_PADDING,
  DOC_RADIUS,
  DOC_FADE_IN_START,
  DOC_FADE_IN_END,
  ANNOTATION_NL_COLOR,
  ANNOTATION_CODE_COLOR,
  BOTTOM_LABEL_COLOR,
  BOTTOM_LABEL_SIZE,
  BOTTOM_LABEL_TEXT,
  BOTTOM_LABEL_START,
  BOTTOM_LABEL_FADE_DURATION,
  FADE_OUT_START,
  FADE_OUT_END,
} from "./constants";
import DocumentContent from "./DocumentContent";
import AnnotationArrow from "./AnnotationArrow";

// ── Default props (required by export contract) ─────────────────────────────
export const defaultPart4PrecisionTradeoff08EmbeddedCodeDocumentProps = {};

// ── Main Component ──────────────────────────────────────────────────────────
export const Part4PrecisionTradeoff08EmbeddedCodeDocument: React.FC = () => {
  const frame = useCurrentFrame();

  // ── Document container fade-in ────────────────────────────────────────────
  const docOpacity = interpolate(
    frame,
    [DOC_FADE_IN_START, DOC_FADE_IN_END],
    [0.15, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Bottom label fade-in ──────────────────────────────────────────────────
  const labelOpacity = interpolate(
    frame,
    [BOTTOM_LABEL_START, BOTTOM_LABEL_START + BOTTOM_LABEL_FADE_DURATION],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  // ── Global fade-out ───────────────────────────────────────────────────────
  const fadeOut = interpolate(
    frame,
    [FADE_OUT_START, FADE_OUT_END],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.quad),
    }
  );

  // ── Annotation arrow y-positions (relative to doc) ────────────────────────
  // Prose sits at roughly top third, code block at roughly mid section
  const proseArrowY = DOC_Y + 200;
  const codeArrowY = DOC_Y + 440;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        opacity: fadeOut,
      }}
    >
      {/* ── Document Container ────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          left: DOC_X,
          top: DOC_Y,
          width: DOC_WIDTH,
          height: DOC_HEIGHT,
          backgroundColor: DOC_BG,
          border: `1px solid ${DOC_BORDER}`,
          borderRadius: DOC_RADIUS,
          padding: DOC_PADDING,
          opacity: docOpacity,
          overflow: "hidden",
          // Subtle paper texture via faint diagonal repeating gradient
          backgroundImage: `
            repeating-linear-gradient(
              45deg,
              transparent,
              transparent 10px,
              rgba(30, 41, 59, 0.02) 10px,
              rgba(30, 41, 59, 0.02) 11px
            )
          `,
        }}
      >
        <DocumentContent />
      </div>

      {/* ── Annotation Arrows ─────────────────────────────────────────── */}
      <AnnotationArrow
        tipX={DOC_X}
        tipY={proseArrowY}
        label="Natural language"
        color={ANNOTATION_NL_COLOR}
        delay={0}
      />
      <AnnotationArrow
        tipX={DOC_X}
        tipY={codeArrowY}
        label="Embedded code"
        color={ANNOTATION_CODE_COLOR}
        delay={10}
      />

      {/* ── Bottom Label ──────────────────────────────────────────────── */}
      <div
        style={{
          position: "absolute",
          bottom: 60,
          left: 0,
          right: 0,
          display: "flex",
          justifyContent: "center",
          opacity: labelOpacity,
        }}
      >
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: BOTTOM_LABEL_SIZE,
            fontWeight: 400,
            color: BOTTOM_LABEL_COLOR,
          }}
        >
          {BOTTOM_LABEL_TEXT}
        </span>
      </div>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff08EmbeddedCodeDocument;
