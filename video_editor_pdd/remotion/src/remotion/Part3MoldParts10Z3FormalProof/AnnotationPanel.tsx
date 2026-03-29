import React from "react";
import { interpolate } from "remotion";

// ── Inline constants (no cross-file imports) ──
const PANEL_BG = "#0F172A";
const PANEL_BORDER = "#334155";
const TEXT_PRIMARY = "#CDD6F4";
const TEXT_EMPHASIS = "#E2E8F0";
const PURPLE_ACCENT = "#A78BFA";
const PURPLE_DEEP = "#7C3AED";

const MAIN_TEXT_WORDS = [
  "PDD", "also", "uses", "Z3", "—", "the", "same", "class", "of",
  "SMT", "solver", "used", "in", "chip", "verification", "—", "to",
  "formally", "prove", "properties", "hold", "for", "every", "possible", "input.",
];

// Indices of highlighted words/phrases
const HIGHLIGHT_MAP: Record<number, boolean> = {
  3: true,   // Z3
  9: true,   // SMT
  10: true,  // solver
  17: true,  // formally
  18: true,  // prove
};

const EMPHASIS_TEXT = "Same math as billion-dollar tapeouts.";
const ITALIC_TEXT = "Not sampling. Mathematical proof.";

const BADGE_SIZE = 48;

interface AnnotationPanelProps {
  /** 0..1 panel slide-in progress */
  slideInProgress: number;
  /** 0..1 panel slide-out progress */
  slideOutProgress: number;
  /** Frame offset within the panel's local timeline */
  localFrame: number;
}

const AnnotationPanel: React.FC<AnnotationPanelProps> = ({
  slideInProgress,
  slideOutProgress,
  localFrame,
}) => {
  // Panel position — slides in from right, slides out to right
  const slideInX = interpolate(slideInProgress, [0, 1], [300, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const slideOutX = interpolate(slideOutProgress, [0, 1], [0, 300], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const panelTranslateX = slideInX + slideOutX;

  // Panel opacity
  const panelOpacity = interpolate(slideInProgress, [0, 0.3, 1], [0, 1, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  }) * interpolate(slideOutProgress, [0, 0.7, 1], [1, 1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Word-by-word typing (frames 30..90 in global = 30..90 in local) ──
  const wordTypingStart = 30;
  const framesPerWord = 3;

  // ── Emphasis line (frames 90..110) ──
  const emphasisProgress = interpolate(localFrame, [90, 110], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });
  const emphasisScale = interpolate(emphasisProgress, [0, 1], [0.95, 1.0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Italic line (frames 150..170) ──
  const italicOpacity = interpolate(localFrame, [150, 170], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // ── Badge fade (frames 210..230) ──
  const badgeOpacity = interpolate(localFrame, [210, 230], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Badge glow pulse
  const badgeGlow = interpolate(localFrame, [230, 260, 290], [0, 0.6, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  return (
    <div
      style={{
        position: "absolute",
        left: 1000,
        top: 200,
        width: 840,
        height: 580,
        transform: `translateX(${panelTranslateX}px)`,
        opacity: panelOpacity,
        background: PANEL_BG,
        border: `1px solid ${PANEL_BORDER}`,
        borderRadius: 12,
        padding: 32,
        boxSizing: "border-box",
        display: "flex",
        flexDirection: "column",
        gap: 20,
        fontFamily: "Inter, sans-serif",
      }}
    >
      {/* Main text — word-by-word */}
      <div style={{ lineHeight: 1.6, minHeight: 120 }}>
        {MAIN_TEXT_WORDS.map((word, i) => {
          const wordFrame = wordTypingStart + i * framesPerWord;
          const wordOpacity = interpolate(
            localFrame,
            [wordFrame, wordFrame + framesPerWord],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          const isHighlighted = HIGHLIGHT_MAP[i] === true;

          return (
            <span
              key={i}
              style={{
                opacity: wordOpacity,
                fontSize: 16,
                fontWeight: isHighlighted ? 700 : 400,
                color: isHighlighted ? PURPLE_ACCENT : TEXT_PRIMARY,
                marginRight: 5,
                display: "inline",
              }}
            >
              {word}{" "}
            </span>
          );
        })}
      </div>

      {/* Divider */}
      <div
        style={{
          width: "100%",
          height: 2,
          backgroundColor: PANEL_BORDER,
          opacity: 0.7,
        }}
      />

      {/* Emphasis line */}
      <div
        style={{
          opacity: emphasisProgress,
          transform: `scale(${emphasisScale})`,
          transformOrigin: "left center",
        }}
      >
        <span
          style={{
            fontSize: 18,
            fontWeight: 600,
            color: TEXT_EMPHASIS,
            lineHeight: 1.5,
          }}
        >
          {EMPHASIS_TEXT}
        </span>
      </div>

      {/* Italic line */}
      <div style={{ opacity: italicOpacity }}>
        <span
          style={{
            fontSize: 16,
            fontStyle: "italic",
            fontWeight: 400,
            color: PURPLE_ACCENT,
            opacity: 0.8,
            lineHeight: 1.5,
          }}
        >
          {ITALIC_TEXT}
        </span>
      </div>

      {/* Spacer */}
      <div style={{ flex: 1 }} />

      {/* Logo badges */}
      <div
        style={{
          display: "flex",
          justifyContent: "center",
          gap: 24,
          opacity: badgeOpacity,
        }}
      >
        {/* Z3 badge */}
        <div
          style={{
            width: BADGE_SIZE,
            height: BADGE_SIZE,
            backgroundColor: PURPLE_ACCENT,
            borderRadius: 8,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: `0 0 ${12 + badgeGlow * 20}px ${PURPLE_ACCENT}${Math.round(
              (0.3 + badgeGlow * 0.4) * 255
            )
              .toString(16)
              .padStart(2, "0")}`,
          }}
        >
          <span
            style={{
              color: "white",
              fontWeight: 700,
              fontSize: 18,
              fontFamily: "Inter, sans-serif",
            }}
          >
            Z3
          </span>
        </div>

        {/* SF (Synopsys Formality) badge */}
        <div
          style={{
            width: BADGE_SIZE,
            height: BADGE_SIZE,
            backgroundColor: PURPLE_DEEP,
            borderRadius: 8,
            display: "flex",
            alignItems: "center",
            justifyContent: "center",
            boxShadow: `0 0 ${12 + badgeGlow * 20}px ${PURPLE_DEEP}${Math.round(
              (0.3 + badgeGlow * 0.4) * 255
            )
              .toString(16)
              .padStart(2, "0")}`,
          }}
        >
          <span
            style={{
              color: "white",
              fontWeight: 700,
              fontSize: 18,
              fontFamily: "Inter, sans-serif",
            }}
          >
            SF
          </span>
        </div>
      </div>
    </div>
  );
};

export default AnnotationPanel;
