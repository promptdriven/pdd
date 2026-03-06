import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  SYNTHESIS_DEFAULT_COLOR,
  SYNTHESIS_HIGHLIGHT_COLOR,
  SYNTHESIS_Y,
  SYNTHESIS_APPEAR,
  SYNTHESIS_PHRASE1_HIGHLIGHT,
  SYNTHESIS_PHRASE2_HIGHLIGHT,
  SYNTHESIS_PHRASE3_HIGHLIGHT,
  SYNTHESIS_PHRASE_DURATION,
  FADEOUT_START,
  FADEOUT_END,
} from "./constants";

interface PhraseData {
  text: string;
  highlightFrame: number;
  accentColor: string;
}

const PHRASES: PhraseData[] = [
  {
    text: "Design the specification.",
    highlightFrame: SYNTHESIS_PHRASE1_HIGHLIGHT,
    accentColor: "#F97316",
  },
  {
    text: "Generate the implementation.",
    highlightFrame: SYNTHESIS_PHRASE2_HIGHLIGHT,
    accentColor: "#3B82F6",
  },
  {
    text: "Verify automatically.",
    highlightFrame: SYNTHESIS_PHRASE3_HIGHLIGHT,
    accentColor: "#22C55E",
  },
];

/** Lerp hex to white for text-shadow color */
function hexToRgba(hex: string, alpha: number): string {
  const h = hex.replace("#", "");
  const r = parseInt(h.substring(0, 2), 16);
  const g = parseInt(h.substring(2, 4), 16);
  const b = parseInt(h.substring(4, 6), 16);
  return `rgba(${r}, ${g}, ${b}, ${alpha})`;
}

export const SynthesisLine: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < SYNTHESIS_APPEAR) return null;

  // Appear opacity
  const appearOpacity = interpolate(
    frame,
    [SYNTHESIS_APPEAR, SYNTHESIS_APPEAR + 20],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Master fade-out
  const fadeOut = interpolate(frame, [FADEOUT_START, FADEOUT_END], [1, 0], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.in(Easing.cubic),
  });

  return (
    <div
      style={{
        position: "absolute",
        top: SYNTHESIS_Y,
        left: 0,
        width: 1920,
        display: "flex",
        justifyContent: "center",
        alignItems: "center",
        gap: 16,
        opacity: appearOpacity * fadeOut,
      }}
    >
      {PHRASES.map((phrase, i) => {
        // Highlight transition for each phrase
        const highlightProgress = interpolate(
          frame,
          [phrase.highlightFrame, phrase.highlightFrame + SYNTHESIS_PHRASE_DURATION],
          [0, 1],
          {
            extrapolateLeft: "clamp",
            extrapolateRight: "clamp",
            easing: Easing.out(Easing.cubic),
          }
        );

        const isHighlighted = frame >= phrase.highlightFrame;

        // Interpolate color from default gray to white
        const parseHex = (hex: string) => {
          const h = hex.replace("#", "");
          return [
            parseInt(h.substring(0, 2), 16),
            parseInt(h.substring(2, 4), 16),
            parseInt(h.substring(4, 6), 16),
          ];
        };
        const [dr, dg, db] = parseHex(SYNTHESIS_DEFAULT_COLOR);
        const [hr, hg, hb] = parseHex(SYNTHESIS_HIGHLIGHT_COLOR);
        const cr = Math.round(dr + (hr - dr) * highlightProgress);
        const cg = Math.round(dg + (hg - dg) * highlightProgress);
        const cb = Math.round(db + (hb - db) * highlightProgress);
        const currentColor = `rgb(${cr}, ${cg}, ${cb})`;

        const textShadow = isHighlighted
          ? `0 0 12px ${hexToRgba(phrase.accentColor, 0.5 * highlightProgress)}`
          : "none";

        return (
          <React.Fragment key={i}>
            {i > 0 && (
              <span
                style={{
                  fontFamily: "Inter, sans-serif",
                  fontWeight: 600,
                  fontSize: 22,
                  color: SYNTHESIS_DEFAULT_COLOR,
                }}
              >
                &mdash;
              </span>
            )}
            <span
              style={{
                fontFamily: "Inter, sans-serif",
                fontWeight: 600,
                fontSize: 22,
                color: currentColor,
                textShadow,
                transition: "none",
              }}
            >
              {phrase.text}
            </span>
          </React.Fragment>
        );
      })}
    </div>
  );
};
