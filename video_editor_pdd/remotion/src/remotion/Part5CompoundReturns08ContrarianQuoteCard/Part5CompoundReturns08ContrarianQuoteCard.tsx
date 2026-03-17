import React from "react";
import {
  AbsoluteFill,
  Sequence,
  useCurrentFrame,
  Easing,
  interpolate,
} from "remotion";
import "../_shared/load-inter-font";
import { COLORS, FRAMES } from "./constants";
import { NoiseBackground } from "./NoiseBackground";
import { QuoteTyper } from "./QuoteTyper";
import { ReframeSubtitle } from "./ReframeSubtitle";

export const defaultPart5CompoundReturns08ContrarianQuoteCardProps = {};

/**
 * 08_contrarian_quote_card — "The Bet"
 *
 * A clean typographic quote card with word-by-word reveal,
 * color-coded highlights (blue / amber), and a narrator reframe.
 * 300 frames @ 30 fps (~10 s).
 */
export const Part5CompoundReturns08ContrarianQuoteCard: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Decorative opening quote mark ---
  const quoteMarkOpacity = interpolate(frame, [0, 15], [0, 0.15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // --- Attribution fade ---
  const attrLocalFrame = frame - FRAMES.attributionStart;
  const attrOpacity =
    attrLocalFrame < 0
      ? 0
      : interpolate(attrLocalFrame, [0, FRAMES.attributionFadeDuration], [0, 0.4], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        });

  // --- Em-dash draw before attribution ---
  const dashWidth =
    attrLocalFrame < 0
      ? 0
      : interpolate(attrLocalFrame, [0, 10], [0, 16], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
          easing: Easing.out(Easing.quad),
        });

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Background with noise */}
      <NoiseBackground />

      {/* Decorative opening quote mark */}
      <div
        style={{
          position: "absolute",
          left: 320,
          top: 290,
          fontFamily: "Georgia, serif",
          fontSize: 120,
          color: COLORS.decorativeQuote,
          opacity: quoteMarkOpacity,
          lineHeight: 1,
          userSelect: "none",
        }}
      >
        {"\u201C"}
      </div>

      {/* Quote text – word by word with highlights */}
      <QuoteTyper />

      {/* Attribution */}
      <div
        style={{
          position: "absolute",
          top: 560,
          right: 320,
          display: "flex",
          alignItems: "center",
          gap: 0,
          opacity: attrOpacity,
        }}
      >
        {/* Animated em-dash drawn before text */}
        <span
          style={{
            display: "inline-block",
            width: dashWidth,
            height: 1,
            backgroundColor: COLORS.attribution,
            marginRight: 8,
            flexShrink: 0,
          }}
        />
        <span
          style={{
            fontFamily: "Inter, sans-serif",
            fontSize: 14,
            color: COLORS.attribution,
            whiteSpace: "nowrap",
          }}
        >
          Research engineer, after seeing PDD for the first time
        </span>
      </div>

      {/* Narrator reframe subtitle */}
      <Sequence from={FRAMES.reframeStart} durationInFrames={FRAMES.total - FRAMES.reframeStart}>
        <ReframeSubtitle />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part5CompoundReturns08ContrarianQuoteCard;
