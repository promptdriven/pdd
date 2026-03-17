import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  FONT_FAMILY,
  HANDWRITTEN_FONT,
  TEXT_COLOR,
  LEFT_COLOR,
  RIGHT_COLOR,
  CENTER_TEXT_START,
  CENTER_TEXT_STAGGER,
  CENTER_TEXT_FADE,
  SUMMARY_START,
  SUMMARY_FADE,
  CHALLENGE_START,
  CHALLENGE_SLIDE_DURATION,
} from "./constants";

/**
 * CenterText renders the three-part colored insight text, summary line,
 * and the handwritten "Try it yourself." challenge.
 */
export const CenterText: React.FC = () => {
  const frame = useCurrentFrame();

  // Three word groups staggered
  const groups = [
    { text: "Bigger window", color: LEFT_COLOR, offset: 0 },
    { text: "AND", color: TEXT_COLOR, offset: CENTER_TEXT_STAGGER + CENTER_TEXT_FADE },
    { text: "smarter model.", color: RIGHT_COLOR, offset: (CENTER_TEXT_STAGGER + CENTER_TEXT_FADE) * 2 },
  ];

  // Summary line
  const summaryOpacity = interpolate(
    frame,
    [SUMMARY_START, SUMMARY_START + SUMMARY_FADE],
    [0, 0.6],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Challenge text
  const challengeProgress = interpolate(
    frame,
    [CHALLENGE_START, CHALLENGE_START + CHALLENGE_SLIDE_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.bezier(0.34, 1.56, 0.64, 1)) }
  );

  const challengeOpacity = interpolate(
    frame,
    [CHALLENGE_START, CHALLENGE_START + CHALLENGE_SLIDE_DURATION],
    [0, 0.5],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const challengeY = interpolate(challengeProgress, [0, 1], [12, 0]);

  return (
    <div style={{ position: "absolute", left: 0, top: 0, width: "100%", height: "100%" }}>
      {/* Center insight text */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 540,
          transform: "translateX(-50%)",
          display: "flex",
          gap: 10,
          alignItems: "baseline",
          whiteSpace: "nowrap",
        }}
      >
        {groups.map((group) => {
          const groupStart = CENTER_TEXT_START + group.offset;
          const opacity = interpolate(
            frame,
            [groupStart, groupStart + CENTER_TEXT_FADE],
            [0, group.text === "AND" ? 0.9 : 0.85],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
          );

          return (
            <span
              key={group.text}
              style={{
                fontFamily: FONT_FAMILY,
                fontSize: 22,
                fontWeight: 700,
                color: group.color,
                opacity,
              }}
            >
              {group.text}
            </span>
          );
        })}
      </div>

      {/* Subtle glow behind center text */}
      {frame >= CENTER_TEXT_START && (
        <div
          style={{
            position: "absolute",
            left: "50%",
            top: 540,
            width: 500,
            height: 40,
            transform: "translate(-50%, -50%)",
            background: "radial-gradient(ellipse, rgba(255,255,255,0.04) 0%, transparent 70%)",
            pointerEvents: "none",
          }}
        />
      )}

      {/* Summary line */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 620,
          transform: "translateX(-50%)",
          fontFamily: FONT_FAMILY,
          fontSize: 16,
          fontWeight: 400,
          color: TEXT_COLOR,
          opacity: summaryOpacity,
          whiteSpace: "nowrap",
          textAlign: "center",
        }}
      >
        Not one or the other. Both. That's a category shift.
      </div>

      {/* Challenge text */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          top: 740,
          transform: `translateX(-50%) translateY(${challengeY}px) rotate(-2deg)`,
          fontFamily: HANDWRITTEN_FONT,
          fontSize: 28,
          color: TEXT_COLOR,
          opacity: challengeOpacity,
          whiteSpace: "nowrap",
          textAlign: "center",
        }}
      >
        Try it yourself.
      </div>
    </div>
  );
};
