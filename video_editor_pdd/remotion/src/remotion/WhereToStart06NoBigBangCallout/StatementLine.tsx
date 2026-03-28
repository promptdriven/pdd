import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  TEXT_FONT_SIZE,
  TEXT_SLIDE_DISTANCE,
  TEXT_ANIM_DURATION,
  RULE_DRAW_DELAY,
  RULE_DRAW_DURATION,
  RULE_THICKNESS,
  RULE_OFFSET_TOP,
  RULE_COLOR_SLATE,
  RULE_COLOR_GREEN,
  RULE_OPACITY_SLATE,
  RULE_OPACITY_GREEN,
  RULE_WIDTH_SHORT,
  RULE_WIDTH_LONG,
  TEXT_COLOR_ACCENT,
  PULSE_START,
  PULSE_DURATION,
} from "./constants";

interface StatementLineProps {
  text: string;
  color: string;
  weight: number;
  startFrame: number;
}

export const StatementLine: React.FC<StatementLineProps> = ({
  text,
  color,
  weight,
  startFrame,
}) => {
  const frame = useCurrentFrame();
  const isAccent = color === TEXT_COLOR_ACCENT;

  // Text fade + slide
  const localTextFrame = frame - startFrame;
  const textOpacity = interpolate(
    localTextFrame,
    [0, TEXT_ANIM_DURATION],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );
  const textTranslateX = interpolate(
    localTextFrame,
    [0, TEXT_ANIM_DURATION],
    [-TEXT_SLIDE_DISTANCE, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  // Rule draw
  const ruleStartFrame = startFrame + RULE_DRAW_DELAY;
  const localRuleFrame = frame - ruleStartFrame;
  const ruleTargetWidth = isAccent ? RULE_WIDTH_LONG : RULE_WIDTH_SHORT;
  const ruleWidth = interpolate(
    localRuleFrame,
    [0, RULE_DRAW_DURATION],
    [0, ruleTargetWidth],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  const ruleColor = isAccent ? RULE_COLOR_GREEN : RULE_COLOR_SLATE;
  const ruleBaseOpacity = isAccent ? RULE_OPACITY_GREEN : RULE_OPACITY_SLATE;

  // Green rule pulse (frame 110-140)
  let ruleFinalOpacity = ruleBaseOpacity;
  if (isAccent && frame >= PULSE_START) {
    const pulseLocal = frame - PULSE_START;
    const pulseFactor = interpolate(
      pulseLocal,
      [0, PULSE_DURATION / 2, PULSE_DURATION],
      [1, 1.6, 1],
      { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.sin) }
    );
    ruleFinalOpacity = ruleBaseOpacity * pulseFactor;
  }

  // Consistent total block height: text (fontSize * lineHeight) + ruleOffset + ruleThickness + marginBottom
  const blockMarginBottom = 70 - TEXT_FONT_SIZE;
  const blockHeight = TEXT_FONT_SIZE + RULE_OFFSET_TOP + RULE_THICKNESS + blockMarginBottom;

  // Before start frame: invisible placeholder preserving layout
  if (frame < startFrame) {
    return <div style={{ height: blockHeight }} />;
  }

  return (
    <div style={{ marginBottom: blockMarginBottom }}>
      <div
        style={{
          opacity: textOpacity,
          transform: `translateX(${textTranslateX}px)`,
          fontFamily: "Inter, sans-serif",
          fontSize: TEXT_FONT_SIZE,
          fontWeight: weight,
          color,
          lineHeight: 1,
          whiteSpace: "nowrap",
        }}
      >
        {text}
      </div>
      <div
        style={{
          marginTop: RULE_OFFSET_TOP,
          height: RULE_THICKNESS,
          width: ruleWidth,
          backgroundColor: ruleColor,
          opacity: localRuleFrame < 0 ? 0 : ruleFinalOpacity,
          borderRadius: 1,
        }}
      />
    </div>
  );
};
