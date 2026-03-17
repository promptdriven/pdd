import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  BLUE,
  GREEN,
  CODE_MUTED,
  TEXT_LIGHT,
  FONT_CODE,
  FONT_UI,
  PANEL_PADDING,
  PANEL_WIDTH,
  WINDOW_TOP,
  WINDOW_HEIGHT,
  SPLIT_X,
  RIGHT_PROMPT_START,
  RIGHT_PROMPT_END,
  RIGHT_TESTS_START,
  RIGHT_TESTS_END,
  RIGHT_GROUNDING_START,
  RIGHT_GROUNDING_END,
  TOKEN_COUNT_START,
  TOKEN_COUNT_END,
  FILL_BAR_START,
  FILL_BAR_END,
  PROMPT_LINES,
  TEST_LINES,
  GROUNDING_LINES,
} from "./constants";

const WINDOW_X = PANEL_PADDING;
const WINDOW_WIDTH = PANEL_WIDTH - PANEL_PADDING * 2;
const SECTION_LEFT_BORDER = 3;
const SECTION_INDENT = 16;

interface SectionBlockProps {
  lines: string[];
  label: string;
  accentColor: string;
  fontFamily: string;
  fontSize: number;
  textColor: string;
  textOpacity: number;
  top: number;
  opacity: number;
}

const SectionBlock: React.FC<SectionBlockProps> = ({
  lines,
  label,
  accentColor,
  fontFamily,
  fontSize,
  textColor,
  textOpacity,
  top,
  opacity,
}) => {
  return (
    <div
      style={{
        position: "absolute",
        left: WINDOW_X + 16,
        top: WINDOW_TOP + top,
        width: WINDOW_WIDTH - 32,
        opacity,
      }}
    >
      {/* Section label */}
      <div
        style={{
          fontFamily: FONT_UI,
          fontSize: 8,
          color: accentColor,
          opacity: 0.4,
          marginBottom: 4,
          letterSpacing: 1,
          textTransform: "uppercase",
        }}
      >
        {label}
      </div>

      {/* Content with left border */}
      <div
        style={{
          borderLeft: `${SECTION_LEFT_BORDER}px solid ${accentColor}4D`,
          paddingLeft: SECTION_INDENT,
        }}
      >
        {lines.map((line, i) => (
          <div
            key={i}
            style={{
              fontFamily,
              fontSize,
              color: textColor,
              opacity: textOpacity,
              lineHeight: "14px",
              whiteSpace: "pre-wrap",
            }}
          >
            {line || "\u00A0"}
          </div>
        ))}
      </div>
    </div>
  );
};

export const RightPanel: React.FC = () => {
  const frame = useCurrentFrame();

  // Prompt block fade
  const promptOpacity = interpolate(
    frame,
    [RIGHT_PROMPT_START, RIGHT_PROMPT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Tests block fade
  const testsOpacity = interpolate(
    frame,
    [RIGHT_TESTS_START, RIGHT_TESTS_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Grounding block fade
  const groundingOpacity = interpolate(
    frame,
    [RIGHT_GROUNDING_START, RIGHT_GROUNDING_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Token count opacity
  const tokenOpacity = interpolate(
    frame,
    [TOKEN_COUNT_START, TOKEN_COUNT_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // Fill bar width
  const fillBarProgress = interpolate(
    frame,
    [FILL_BAR_START, FILL_BAR_END],
    [0, 0.25],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  return (
    <div
      style={{
        position: "absolute",
        left: SPLIT_X + 2,
        top: 0,
        width: PANEL_WIDTH,
        height: "100%",
      }}
    >
      {/* Context window border */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          top: WINDOW_TOP,
          width: WINDOW_WIDTH,
          height: WINDOW_HEIGHT,
          border: `1px solid ${BLUE}4D`, // 0.3 opacity
          borderRadius: 6,
          overflow: "hidden",
        }}
      >
        {/* Fill indicator bar at bottom */}
        <div
          style={{
            position: "absolute",
            bottom: 0,
            left: 0,
            width: WINDOW_WIDTH,
            height: 3,
            backgroundColor: `${BLUE}0A`,
          }}
        >
          <div
            style={{
              width: `${fillBarProgress * 100}%`,
              height: "100%",
              backgroundColor: `${BLUE}33`,
            }}
          />
        </div>
      </div>

      {/* Prompt section */}
      <SectionBlock
        lines={PROMPT_LINES}
        label="prompt"
        accentColor={BLUE}
        fontFamily={FONT_UI}
        fontSize={10}
        textColor={TEXT_LIGHT}
        textOpacity={0.6}
        top={20}
        opacity={promptOpacity}
      />

      {/* Tests section */}
      <SectionBlock
        lines={TEST_LINES}
        label="tests"
        accentColor={GREEN}
        fontFamily={FONT_CODE}
        fontSize={8}
        textColor={GREEN}
        textOpacity={0.5}
        top={280}
        opacity={testsOpacity}
      />

      {/* Grounding section */}
      <SectionBlock
        lines={GROUNDING_LINES}
        label="grounding"
        accentColor={CODE_MUTED}
        fontFamily={FONT_CODE}
        fontSize={8}
        textColor={CODE_MUTED}
        textOpacity={0.3}
        top={500}
        opacity={groundingOpacity}
      />

      {/* Token count */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          bottom: 38,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 11,
          color: BLUE,
          opacity: tokenOpacity * 0.5,
        }}
      >
        2,300 tokens
      </div>

      {/* Quality note */}
      <div
        style={{
          position: "absolute",
          left: WINDOW_X,
          bottom: 22,
          width: WINDOW_WIDTH,
          textAlign: "center",
          fontFamily: FONT_UI,
          fontSize: 10,
          color: GREEN,
          opacity: tokenOpacity * 0.5,
        }}
      >
        100% author-curated
      </div>
    </div>
  );
};

export default RightPanel;
