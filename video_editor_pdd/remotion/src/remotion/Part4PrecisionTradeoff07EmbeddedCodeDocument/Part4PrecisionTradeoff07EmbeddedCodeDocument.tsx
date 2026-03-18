import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import {
  BG_COLOR,
  DURATION_FRAMES,
  EDITOR_Y,
  CONTENT_START_Y,
  LINE_HEIGHT,
  NATURAL_LANGUAGE_1,
  CODE_LINES,
  NATURAL_LANGUAGE_2,
  LABEL_NL_COLOR,
  LABEL_CODE_COLOR,
  NL1_TYPE_END,
  CODE_TYPE_END,
  NL2_TYPE_END,
  LABELS_PULSE_START,
  LABELS_PULSE_END,
  TITLE_BAR_HEIGHT,
} from "./constants";
import { EditorWindow } from "./EditorWindow";
import { BracketLabel } from "./BracketLabel";
import { FloatingAnnotation } from "./FloatingAnnotation";

export const defaultPart4PrecisionTradeoff07EmbeddedCodeDocumentProps = {};

// Calculate absolute Y positions for bracket labels
// These are relative to the AbsoluteFill (the whole canvas)
const editorContentTop = EDITOR_Y + TITLE_BAR_HEIGHT + 12; // 12px padding
const nl1Top = editorContentTop + CONTENT_START_Y;
const nl1Bottom = nl1Top + NATURAL_LANGUAGE_1.length * LINE_HEIGHT;
const codeTop = nl1Bottom;
const codeBottom = codeTop + CODE_LINES.length * LINE_HEIGHT;
const nl2Top = codeBottom;
const nl2Bottom = nl2Top + NATURAL_LANGUAGE_2.length * LINE_HEIGHT;

export const Part4PrecisionTradeoff07EmbeddedCodeDocument: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Editor window with all typed content */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <EditorWindow />
      </Sequence>

      {/* Section label: Intent (natural language) */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <BracketLabel
          text="Intent (natural language)"
          color={LABEL_NL_COLOR}
          opacity={0.5}
          yTop={nl1Top}
          yBottom={nl1Bottom}
          x={1400}
          appearFrame={NL1_TYPE_END}
          drawDuration={20}
          pulseStart={LABELS_PULSE_START}
          pulseEnd={LABELS_PULSE_END}
        />
      </Sequence>

      {/* Section label: Critical algorithm (code) */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <BracketLabel
          text="Critical algorithm (code)"
          color={LABEL_CODE_COLOR}
          opacity={0.5}
          yTop={codeTop}
          yBottom={codeBottom}
          x={1400}
          appearFrame={CODE_TYPE_END}
          drawDuration={20}
          pulseStart={LABELS_PULSE_START}
          pulseEnd={LABELS_PULSE_END}
        />
      </Sequence>

      {/* Section label: Constraints (natural language) */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <BracketLabel
          text="Constraints (natural language)"
          color={LABEL_NL_COLOR}
          opacity={0.5}
          yTop={nl2Top}
          yBottom={nl2Bottom}
          x={1400}
          appearFrame={NL2_TYPE_END}
          drawDuration={20}
          pulseStart={LABELS_PULSE_START}
          pulseEnd={LABELS_PULSE_END}
        />
      </Sequence>

      {/* Floating annotation */}
      <Sequence from={0} durationInFrames={DURATION_FRAMES}>
        <FloatingAnnotation />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part4PrecisionTradeoff07EmbeddedCodeDocument;
