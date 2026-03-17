import React from "react";
import { AbsoluteFill } from "remotion";
import { CodeUnderlay } from "./CodeUnderlay";
import { QuestionFadeOut } from "./QuestionFadeOut";
import { TitleLine } from "./TitleLine";
import { HorizontalRule } from "./HorizontalRule";
import { Subtitle } from "./Subtitle";
import { TerminalBreadcrumb } from "./TerminalBreadcrumb";
import {
  BG_COLOR,
  TITLE_LINE1_TEXT,
  TITLE_LINE1_Y,
  TITLE_LINE1_START_FRAME,
  TITLE_LINE1_ANIM_DURATION,
  TITLE_LINE2_TEXT,
  TITLE_LINE2_Y,
  TITLE_LINE2_START_FRAME,
  TITLE_LINE2_ANIM_DURATION,
} from "./constants";

export const defaultColdOpen07PddTitleCardProps = {};

/**
 * Section 0.7: PDD Title Card — The Promise
 *
 * The question from the previous shot dissolves, and the answer materializes:
 * "Prompt-Driven Development" fades in as a clean, authoritative title card
 * over a dimmed code background. Below it, the thesis statement appears:
 * "Writing the mold, not the plastic."
 *
 * Timeline (150 frames / 5s @ 30fps):
 *   0-20:   Question fades out, code underlay dims 0.08 → 0.04
 *   20-45:  "Prompt-Driven" slides up + fades in
 *   50-60:  Horizontal rule draws from center outward
 *   60-85:  "Development" slides up + fades in
 *   80-100: Subtitle + terminal breadcrumb fade in
 *   100-150: Hold — glow pulses gently
 */
export const ColdOpen07PddTitleCard: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      <CodeUnderlay />
      <QuestionFadeOut />
      <TitleLine
        text={TITLE_LINE1_TEXT}
        y={TITLE_LINE1_Y}
        startFrame={TITLE_LINE1_START_FRAME}
        animDuration={TITLE_LINE1_ANIM_DURATION}
      />
      <HorizontalRule />
      <TitleLine
        text={TITLE_LINE2_TEXT}
        y={TITLE_LINE2_Y}
        startFrame={TITLE_LINE2_START_FRAME}
        animDuration={TITLE_LINE2_ANIM_DURATION}
      />
      <Subtitle />
      <TerminalBreadcrumb />
    </AbsoluteFill>
  );
};

export default ColdOpen07PddTitleCard;
