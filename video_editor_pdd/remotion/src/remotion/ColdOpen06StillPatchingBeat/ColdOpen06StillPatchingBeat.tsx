import React from "react";
import { AbsoluteFill } from "remotion";
import { BG_COLOR } from "./constants";
import { CodeUnderlay } from "./CodeUnderlay";
import { QuestionText } from "./QuestionText";
import { AccentLine } from "./AccentLine";

export const defaultColdOpen06StillPatchingBeatProps = {};

/**
 * Section 0.6 — "So why are we still patching?"
 *
 * A deliberate stillness beat. The clean regenerated code from the previous
 * shot dims to near-invisible, and a single question fades in at center.
 * The question hangs — no animation beyond the initial fade. This is the
 * pivot moment of the cold open.
 *
 * Timeline (150 frames @ 30fps = 5s):
 *   0-30:  Code underlay dims from visible to 0.08 opacity
 *  30-60:  Question text fades in
 *  75-90:  Accent line draws from center outward
 *  90-150: Hold — complete stillness
 */
export const ColdOpen06StillPatchingBeat: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Dimmed code underlay from previous shot */}
      <CodeUnderlay />

      {/* Question text: "So why are we still patching?" */}
      <QuestionText />

      {/* Thin accent line beneath the question */}
      <AccentLine />
    </AbsoluteFill>
  );
};

export default ColdOpen06StillPatchingBeat;
