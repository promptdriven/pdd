import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";

import { BEATS, VISUAL_SEQUENCE, Part2ParadigmShiftPropsType } from "./constants";
import { Part2ParadigmShiftMain } from "../part2_paradigm_shift_main";

export const Part2ParadigmShift: React.FC<Part2ParadigmShiftPropsType> = () => {
  const frame = useCurrentFrame();

  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      <Audio src={staticFile("part2_paradigm_shift_narration.wav")} />

      {/* Visual 0: Part2ParadigmShiftMain */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START}>
          <Part2ParadigmShiftMain />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
