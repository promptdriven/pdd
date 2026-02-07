import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, ColdOpenSectionPropsType } from "./constants";
import { ColdOpenSplitScreen, defaultColdOpenProps } from "../01-ColdOpen";

export const ColdOpenSection: React.FC<ColdOpenSectionPropsType> = () => {
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {
    if (frame >= VISUAL_SEQUENCE[i].start) {
      activeVisual = i;
      break;
    }
  }

  return (
    <AbsoluteFill style={{ backgroundColor: "#0a0a1a" }}>
      {/* Narration audio */}
      <Audio src={staticFile("cold_open_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: ColdOpenSplitScreen - If you use Cursor, Claude Code, Copilot, getting g */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <ColdOpenSplitScreen {...defaultColdOpenProps} />
        </Sequence>
      )}

      {/* Visual 1: ColdOpenSplitScreen - Great-grandmother figured out sixty years ago */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <ColdOpenSplitScreen {...defaultColdOpenProps} />
        </Sequence>
      )}

      {/* Visual 2: ColdOpenSplitScreen - When socks got cheap enough she stopped */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <ColdOpenSplitScreen {...defaultColdOpenProps} />
        </Sequence>
      )}

      {/* Visual 3: ColdOpenSplitScreen - Code just got that cheap */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <ColdOpenSplitScreen {...defaultColdOpenProps} />
        </Sequence>
      )}

      {/* Visual 4: ColdOpenSplitScreen - So why are we still patching */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <ColdOpenSplitScreen {...defaultColdOpenProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
