import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part5CompoundReturnsPropsType } from "./constants";
import { BothGenerateFinal, defaultBothGenerateFinalProps } from "../45-BothGenerateFinal";
import { CrossingPoint, defaultCrossingPointProps } from "../08-CrossingPoint";
import { GraphAnimateCurve, defaultGraphAnimateCurveProps } from "../42-GraphAnimateCurve";
import { ShortPromptTests, defaultShortPromptTestsProps } from "../44-ShortPromptTests";

export const Part5CompoundReturns: React.FC<Part5CompoundReturnsPropsType> = () => {
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
      <Audio src={staticFile("part5_compound_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: GraphAnimateCurve - Let's talk about compound returns */}
      {activeVisual === 0 && (
        <Sequence from={BEATS.VISUAL_00_START} durationInFrames={BEATS.VISUAL_00_END - BEATS.VISUAL_00_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 1: GraphAnimateCurve - Patch code local returns, 1.7x issues, risks more  */}
      {activeVisual === 1 && (
        <Sequence from={BEATS.VISUAL_01_START} durationInFrames={BEATS.VISUAL_01_END - BEATS.VISUAL_01_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 2: GraphAnimateCurve - Returns linear at best, cost compounding, 1.52T an */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <GraphAnimateCurve {...defaultGraphAnimateCurveProps} />
        </Sequence>
      )}

      {/* Visual 3: ShortPromptTests - PDD test returns compound, constrains future, perm */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <ShortPromptTests {...defaultShortPromptTestsProps} />
        </Sequence>
      )}

      {/* Visual 4: BothGenerateFinal - Every mold investment compounds, patching diminish */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <BothGenerateFinal {...defaultBothGenerateFinalProps} />
        </Sequence>
      )}

      {/* Visual 5: Veo clip - Great-grandmother rational for darning, economics  */}
      {activeVisual === 5 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 6: Veo clip - Not stupid for patching, economics made it rationa */}
      {activeVisual === 6 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_split_screen_sepia.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 7: CrossingPoint - Economics changed, rational becomes darning socks */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <CrossingPoint {...defaultCrossingPointProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
