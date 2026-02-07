import React from "react";
import {
  AbsoluteFill,
  Audio,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { BEATS, VISUAL_SEQUENCE, Part2ParadigmShiftPropsType } from "./constants";
import { MoldToPrompt, defaultMoldToPromptProps } from "../19-MoldToPrompt";
import { PartsEject, defaultPartsEjectProps } from "../14-PartsEject";
import { PerfectParts, defaultPerfectPartsProps } from "../16-PerfectParts";
import { PlasticRegenerates, defaultPlasticRegeneratesProps } from "../18-PlasticRegenerates";
import { PromptGeneratesCode, defaultPromptGeneratesCodeProps } from "../20-PromptGeneratesCode";
import { ValueAura, defaultValueAuraProps } from "../17-ValueAura";

export const Part2ParadigmShift: React.FC<Part2ParadigmShiftPropsType> = () => {
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
      <Audio src={staticFile("part2_paradigm_shift_narration.wav")} />

      {/* Visual compositions sequenced by BEATS */}
      
      {/* Visual 0: Veo clip - Pattern across industries, deeper shift in how thi */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("01_factory_floor.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: Veo clip - Consider injection molding, crafted to designed mo */}
      {activeVisual === 1 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("02_mold_closeup.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 2: PartsEject - Make mold once, unlimited parts, refine once all i */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <PartsEject {...defaultPartsEjectProps} />
        </Sequence>
      )}

      {/* Visual 3: Veo clip - When there's a defect, don't patch individual part */}
      {activeVisual === 3 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("veo_defect_discovered.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 4: PerfectParts - Fix the mold, fix applies to every future part */}
      {activeVisual === 4 && (
        <Sequence from={BEATS.VISUAL_04_START} durationInFrames={BEATS.VISUAL_04_END - BEATS.VISUAL_04_START}>
          <PerfectParts {...defaultPerfectPartsProps} />
        </Sequence>
      )}

      {/* Visual 5: ValueAura - Real shift: migration of where value lives */}
      {activeVisual === 5 && (
        <Sequence from={BEATS.VISUAL_05_START} durationInFrames={BEATS.VISUAL_05_END - BEATS.VISUAL_05_START}>
          <ValueAura {...defaultValueAuraProps} />
        </Sequence>
      )}

      {/* Visual 6: PlasticRegenerates - Molding value in specification, disposable, regene */}
      {activeVisual === 6 && (
        <Sequence from={BEATS.VISUAL_06_START} durationInFrames={BEATS.VISUAL_06_END - BEATS.VISUAL_06_START}>
          <PlasticRegenerates {...defaultPlasticRegeneratesProps} />
        </Sequence>
      )}

      {/* Visual 7: Veo clip - Not just plastics, chip industry hit this exact wa */}
      {activeVisual === 7 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_craftsman_vs_mold.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 8: MoldToPrompt - 1980s drew gates by hand, moved to Verilog in 1985 */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}

      {/* Visual 9: MoldToPrompt - Synthesis non-deterministic, different gates every */}
      {activeVisual === 9 && (
        <Sequence from={BEATS.VISUAL_09_START} durationInFrames={BEATS.VISUAL_09_END - BEATS.VISUAL_09_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}

      {/* Visual 10: MoldToPrompt - Synopsys wrapped verification, SAT/SMT proof, same */}
      {activeVisual === 10 && (
        <Sequence from={BEATS.VISUAL_10_START} durationInFrames={BEATS.VISUAL_10_END - BEATS.VISUAL_10_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}

      {/* Visual 11: MoldToPrompt - By 1990 schematic, mid-90s half switched, all use  */}
      {activeVisual === 11 && (
        <Sequence from={BEATS.VISUAL_11_START} durationInFrames={BEATS.VISUAL_11_END - BEATS.VISUAL_11_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}

      {/* Visual 12: PromptGeneratesCode - Same transition for software, prompt is mold, test */}
      {activeVisual === 12 && (
        <Sequence from={BEATS.VISUAL_12_START} durationInFrames={BEATS.VISUAL_12_END - BEATS.VISUAL_12_START}>
          <PromptGeneratesCode {...defaultPromptGeneratesCodeProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
