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
import { DefectDiscovered, defaultDefectDiscoveredProps } from "../15-DefectDiscovered";
import { MoldToPrompt, defaultMoldToPromptProps } from "../19-MoldToPrompt";
import { PartsEject, defaultPartsEjectProps } from "../14-PartsEject";
import { PerfectParts, defaultPerfectPartsProps } from "../16-PerfectParts";
import { PlasticRegenerates, defaultPlasticRegeneratesProps } from "../18-PlasticRegenerates";
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
      
      {/* Visual 0: Veo clip - What changed with clothes, paradigm shift */}
      {activeVisual === 0 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("01_factory_floor.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 1: Veo clip - Manufacturing: crafting to designing molds */}
      {activeVisual === 1 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("02_mold_closeup.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 2: PartsEject - Make mold once, unlimited identical parts */}
      {activeVisual === 2 && (
        <Sequence from={BEATS.VISUAL_02_START} durationInFrames={BEATS.VISUAL_02_END - BEATS.VISUAL_02_START}>
          <PartsEject {...defaultPartsEjectProps} />
        </Sequence>
      )}

      {/* Visual 3: DefectDiscovered - Defect: don't patch parts */}
      {activeVisual === 3 && (
        <Sequence from={BEATS.VISUAL_03_START} durationInFrames={BEATS.VISUAL_03_END - BEATS.VISUAL_03_START}>
          <DefectDiscovered {...defaultDefectDiscoveredProps} />
        </Sequence>
      )}

      {/* Visual 4: PerfectParts - Fix the mold, applies to every future part */}
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

      {/* Visual 6: Veo clip - Crafting: value in object, protect it */}
      {activeVisual === 6 && (
        <AbsoluteFill>
          <OffthreadVideo
            src={staticFile("07_craftsman_vs_mold.mp4")}
            style={{ width: "100%", height: "100%" }}
          />
        </AbsoluteFill>
      )}

      {/* Visual 7: PlasticRegenerates - Molding: value in specification, disposable */}
      {activeVisual === 7 && (
        <Sequence from={BEATS.VISUAL_07_START} durationInFrames={BEATS.VISUAL_07_END - BEATS.VISUAL_07_START}>
          <PlasticRegenerates {...defaultPlasticRegeneratesProps} />
        </Sequence>
      )}

      {/* Visual 8: MoldToPrompt - This is PDD: prompt is mold, code is plastic */}
      {activeVisual === 8 && (
        <Sequence from={BEATS.VISUAL_08_START} durationInFrames={BEATS.VISUAL_08_END - BEATS.VISUAL_08_START}>
          <MoldToPrompt {...defaultMoldToPromptProps} />
        </Sequence>
      )}
    </AbsoluteFill>
  );
};
