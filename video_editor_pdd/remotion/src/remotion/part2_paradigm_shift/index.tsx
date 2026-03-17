import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part2ParadigmShiftMain } from "../part2_paradigm_shift_main";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "part2_paradigm_shift_main": Part2ParadigmShiftMain,
};

const VISUAL_DURATIONS: Record<string, number> = {
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "02_factory_floor_intro": { defaultSrc: "veo/factory_floor_intro.mp4", backgroundSrc: "veo/factory_floor_intro.mp4", outputSrc: "veo/factory_floor_intro.mp4", baseSrc: "veo/factory_floor_intro.mp4" },
  "03_injection_molding_process": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "06_chip_design_history": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "part2_paradigm_shift_main": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "02_factory_floor_intro": {"specBaseName": "02_factory_floor_intro", "dataPoints": null, "overlayConfig": null},
  "03_injection_molding_process": {"specBaseName": "03_injection_molding_process", "dataPoints": null, "overlayConfig": null},
  "06_chip_design_history": {"specBaseName": "06_chip_design_history", "dataPoints": null, "overlayConfig": null},
  "part2_paradigm_shift_main": {"specBaseName": "main", "dataPoints": null, "overlayConfig": null},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 228.053292;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
      {activeVisuals.map((visual) => {
        const VisualComponent = COMPONENT_MAP[visual.id] ?? null;
        const visualDuration = Math.max(1, visual.end - visual.start);
        const intrinsicDurationInFrames = VISUAL_DURATIONS[visual.id] ?? visualDuration;
        const visualMedia = VISUAL_MEDIA[visual.id] ?? null;
        const visualOverlayConfig = VISUAL_OVERLAYS[visual.id] ?? null;
        const visualContract = VISUAL_CONTRACTS[visual.id] ?? null;

        return (
          <Sequence key={visual.id} from={visual.start} durationInFrames={visualDuration}>
            {VisualComponent ? (
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualMedia}>
                    <VisualComponent />
                  </VisualMediaProvider>
                </VisualContractProvider>
              </SlotScaledSequence>
            ) : visualMedia?.defaultSrc ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                </VisualMediaProvider>
              </VisualContractProvider>
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part2ParadigmShiftSection;
