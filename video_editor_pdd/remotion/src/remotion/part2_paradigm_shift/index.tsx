import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part2ParadigmShift01SectionTitleCard } from "../Part2ParadigmShift01SectionTitleCard";
import { Part2ParadigmShift04DefectFixTheMold } from "../Part2ParadigmShift04DefectFixTheMold";
import { Part2ParadigmShift05ValueMigrationSplit } from "../Part2ParadigmShift05ValueMigrationSplit";
import { Part2ParadigmShift07VerilogSynthesisTriple } from "../Part2ParadigmShift07VerilogSynthesisTriple";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "../Part2ParadigmShift08SynopsysPddEquivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "../Part2ParadigmShift09AbstractionStaircase";
import { Part2ParadigmShift10NetlistZoomUnreviewable } from "../Part2ParadigmShift10NetlistZoomUnreviewable";
import { Part2ParadigmShift11PromptReplacesReview } from "../Part2ParadigmShift11PromptReplacesReview";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part2ParadigmShift01SectionTitleCard,
  "04_defect_fix_the_mold": Part2ParadigmShift04DefectFixTheMold,
  "05_value_migration_split": Part2ParadigmShift05ValueMigrationSplit,
  "07_verilog_synthesis_triple": Part2ParadigmShift07VerilogSynthesisTriple,
  "08_synopsys_pdd_equivalence": Part2ParadigmShift08SynopsysPddEquivalence,
  "09_abstraction_staircase": Part2ParadigmShift09AbstractionStaircase,
  "10_netlist_zoom_unreviewable": Part2ParadigmShift10NetlistZoomUnreviewable,
  "11_prompt_replaces_review": Part2ParadigmShift11PromptReplacesReview,
};

const VISUAL_DURATIONS: Record<string, number> = {
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "02_factory_floor_intro": { defaultSrc: "veo/factory_floor_intro.mp4", backgroundSrc: "veo/factory_floor_intro.mp4", outputSrc: "veo/factory_floor_intro.mp4", baseSrc: "veo/factory_floor_intro.mp4" },
  "03_injection_molding_process": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "04_defect_fix_the_mold": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "05_value_migration_split": { defaultSrc: "veo/injection_molding_process.mp4", backgroundSrc: "veo/injection_molding_process.mp4", outputSrc: "veo/injection_molding_process.mp4", baseSrc: "veo/injection_molding_process.mp4" },
  "06_chip_design_history": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "07_verilog_synthesis_triple": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "08_synopsys_pdd_equivalence": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "09_abstraction_staircase": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "10_netlist_zoom_unreviewable": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
  "11_prompt_replaces_review": { defaultSrc: "veo/chip_design_1980s_lab.mp4", backgroundSrc: "veo/chip_design_1980s_lab.mp4", outputSrc: "veo/chip_design_1980s_lab.mp4", baseSrc: "veo/chip_design_1980s_lab.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_factory_floor_intro": {"specBaseName": "02_factory_floor_intro", "dataPoints": null, "overlayConfig": null},
  "03_injection_molding_process": {"specBaseName": "03_injection_molding_process", "dataPoints": null, "overlayConfig": null},
  "04_defect_fix_the_mold": {"specBaseName": "04_defect_fix_the_mold", "dataPoints": null, "overlayConfig": null},
  "05_value_migration_split": {"specBaseName": "05_value_migration_split", "dataPoints": null, "overlayConfig": null},
  "06_chip_design_history": {"specBaseName": "06_chip_design_history", "dataPoints": null, "overlayConfig": null},
  "07_verilog_synthesis_triple": {"specBaseName": "07_verilog_synthesis_triple", "dataPoints": null, "overlayConfig": null},
  "08_synopsys_pdd_equivalence": {"specBaseName": "08_synopsys_pdd_equivalence", "dataPoints": null, "overlayConfig": null},
  "09_abstraction_staircase": {"specBaseName": "09_abstraction_staircase", "dataPoints": null, "overlayConfig": null},
  "10_netlist_zoom_unreviewable": {"specBaseName": "10_netlist_zoom_unreviewable", "dataPoints": null, "overlayConfig": null},
  "11_prompt_replaces_review": {"specBaseName": "11_prompt_replaces_review", "dataPoints": null, "overlayConfig": null},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 228.117333;
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
