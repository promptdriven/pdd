import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part2ParadigmShift08SynopsysPddEquivalence } from "../Part2ParadigmShift08SynopsysPddEquivalence";
import { Part2ParadigmShift09AbstractionStaircase } from "../Part2ParadigmShift09AbstractionStaircase";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "11_synopsys_pdd_equivalence": Part2ParadigmShift08SynopsysPddEquivalence,
  "12_abstraction_staircase": Part2ParadigmShift09AbstractionStaircase,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "11_synopsys_pdd_equivalence": 1140,
  "12_abstraction_staircase": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "02_factory_floor_wide": { defaultSrc: "veo/factory_floor_wide.mp4", backgroundSrc: "veo/factory_floor_wide.mp4", outputSrc: "veo/factory_floor_wide.mp4", baseSrc: "veo/factory_floor_wide.mp4" },
  "03_injection_molding_closeup": { defaultSrc: "veo/injection_molding_closeup.mp4", backgroundSrc: "veo/injection_molding_closeup.mp4", outputSrc: "veo/injection_molding_closeup.mp4", baseSrc: "veo/injection_molding_closeup.mp4" },
  "05_defect_and_mold_fix": { defaultSrc: "veo/defect_mold_fix.mp4", backgroundSrc: "veo/defect_mold_fix.mp4", outputSrc: "veo/defect_mold_fix.mp4", baseSrc: "veo/defect_mold_fix.mp4" },
  "06_split_craftsman_vs_mold": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
  "07_craftsman_carving": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
  "08_mold_producing_parts": { defaultSrc: "veo/mold_producing_parts.mp4", backgroundSrc: "veo/mold_producing_parts.mp4", outputSrc: "veo/mold_producing_parts.mp4", baseSrc: "veo/mold_producing_parts.mp4" },
  "09_1980s_chip_lab": { defaultSrc: "veo/1980s_chip_lab.mp4", backgroundSrc: "veo/1980s_chip_lab.mp4", outputSrc: "veo/1980s_chip_lab.mp4", baseSrc: "veo/1980s_chip_lab.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 60 },
  "10_verilog_synthesis_triple": { fadeInFrames: 120 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_silhouette", "color": "#8B5CF6", "role": "injection_mold_preview"}], "narrationSegments": ["part2_paradigm_shift_001", "part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "02_factory_floor_wide": {"specBaseName": "02_factory_floor_wide", "dataPoints": {"type": "veo_clip", "clipId": "factory_floor_wide", "durationSeconds": 10}, "mediaAliases": {"defaultSrc": "veo/factory_floor_wide.mp4", "backgroundSrc": "veo/factory_floor_wide.mp4", "outputSrc": "veo/factory_floor_wide.mp4", "baseSrc": "veo/factory_floor_wide.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_injection_molding_closeup": {"specBaseName": "03_injection_molding_closeup", "dataPoints": {"type": "veo_clip", "clipId": "injection_molding_closeup", "durationSeconds": 8}, "mediaAliases": {"defaultSrc": "veo/injection_molding_closeup.mp4", "backgroundSrc": "veo/injection_molding_closeup.mp4", "outputSrc": "veo/injection_molding_closeup.mp4", "baseSrc": "veo/injection_molding_closeup.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_mold_production_counter": {"specBaseName": "04_mold_production_counter", "dataPoints": {"type": "animated_infographic", "elements": [{"id": "mold", "shape": "cross_section", "color": "#64748B", "role": "constant_specification"}, {"id": "parts", "shape": "rounded_rect", "color": "#D9944A", "role": "generated_output"}, {"id": "counter", "values": [1, 10, 100, 1000, 10000], "role": "scale_indicator"}, {"id": "defect", "color": "#EF4444", "role": "flaw_transition"}], "narrationSegments": ["part2_paradigm_shift_007", "part2_paradigm_shift_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_defect_and_mold_fix": {"specBaseName": "05_defect_and_mold_fix", "dataPoints": {"type": "veo_clip", "clipId": "defect_mold_fix", "durationSeconds": 7, "characters": [{"id": "factory_engineer", "label": "Factory Engineer", "referencePrompt": "An engineer in a clean grey work shirt, mid-40s, steady hands, working at a well-lit industrial workbench with precision tools and machined steel molds."}]}, "mediaAliases": {"defaultSrc": "veo/defect_mold_fix.mp4", "backgroundSrc": "veo/defect_mold_fix.mp4", "outputSrc": "veo/defect_mold_fix.mp4", "baseSrc": "veo/defect_mold_fix.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_split_craftsman_vs_mold": {"specBaseName": "06_split_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.6}, "panels": {"left": {"clips": ["craftsman_carving"], "aura": {"color": "#F59E0B", "target": "chair", "appearsAt": 8.0}, "label": "Value in the object"}, "right": {"clips": ["mold_producing_parts"], "aura": {"color": "#4A90D9", "target": "mold", "appearsAt": 12.0}, "label": "Value in the specification"}}, "narrationSegments": ["part2_paradigm_shift_010", "part2_paradigm_shift_011", "part2_paradigm_shift_012"], "durationSeconds": 25.0}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "07_craftsman_carving": {"specBaseName": "07_craftsman_carving", "dataPoints": {"type": "veo_clip", "clipId": "craftsman_carving", "durationSeconds": 25, "characters": [{"id": "craftsman", "label": "Woodworking Craftsman", "referencePrompt": "A craftsman in his 50s wearing a leather apron over a flannel shirt, working in a warm wood-filled workshop with natural window light and an overhead lamp. Weathered hands, focused expression."}]}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_mold_producing_parts": {"specBaseName": "08_mold_producing_parts", "dataPoints": {"type": "veo_clip", "clipId": "mold_producing_parts", "durationSeconds": 25}, "mediaAliases": {"defaultSrc": "veo/mold_producing_parts.mp4", "backgroundSrc": "veo/mold_producing_parts.mp4", "outputSrc": "veo/mold_producing_parts.mp4", "baseSrc": "veo/mold_producing_parts.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_1980s_chip_lab": {"specBaseName": "09_1980s_chip_lab", "dataPoints": {"type": "veo_clip", "clipId": "1980s_chip_lab", "durationSeconds": 7, "characters": [{"id": "chip_engineer_1980s", "label": "1980s Chip Engineer", "referencePrompt": "A chip design engineer in his 30s wearing a short-sleeve dress shirt, hunched over a large drafting desk in a 1980s electronics lab. Technical pen in hand, surrounded by datasheets and analog instruments."}]}, "mediaAliases": {"defaultSrc": "veo/1980s_chip_lab.mp4", "backgroundSrc": "veo/1980s_chip_lab.mp4", "outputSrc": "veo/1980s_chip_lab.mp4", "baseSrc": "veo/1980s_chip_lab.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_verilog_synthesis_triple": {"specBaseName": "10_verilog_synthesis_triple", "dataPoints": {"type": "animated_infographic", "phases": [{"id": "schematic_to_verilog", "description": "Hand-drawn schematic dissolves into Verilog code", "frames": [0, 240]}, {"id": "triple_synthesis", "description": "Same Verilog synthesized three times, producing three different netlists", "frames": [240, 690], "netlists": ["clustered", "grid", "radial"]}, {"id": "equivalence_check", "description": "Green checkmarks confirm all three are functionally equivalent", "frames": [690, 1080], "checkColor": "#10B981"}], "narrationSegments": ["part2_paradigm_shift_014", "part2_paradigm_shift_015"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 120}, "renderMode": "generated-media"},
  "11_synopsys_pdd_equivalence": {"specBaseName": "11_synopsys_pdd_equivalence", "dataPoints": {"type": "animated_infographic", "phases": [{"id": "verification_flow", "description": "Flow diagram: Verilog → Synthesis → Netlist → Formal Verification", "frames": [0, 600], "keyInsight": {"different": "The gates were different every time.", "same": "The function was the same every time."}}, {"id": "synopsys_pdd_parallel", "description": "Side-by-side comparison of Synopsys and PDD pipelines", "frames": [600, 1140], "morphs": [{"from": "Verilog", "to": "PROMPT", "colorFrom": "#C678DD", "colorTo": "#8B5CF6"}, {"from": "Gate netlist", "to": "Software code", "colorFrom": "#10B981", "colorTo": "#61AFEF"}, {"from": "Synopsys checkmark", "to": "Test suite", "colorFrom": "#10B981", "colorTo": "#10B981"}]}], "narrationSegments": ["part2_paradigm_shift_016", "part2_paradigm_shift_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_abstraction_staircase": {"specBaseName": "12_abstraction_staircase", "dataPoints": {"type": "animated_timeline", "layout": "ascending_staircase", "steps": [{"label": "Transistors", "decade": "1970s", "color": "#D9944A"}, {"label": "Schematics", "decade": "1980s", "color": "#E97B2C"}, {"label": "RTL / Verilog", "decade": "1990s", "color": "#4A90D9"}, {"label": "Behavioral / HLS", "decade": "2010s", "color": "#14B8A6"}, {"label": "Natural Language → Code", "decade": "2020s", "color": "#8B5CF6", "pulsing": true}], "transitionArrows": {"label": "Couldn't scale", "color": "#EF4444"}, "narrationSegments": ["part2_paradigm_shift_018"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_billion_gate_unreviewable": {"specBaseName": "13_billion_gate_unreviewable", "dataPoints": {"type": "animated_infographic", "phases": [{"id": "overwhelming_scale", "description": "Billions of gates and massive code diffs — unreviewable", "frames": [0, 210], "elements": ["gate_grid", "code_diff_scroll"]}, {"id": "prompt_and_tests", "description": "Clean prompt document + verified test suite — reviewable", "frames": [210, 390], "prompt": {"label": "PROMPT", "color": "#8B5CF6", "lineCount": 5}, "tests": {"label": "TESTS", "color": "#10B981", "items": ["test_handles_null_input", "test_validates_schema", "test_returns_correct_type", "test_edge_case_empty", "test_performance_under_load"]}, "bottomLabel": "Review the spec. Verify the output."}], "narrationSegments": ["part2_paradigm_shift_019"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 227.48;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

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
                  <VisualMediaProvider media={visualContract?.renderMode === "component" ? null : visualMedia}>
                    <VisualComponent />
                  </VisualMediaProvider>
                </VisualContractProvider>
              </SlotScaledSequence>
            ) : visualContract?.renderMode === "component" ? (
              <VisualContractProvider contract={visualContract}>
                <VisualMediaProvider media={visualMedia}>
                  <GeneratedContractVisual />
                </VisualMediaProvider>
              </VisualContractProvider>
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
