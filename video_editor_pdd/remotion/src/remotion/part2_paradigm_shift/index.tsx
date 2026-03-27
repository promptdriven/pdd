import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part2ParadigmShift07VerilogSynthesisTriple } from "../Part2ParadigmShift07VerilogSynthesisTriple";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "12_verilog_synthesis": Part2ParadigmShift07VerilogSynthesisTriple,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "12_verilog_synthesis": 540,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "02_factory_floor_wide": { defaultSrc: "veo/factory_floor_wide.mp4", backgroundSrc: "veo/factory_floor_wide.mp4", outputSrc: "veo/factory_floor_wide.mp4", baseSrc: "veo/factory_floor_wide.mp4" },
  "03_injection_molding_closeup": { defaultSrc: "veo/injection_molding_closeup.mp4", backgroundSrc: "veo/injection_molding_closeup.mp4", outputSrc: "veo/injection_molding_closeup.mp4", baseSrc: "veo/injection_molding_closeup.mp4" },
  "05_defect_and_mold_fix": { defaultSrc: "veo/defect_and_mold_fix.mp4", backgroundSrc: "veo/defect_and_mold_fix.mp4", outputSrc: "veo/defect_and_mold_fix.mp4", baseSrc: "veo/defect_and_mold_fix.mp4" },
  "06_new_parts_eject": { defaultSrc: "veo/new_parts_eject.mp4", backgroundSrc: "veo/new_parts_eject.mp4", outputSrc: "veo/new_parts_eject.mp4", baseSrc: "veo/new_parts_eject.mp4" },
  "07_split_craftsman_vs_mold": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
  "08_veo_craftsman_carving": { defaultSrc: "veo/craftsman_carving.mp4", backgroundSrc: "veo/craftsman_carving.mp4", outputSrc: "veo/craftsman_carving.mp4", baseSrc: "veo/craftsman_carving.mp4" },
  "09_veo_mold_plastic_flow": { defaultSrc: "veo/mold_plastic_flow.mp4", backgroundSrc: "veo/mold_plastic_flow.mp4", outputSrc: "veo/mold_plastic_flow.mp4", baseSrc: "veo/mold_plastic_flow.mp4" },
  "10_veo_1980s_chip_lab": { defaultSrc: "veo/1980s_chip_lab.mp4", backgroundSrc: "veo/1980s_chip_lab.mp4", outputSrc: "veo/1980s_chip_lab.mp4", baseSrc: "veo/1980s_chip_lab.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 90 },
  "13_triple_synthesis_equivalence": { fadeInFrames: 120 },
  "14_synopsys_pdd_equivalence": { fadeOutFrames: 60 },
  "15_abstraction_staircase": { fadeOutFrames: 60 },
  "18_prompt_mold_finale": { fadeOutFrames: 60 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_silhouette", "colors": ["#4A90D9", "#D9944A"], "role": "injection_mold_preview"}], "narrationSegments": ["part2_paradigm_shift_001", "part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004", "part2_paradigm_shift_005"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 90}, "renderMode": "component"},
  "02_factory_floor_wide": {"specBaseName": "02_factory_floor_wide", "dataPoints": {"type": "veo_clip", "clipId": "factory_floor_wide", "durationSeconds": 10}, "mediaAliases": {"defaultSrc": "veo/factory_floor_wide.mp4", "backgroundSrc": "veo/factory_floor_wide.mp4", "outputSrc": "veo/factory_floor_wide.mp4", "baseSrc": "veo/factory_floor_wide.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_injection_molding_closeup": {"specBaseName": "03_injection_molding_closeup", "dataPoints": {"type": "veo_clip", "clipId": "injection_molding_closeup", "durationSeconds": 10}, "mediaAliases": {"defaultSrc": "veo/injection_molding_closeup.mp4", "backgroundSrc": "veo/injection_molding_closeup.mp4", "outputSrc": "veo/injection_molding_closeup.mp4", "baseSrc": "veo/injection_molding_closeup.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_mold_production_counter": {"specBaseName": "04_mold_production_counter", "dataPoints": {"type": "counter_animation", "chartId": "mold_production_counter", "counter": {"start": 1, "end": 10000, "milestones": [1, 10, 100, 1000, 10000], "easing": "exponential"}, "moldCycle": {"startFramesPerCycle": 60, "endFramesPerCycle": 6}, "narrationSegments": ["part2_paradigm_shift_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_defect_and_mold_fix": {"specBaseName": "05_defect_and_mold_fix", "dataPoints": {"type": "veo_clip", "clipId": "defect_and_mold_fix", "durationSeconds": 9, "characters": [{"id": "manufacturing_engineer", "label": "Manufacturing Engineer", "referencePrompt": "Middle-aged manufacturing engineer in safety glasses and clean work shirt, professional workshop setting"}]}, "mediaAliases": {"defaultSrc": "veo/defect_and_mold_fix.mp4", "backgroundSrc": "veo/defect_and_mold_fix.mp4", "outputSrc": "veo/defect_and_mold_fix.mp4", "baseSrc": "veo/defect_and_mold_fix.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_new_parts_eject": {"specBaseName": "06_new_parts_eject", "dataPoints": {"type": "veo_clip", "clipId": "new_parts_eject", "durationSeconds": 7}, "mediaAliases": {"defaultSrc": "veo/new_parts_eject.mp4", "backgroundSrc": "veo/new_parts_eject.mp4", "outputSrc": "veo/new_parts_eject.mp4", "baseSrc": "veo/new_parts_eject.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_split_craftsman_vs_mold": {"specBaseName": "07_split_craftsman_vs_mold", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.4}, "panels": {"left": {"clips": ["craftsman_carving"], "label": "Craftsman — value in the object", "aura": {"color": "#D9944A", "target": "object"}}, "right": {"clips": ["mold_plastic_flow"], "label": "Mold — value in the specification", "aura": {"color": "#4A90D9", "target": "mold"}, "partDissolve": true}}, "narrationSegments": ["part2_paradigm_shift_009", "part2_paradigm_shift_010"], "durationSeconds": 20.0}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "component"},
  "08_veo_craftsman_carving": {"specBaseName": "08_veo_craftsman_carving", "dataPoints": {"type": "veo_clip", "clipId": "craftsman_carving", "durationSeconds": 20, "characters": [{"id": "craftsman", "label": "Craftsman", "referencePrompt": "Experienced woodworker, middle-aged, work apron, traditional workshop setting with warm lighting"}]}, "mediaAliases": {"defaultSrc": "veo/craftsman_carving.mp4", "backgroundSrc": "veo/craftsman_carving.mp4", "outputSrc": "veo/craftsman_carving.mp4", "baseSrc": "veo/craftsman_carving.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_veo_mold_plastic_flow": {"specBaseName": "09_veo_mold_plastic_flow", "dataPoints": {"type": "veo_clip", "clipId": "mold_plastic_flow", "durationSeconds": 20}, "mediaAliases": {"defaultSrc": "veo/mold_plastic_flow.mp4", "backgroundSrc": "veo/mold_plastic_flow.mp4", "outputSrc": "veo/mold_plastic_flow.mp4", "baseSrc": "veo/mold_plastic_flow.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_veo_1980s_chip_lab": {"specBaseName": "10_veo_1980s_chip_lab", "dataPoints": {"type": "veo_clip", "clipId": "1980s_chip_lab", "durationSeconds": 8, "characters": [{"id": "chip_engineer", "label": "1980s Chip Engineer", "referencePrompt": "Male electronics engineer in button-down shirt, 1980s style, drafting desk with schematics, fluorescent-lit lab"}]}, "mediaAliases": {"defaultSrc": "veo/1980s_chip_lab.mp4", "backgroundSrc": "veo/1980s_chip_lab.mp4", "outputSrc": "veo/1980s_chip_lab.mp4", "baseSrc": "veo/1980s_chip_lab.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "11_schematic_density_zoom": {"specBaseName": "11_schematic_density_zoom", "dataPoints": {"type": "schematic_zoom", "chartId": "schematic_density_zoom", "counter": {"start": 20, "end": 50000, "milestones": [100, 500, 5000, 25000, 50000]}, "zoom": {"startScale": 8, "endScale": 0.1, "easing": "easeInOutCubic"}, "narrationSegments": ["part2_paradigm_shift_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_verilog_synthesis": {"specBaseName": "12_verilog_synthesis", "dataPoints": {"type": "synthesis_animation", "chartId": "verilog_synthesis", "codeLanguage": "verilog", "codeSample": "module counter(\\n  input clk, rst,\\n  output reg [7:0] count\\n);\\n  always @(posedge clk)\\n    if (rst) count <= 0;\\n    else count <= count + 1;\\nendmodule", "synthesisStages": ["code_input", "synthesis_process", "gate_output"], "narrationSegments": ["part2_paradigm_shift_011"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_triple_synthesis_equivalence": {"specBaseName": "13_triple_synthesis_equivalence", "dataPoints": {"type": "equivalence_demo", "chartId": "triple_synthesis_equivalence", "runs": [{"id": "run_1", "topology": "dense-left", "label": "Run 1"}, {"id": "run_2", "topology": "tree-branch", "label": "Run 2"}, {"id": "run_3", "topology": "linear-chain", "label": "Run 3"}], "equivalenceLabel": "Functionally equivalent", "equivalenceColor": "#5AAA6E", "narrationSegments": ["part2_paradigm_shift_012", "part2_paradigm_shift_013"]}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 120}, "renderMode": "generated-media"},
  "14_synopsys_pdd_equivalence": {"specBaseName": "14_synopsys_pdd_equivalence", "dataPoints": {"type": "text_overlay", "chartId": "synopsys_pdd_equivalence", "lines": [{"accent": {"text": "Synopsys:", "color": "#4A90D9"}, "body": "specification in → verified hardware out."}, {"accent": {"text": "PDD:", "color": "#D9944A"}, "body": "prompt in → verified software out."}], "subtitle": "Same architecture.", "equivalenceMappings": [{"from": "specification", "to": "prompt"}, {"from": "hardware", "to": "software"}], "narrationSegments": ["part2_paradigm_shift_014"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "generated-media"},
  "15_abstraction_staircase": {"specBaseName": "15_abstraction_staircase", "dataPoints": {"type": "staircase_timeline", "chartId": "abstraction_staircase", "steps": [{"label": "Transistors", "decade": "1970s", "color": "#D9944A", "level": 1}, {"label": "Schematics", "decade": "1980s", "color": "#D9944A", "level": 2}, {"label": "RTL / Verilog", "decade": "1990s", "color": "#4A90D9", "level": 3}, {"label": "Behavioral / HLS", "decade": "2010s", "color": "#4A90D9", "level": 4}, {"label": "Natural language → Code", "decade": "2020s", "color": "#5AAA6E", "level": 5, "emphasis": true}], "transitionLabel": "Couldn't scale", "transitionColor": "#EF4444", "narrationSegments": ["part2_paradigm_shift_015"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "generated-media"},
  "16_billion_gate_unreviewable": {"specBaseName": "16_billion_gate_unreviewable", "dataPoints": {"type": "density_comparison", "chartId": "billion_gate_unreviewable", "chipView": {"gateCount": "2.1 billion", "zoomLevels": 3}, "diffView": {"linesChanged": 47382, "scrollSpeed": "fast"}, "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "17_review_spec_verify_output": {"specBaseName": "17_review_spec_verify_output", "dataPoints": {"type": "comparison_layout", "chartId": "review_spec_verify_output", "panels": {"left": {"type": "prompt_document", "header": "PROMPT", "accentColor": "#D9944A", "lineCount": 20}, "right": {"type": "test_suite", "header": "TEST SUITE", "accentColor": "#5AAA6E", "tests": [{"name": "test_counter_increments", "status": "pass"}, {"name": "test_reset_clears_state", "status": "pass"}, {"name": "test_overflow_wraps", "status": "pass"}, {"name": "test_edge_case_zero", "status": "pass"}, {"name": "test_concurrent_access", "status": "pass"}]}}, "label": "Review the spec. Verify the output.", "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "18_prompt_mold_finale": {"specBaseName": "18_prompt_mold_finale", "dataPoints": {"type": "metaphor_animation", "chartId": "prompt_mold_finale", "elements": {"prompt": {"label": "PROMPT", "color": "#D9944A", "role": "mold_specification"}, "code": {"color": "#E2E8F0", "role": "plastic_output", "regenerates": true}, "tests": {"color": "#5AAA6E", "role": "mold_walls", "labels": ["assert", "expect", "verify", "test"]}}, "regenerationCycles": 3, "thesis": "The prompt is your mold. The code is just plastic.", "narrationSegments": ["part2_paradigm_shift_016"]}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "generated-media"},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 228.14;
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
