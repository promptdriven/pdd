import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
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
  "01_section_title_card": 120,
  "04_defect_fix_the_mold": 420,
  "05_value_migration_split": 480,
  "07_verilog_synthesis_triple": 540,
  "09_abstraction_staircase": 480,
  "10_netlist_zoom_unreviewable": 480,
  "11_prompt_replaces_review": 360,
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
  "03_injection_molding_process": { counterOverlay: true, counterPosition: "lower_right" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 2, "sectionLabel": "PART 2", "titleLine1": "THE PARADIGM", "titleLine2": "SHIFT", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_cavity_outline", "color": "#D9944A", "component": "injection_mold"}, {"shape": "circuit_schematic", "color": "#4A90D9", "component": "chip_design"}], "narrationSegments": ["part2_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_factory_floor_intro": {"specBaseName": "02_factory_floor_intro", "dataPoints": {"type": "veo_clip", "clipId": "factory_floor_intro", "camera": {"framing": "wide_to_medium", "movement": "dolly_forward", "travelPercent": 8, "dof": "moderate", "angle": "slightly_low"}, "lighting": {"key": {"color": "#E8C87A", "position": "overhead", "type": "industrial"}, "fill": "ambient_bounce", "grade": "industrial_warm"}, "narrationSegments": ["part2_002"], "narrationTimingSeconds": {"start": 514.0, "end": 520.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_injection_molding_process": {"specBaseName": "03_injection_molding_process", "dataPoints": {"type": "veo_clip", "clipId": "injection_molding_process", "camera": {"framing": "close_up", "movement": "static_with_vibration", "dof": "shallow", "angle": "slightly_above"}, "lighting": {"key": {"color": "#C0D8E8", "position": "work_light", "type": "cool_industrial"}, "accent": {"color": "#D4A043", "source": "molten_plastic"}, "grade": "cool_industrial_warm_accent"}, "overlay": {"counter": {"values": [1, 10, 100, 1000, 10000], "position": "lower_right"}}, "narrationSegments": ["part2_003"], "narrationTimingSeconds": {"start": 520.0, "end": 528.0}}, "overlayConfig": {"counterOverlay": true, "counterPosition": "lower_right"}, "renderMode": "generated-media"},
  "04_defect_fix_the_mold": {"specBaseName": "04_defect_fix_the_mold", "dataPoints": {"type": "animated_diagram", "diagramId": "defect_fix_mold", "acts": [{"name": "defect", "frames": [60, 100], "element": "red_pulse_on_part"}, {"name": "rejected_patch", "frames": [100, 140], "element": "ghost_tool_red_x"}, {"name": "fix_mold", "frames": [140, 200], "element": "wall_adjustment_amber"}, {"name": "fixed_parts", "frames": [200, 340], "element": "green_checkmark_parts"}], "colors": {"defect": "#EF4444", "mold_wall": "#D9944A", "fixed": "#5AAA6E", "part": "#94A3B8"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_004"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_value_migration_split": {"specBaseName": "05_value_migration_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "CRAFTING", "concept": "Value lives in the object — history accumulates, loss is permanent", "summaryLabel": "Value lives in the object", "auraTarget": "object", "auraColor": "#C4956A", "background": "#0F172A"}, "rightPanel": {"label": "MOLDING", "concept": "Value lives in the specification — parts are disposable, regenerated at will", "summaryLabel": "Value lives in the specification", "auraTarget": "mold", "auraColor": "#D9944A", "partDissolveAndRegenerate": true, "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part2_005"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_chip_design_history": {"specBaseName": "06_chip_design_history", "dataPoints": {"type": "veo_clip", "clipId": "chip_design_1980s_lab", "characters": [{"id": "chip_engineer", "label": "Chip Engineer", "referencePrompt": "Male engineer, 30s-40s, dress shirt with rolled sleeves, 1980s electronics lab, hunched over drafting desk drawing circuit schematics by hand"}], "camera": {"framing": "medium_wide_to_close_up", "movement": "push_in", "travelPercent": 15, "dof": "moderate_to_shallow", "angle": "over_shoulder_elevated"}, "lighting": {"key": {"color": "#E8C87A", "position": "left", "type": "desk_lamp"}, "fill": {"color": "#B8C8D8", "position": "overhead", "type": "fluorescent"}, "practical": {"color": "#3A8A3A", "source": "oscilloscope"}, "grade": "1980s_warm_cool_mixed"}, "narrationSegments": ["part2_006"], "narrationTimingSeconds": {"start": 558.0, "end": 565.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_verilog_synthesis_triple": {"specBaseName": "07_verilog_synthesis_triple", "dataPoints": {"type": "animated_diagram", "diagramId": "verilog_synthesis_triple", "phases": [{"name": "schematic_to_verilog", "frames": [0, 180], "elements": ["dissolving_schematic", "verilog_code", "compiler", "single_netlist"]}, {"name": "triple_synthesis", "frames": [180, 540], "elements": ["shared_code", "three_compilers", "three_netlists", "equivalence_checkmarks"]}], "verilogCode": "module counter(\n  input clk, rst,\n  output reg [7:0] count\n);\n  always @(posedge clk)\n    if (rst) count <= 0;\n    else count <= count + 1;\nendmodule", "netlists": [{"id": "netlist_a", "gateCount": 6, "layout": "horizontal_compact"}, {"id": "netlist_b", "gateCount": 8, "layout": "vertical_long"}, {"id": "netlist_c", "gateCount": 5, "layout": "mixed_optimized"}], "equivalence": true, "colors": {"code_keywords": "#C792EA", "code_text": "#E2E8F0", "compiler": "#4A90D9", "gates": "#94A3B8", "checkmark": "#5AAA6E"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_007"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_synopsys_pdd_equivalence": {"specBaseName": "08_synopsys_pdd_equivalence", "dataPoints": {"type": "animated_diagram", "diagramId": "synopsys_pdd_equivalence", "rows": [{"label": "SYNOPSYS", "color": "#4A90D9", "y": 280, "stages": [{"name": "Verilog spec", "icon": "document_code", "x": 260}, {"name": "Synthesis", "icon": "gear", "x": 560}, {"name": "Hardware", "icon": "gate_cluster", "x": 860, "color": "#94A3B8"}, {"name": "FEC verified", "icon": "shield_check", "x": 1160, "color": "#5AAA6E"}]}, {"label": "PDD", "color": "#D9944A", "y": 680, "stages": [{"name": "Prompt spec", "icon": "document_text", "x": 260}, {"name": "Generation", "icon": "neural_network", "x": 560}, {"name": "Software", "icon": "code_brackets", "x": 860, "color": "#94A3B8"}, {"name": "Tests pass", "icon": "shield_check", "x": 1160, "color": "#5AAA6E"}]}], "equivalenceSymbol": "≡", "summaryText": "Specification in → verified artifact out", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_008"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_abstraction_staircase": {"specBaseName": "09_abstraction_staircase", "dataPoints": {"type": "animated_diagram", "diagramId": "abstraction_staircase", "steps": [{"level": 1, "label": "Transistors", "decade": "1970s", "position": [120, 800], "color": "#64748B"}, {"level": 2, "label": "Schematics", "decade": "1980s", "position": [400, 680], "color": "#7A8FA3"}, {"level": 3, "label": "RTL / Verilog", "decade": "1990s", "position": [680, 560], "color": "#94A3B8"}, {"level": 4, "label": "Behavioral / HLS", "decade": "2010s", "position": [960, 440], "color": "#B0BEC5"}, {"level": 5, "label": "Natural Language → Code", "decade": "2020s", "position": [1240, 320], "color": "#D9944A", "active": true}], "transitionArrows": {"label": "Couldn't scale", "color": "#EF4444"}, "citations": ["IEEE 1364-1995 (Verilog standardization)", "Accellera 2010 (90% behavioral IP)", "Microsoft Research 2007+ (Z3 SMT solver)"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_009"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_netlist_zoom_unreviewable": {"specBaseName": "10_netlist_zoom_unreviewable", "dataPoints": {"type": "animated_diagram", "diagramId": "netlist_zoom_unreviewable", "phases": [{"name": "chip_layout_zoom", "frames": [0, 240], "zoomLevels": [1, 2, 4, 8], "gateCount": "~2.4 billion", "colors": {"metal": "#4A90D9", "polysilicon": "#D9944A", "diffusion": "#5AAA6E", "vias": "#E2E8F0"}}, {"name": "code_diff_scroll", "frames": [240, 480], "linesChanged": 10247, "scrollSpeedRange": [2, 30], "addedColor": "#5AAA6E", "deletedColor": "#EF4444"}], "argument": "Code review at AI generation scale is as futile as reviewing a gate-level netlist", "backgroundColor": "#0A0F1A", "narrationSegments": ["part2_010"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "11_prompt_replaces_review": {"specBaseName": "11_prompt_replaces_review", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "REVIEW THE CODE", "concept": "Impossible at scale — code review becomes netlist review", "cognitiveLoad": "OVERLOADED", "loadPercent": 100, "background": "#0F172A"}, "rightPanel": {"label": "REVIEW THE SPEC", "concept": "Verify output against spec — review the prompt, run the tests", "cognitiveLoad": "MANAGEABLE", "loadPercent": 25, "tests": ["test_handles_null_input", "test_returns_correct_format", "test_unicode_support", "test_edge_case_empty", "test_performance_under_100ms", "test_idempotent_behavior"], "background": "#0A0F1A"}, "backgroundColor": "#000000", "narrationSegments": ["part2_011"]}, "overlayConfig": null, "renderMode": "raw-media"},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 227.48;
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
                {visualOverlayConfig || visualMedia?.leftSrc || visualMedia?.rightSrc ? (
                  <GeneratedMediaVisual config={visualOverlayConfig} />
                ) : (
                  <OffthreadVideo src={staticFile(visualMedia.defaultSrc)} style={{ width: "100%", height: "100%" }} />
                )}
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
