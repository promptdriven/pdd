import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part3MoldThreeParts02MoldCrossSection } from "../Part3MoldThreeParts02MoldCrossSection";
import { Part3MoldThreeParts10ThreeComponentsTable } from "../Part3MoldThreeParts10ThreeComponentsTable";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_mold_cross_section": Part3MoldThreeParts02MoldCrossSection,
  "18_three_components_table": Part3MoldThreeParts10ThreeComponentsTable,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_mold_cross_section": 300,
  "18_three_components_table": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "04_liquid_hits_wall": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "16_grounding_material": { defaultSrc: "veo/grounding_material_flow.mp4", backgroundSrc: "veo/grounding_material_flow.mp4", outputSrc: "veo/grounding_material_flow.mp4", baseSrc: "veo/grounding_material_flow.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell"}, {"shape": "mold_walls", "color": "#D9944A", "component": "test_walls"}, {"shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle"}, {"shape": "mold_material", "color": "#A78BFA", "component": "grounding_material"}], "narrationSegments": ["part3_mold_three_parts_001", "part3_mold_three_parts_002", "part3_mold_three_parts_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints"}, {"id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification"}, {"id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_004", "part3_mold_three_parts_005", "part3_mold_three_parts_006"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_test_walls_illuminate": {"specBaseName": "03_test_walls_illuminate", "dataPoints": {"type": "animated_diagram", "diagramId": "test_walls_illuminate", "walls": [{"id": "wall_null", "label": "null → None"}, {"id": "wall_empty", "label": "empty string → ''"}, {"id": "wall_unicode", "label": "handles unicode"}, {"id": "wall_latency", "label": "latency < 100ms"}, {"id": "wall_no_throw", "label": "no exceptions thrown"}, {"id": "wall_idempotent", "label": "idempotent"}], "wallColor": "#D9944A", "liquidGradient": ["#4A90D9", "#A78BFA"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_007", "part3_mold_three_parts_008"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_liquid_hits_wall": {"specBaseName": "04_liquid_hits_wall", "dataPoints": {"type": "veo_clip", "clipId": "liquid_hits_wall", "camera": {"framing": "extreme_close_up", "movement": "static_with_slight_drift", "dof": "very_shallow", "aperture": "f/2.0", "angle": "side_profile"}, "lighting": {"key": {"color": "#FFB347", "type": "self_luminous_liquid"}, "fill": {"color": "#B8C9E0", "opacity": 0.2, "type": "steel_reflection"}, "rim": {"color": "#FFFFFF", "opacity": 0.3, "type": "wall_edge_highlight"}, "contact": {"color": "#FF8C42", "opacity": 0.4, "type": "amber_pulse"}}, "narrationSegments": ["part3_mold_three_parts_009"]}, "mediaAliases": {"defaultSrc": "veo/bug_adds_wall.mp4", "backgroundSrc": "veo/bug_adds_wall.mp4", "outputSrc": "veo/bug_adds_wall.mp4", "baseSrc": "veo/bug_adds_wall.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_research_annotations": {"specBaseName": "05_research_annotations", "dataPoints": {"type": "annotation_overlay", "diagramId": "research_annotations", "annotations": [{"id": "coderabbit_stat", "type": "warning", "stat": "1.7×", "text": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "detail": "75% more logic errors, 8× more perf problems", "color": "#EF4444"}, {"id": "dora_stat", "type": "positive", "text": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_009", "part3_mold_three_parts_010"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_bug_add_wall": {"specBaseName": "06_bug_add_wall", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_add_wall", "phases": [{"id": "bug_found", "action": "highlight_bug_line", "color": "#EF4444"}, {"id": "add_wall", "action": "materialize_wall", "label": "handles_null_userid", "color": "#D9944A"}, {"id": "regenerate", "action": "dissolve_and_regenerate_code"}, {"id": "permanent", "action": "wall_glows_permanently"}], "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_011", "part3_mold_three_parts_012", "part3_mold_three_parts_013"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_ratchet_timelapse": {"specBaseName": "07_ratchet_timelapse", "dataPoints": {"type": "animated_diagram", "diagramId": "ratchet_timelapse", "wallTimeline": [{"frame": 0, "count": 4, "phase": "initial"}, {"frame": 90, "count": 7, "phase": "early_growth"}, {"frame": 180, "count": 12, "phase": "mid_growth"}, {"frame": 270, "count": 18, "phase": "acceleration"}, {"frame": 330, "count": 25, "phase": "mature"}], "wallColor": "#D9944A", "ratchetMetaphor": true, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_014", "part3_mold_three_parts_015"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_traditional_vs_pdd_split": {"specBaseName": "08_traditional_vs_pdd_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "TRADITIONAL", "headerColor": "#EF4444", "steps": [{"text": "Bug found", "opacity": 0.8}, {"text": "→ Patch code", "opacity": 0.8}, {"text": "Similar bug elsewhere", "opacity": 0.7}, {"text": "→ Patch again", "opacity": 0.6}, {"text": "Different bug", "opacity": 0.5}, {"text": "→ Patch again...", "opacity": 0.4}, {"text": "...", "opacity": 0.2}], "thematicRole": "endless_cycle"}, "rightPanel": {"header": "PDD", "headerColor": "#4ADE80", "steps": [{"text": "Bug found"}, {"text": "→ Add test (pdd bug)"}, {"text": "→ Regenerate (pdd fix)"}, {"text": "Bug impossible forever", "icon": "lock", "glow": true}], "thematicRole": "permanent_fix"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_015", "part3_mold_three_parts_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_bug_fork_diagram": {"specBaseName": "09_bug_fork_diagram", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_fork", "root": {"label": "Bug found", "color": "#EF4444"}, "branches": [{"id": "code_bug", "label": "Code bug — add a wall", "color": "#D9944A", "action": "add_test", "file": "test_user_parser.py"}, {"id": "prompt_defect", "label": "Prompt defect — change the mold", "color": "#2DD4BF", "action": "fix_specification", "file": "user_parser.prompt"}], "convergence": {"label": "Regenerate", "color": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_016"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_five_generations": {"specBaseName": "10_five_generations", "dataPoints": {"type": "animated_diagram", "diagramId": "five_generations", "panels": [{"id": "gen_1", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_2", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_3", "status": "fail", "color": "#EF4444", "statusDelay": 0}, {"id": "gen_4", "status": "warn", "color": "#F59E0B", "statusDelay": 60}, {"id": "gen_5", "status": "pass", "color": "#4ADE80", "statusDelay": 120}], "label": "Generate five. Pick the one that passes all tests.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_017"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "11_z3_formal_proof": {"specBaseName": "11_z3_formal_proof", "dataPoints": {"type": "annotation_overlay", "diagramId": "z3_formal_proof", "comparison": {"left": {"label": "Synopsys Formality", "domain": "chip_verification", "color": "#4A90D9"}, "right": {"label": "PDD + Z3", "domain": "code_verification", "color": "#2DD4BF"}, "equivalence": {"symbol": "≡", "color": "#A78BFA"}}, "emphasisLine": "Not sampling. Mathematical proof.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_018"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "12_module_level_aside": {"specBaseName": "12_module_level_aside", "dataPoints": {"type": "animated_diagram", "diagramId": "module_level_aside", "modules": [{"id": "auth", "label": "auth"}, {"id": "users", "label": "users"}, {"id": "payments", "label": "payments"}, {"id": "api", "label": "api"}, {"id": "parser", "label": "parser", "highlighted": true}, {"id": "events", "label": "events"}, {"id": "cache", "label": "cache"}, {"id": "queue", "label": "queue"}, {"id": "config", "label": "config"}], "limitations": ["race conditions", "cascading failures", "architectural mismatches"], "pddModule": "parser", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_019"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_prompt_nozzle": {"specBaseName": "13_prompt_nozzle", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_nozzle", "nozzleLabels": ["intent", "requirements", "constraints"], "promptText": ["Parse user IDs from untrusted input.", "Return None on failure, never throw.", "Handle unicode."], "promptFile": "user_parser.prompt", "dualGeneration": true, "nozzleColor": "#2DD4BF", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_020", "part3_mold_three_parts_021", "part3_mold_three_parts_022"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "14_prompt_ratio": {"specBaseName": "14_prompt_ratio", "dataPoints": {"type": "animated_diagram", "diagramId": "prompt_ratio", "promptSize": "~12 lines", "codeSize": "~200 lines", "ratio": "1:5 to 1:10", "analogy": {"prompt": "header file", "code": "OBJ file"}, "promptColor": "#2DD4BF", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_023"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "15_context_window_comparison": {"specBaseName": "15_context_window_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "RAW CODE CONTEXT", "headerColor": "#94A3B8", "content": "dense_code", "tokenCount": 15000, "scope": "1 module's implementation", "thematicRole": "overwhelming_code"}, "rightPanel": {"header": "PROMPT CONTEXT", "headerColor": "#2DD4BF", "content": "prompt_blocks", "tokenCount": 15000, "scope": "10 modules' specifications", "thematicRole": "curated_prompts"}, "multiplier": "10×", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_024"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "16_grounding_material": {"specBaseName": "16_grounding_material", "dataPoints": {"type": "veo_clip", "clipId": "grounding_material", "camera": {"framing": "close_up", "movement": "static_with_slight_drift", "dof": "shallow", "aperture": "f/2.0", "angle": "side_profile_eye_level"}, "lighting": {"key": {"color": "#E2E8F0", "opacity": 0.3, "type": "overhead_neutral"}, "materials": [{"color": "#4A90D9", "style": "crystalline_oop", "opacity": 0.4}, {"color": "#4ADE80", "style": "organic_functional", "opacity": 0.3}, {"color": "#D9944A", "style": "warm_team_style", "opacity": 0.3}]}, "narrationSegments": ["part3_mold_three_parts_025"]}, "mediaAliases": {"defaultSrc": "veo/grounding_material_flow.mp4", "backgroundSrc": "veo/grounding_material_flow.mp4", "outputSrc": "veo/grounding_material_flow.mp4", "baseSrc": "veo/grounding_material_flow.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "17_grounding_feedback_loop": {"specBaseName": "17_grounding_feedback_loop", "dataPoints": {"type": "animated_diagram", "diagramId": "grounding_feedback_loop", "phases": [{"id": "dual_grounding", "paths": [{"label": "OOP grounding", "style": "classes_with_methods", "color": "#4A90D9"}, {"label": "Functional grounding", "style": "pure_functions", "color": "#4ADE80"}]}, {"id": "feedback", "flow": "(prompt, code) → Grounding Database", "color": "#A78BFA"}, {"id": "pipeline", "stages": ["Prompt", "Grounding", "Mold", "Test Walls", "Code"]}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_026", "part3_mold_three_parts_027", "part3_mold_three_parts_028"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "18_three_components_table": {"specBaseName": "18_three_components_table", "dataPoints": {"type": "animated_diagram", "diagramId": "three_components_table", "table": {"columns": ["Component", "Encodes", "Owner"], "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#2DD4BF"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#A78BFA"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A"}]}, "priorityRule": "When these conflict, tests win. Always.", "hierarchy": ["Tests", "Prompt", "Grounding"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_029", "part3_mold_three_parts_030"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part3MoldThreePartsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 344.16;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part3_mold_three_parts/narration.wav")} />
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

export default Part3MoldThreePartsSection;
