import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Part3MoldParts02MoldCrossSection } from "../Part3MoldParts02MoldCrossSection";
import { Part3MoldParts03MoldWallsIlluminate } from "../Part3MoldParts03MoldWallsIlluminate";
import { Part3MoldParts04LiquidInjection } from "../Part3MoldParts04LiquidInjection";
import { Part3MoldParts05BugAddsWall } from "../Part3MoldParts05BugAddsWall";
import { Part3MoldParts06RatchetTimelapse } from "../Part3MoldParts06RatchetTimelapse";
import { Part3MoldParts08BugForkRoad } from "../Part3MoldParts08BugForkRoad";
import { Part3MoldParts09FiveGenerations } from "../Part3MoldParts09FiveGenerations";
import { Part3MoldParts12PromptNozzle } from "../Part3MoldParts12PromptNozzle";
import { Part3MoldParts15GroundingStyles } from "../Part3MoldParts15GroundingStyles";
import { Part3MoldParts17ComponentTable } from "../Part3MoldParts17ComponentTable";
import { Part3MoldParts18CodeOutputFinale } from "../Part3MoldParts18CodeOutputFinale";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_mold_cross_section": Part3MoldParts02MoldCrossSection,
  "03_mold_walls_illuminate": Part3MoldParts03MoldWallsIlluminate,
  "04_liquid_injection": Part3MoldParts04LiquidInjection,
  "05_bug_adds_wall": Part3MoldParts05BugAddsWall,
  "06_ratchet_timelapse": Part3MoldParts06RatchetTimelapse,
  "08_bug_fork_road": Part3MoldParts08BugForkRoad,
  "09_five_generations": Part3MoldParts09FiveGenerations,
  "12_prompt_nozzle": Part3MoldParts12PromptNozzle,
  "15_grounding_styles": Part3MoldParts15GroundingStyles,
  "17_component_table": Part3MoldParts17ComponentTable,
  "18_code_output_finale": Part3MoldParts18CodeOutputFinale,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_mold_cross_section": 420,
  "03_mold_walls_illuminate": 300,
  "04_liquid_injection": 870,
  "05_bug_adds_wall": 480,
  "06_ratchet_timelapse": 270,
  "08_bug_fork_road": 540,
  "09_five_generations": 540,
  "12_prompt_nozzle": 720,
  "15_grounding_styles": 780,
  "17_component_table": 300,
  "18_code_output_finale": 90,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "14_veo_grounding_material": { defaultSrc: "veo/grounding_material_flow.mp4", backgroundSrc: "veo/grounding_material_flow.mp4", outputSrc: "veo/grounding_material_flow.mp4", baseSrc: "veo/grounding_material_flow.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "01_section_title_card": { fadeOutFrames: 60 },
  "04_liquid_injection": { gradientOverlay: "bottom" },
  "05_bug_adds_wall": { fadeOutFrames: 30 },
  "10_z3_formal_proof": { fadeInFrames: 60 },
  "11_module_boundary": { fadeInFrames: 60 },
  "15_grounding_styles": { fadeInFrames: 60 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_cross_section", "regions": ["walls", "nozzle", "cavity"], "role": "three_parts_preview"}], "narrationSegments": ["part3_mold_parts_001", "part3_mold_parts_002", "part3_mold_parts_003", "part3_mold_parts_004", "part3_mold_parts_005"], "durationSeconds": 44.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 60}, "renderMode": "component"},
  "02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "mold_diagram", "regions": [{"id": "walls", "label": "TESTS", "color": "#4A90D9", "highlightFrame": 60}, {"id": "nozzle", "label": "PROMPT", "color": "#D9944A", "highlightFrame": 150}, {"id": "cavity", "label": "GROUNDING", "color": "#4AD9A0", "highlightFrame": 240}], "narrationSegments": ["part3_mold_parts_005"], "durationSeconds": 14.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_mold_walls_illuminate": {"specBaseName": "03_mold_walls_illuminate", "dataPoints": {"type": "mold_wall_labels", "walls": [{"label": "null → None", "side": "left", "frameIn": 30}, {"label": "empty string → ''", "side": "right", "frameIn": 75}, {"label": "handles unicode", "side": "left", "frameIn": 120}, {"label": "latency < 100ms", "side": "right", "frameIn": 165}], "narrationSegments": ["part3_mold_parts_006"], "durationSeconds": 10.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_liquid_injection": {"specBaseName": "04_liquid_injection", "dataPoints": {"type": "liquid_injection_with_annotations", "liquidGradient": ["#38BDF8", "#0D9488"], "focusWall": "null → None", "annotations": [{"text": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "color": "#F87171", "frameIn": 330}, {"text": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80", "frameIn": 510}], "narrationSegments": ["part3_mold_parts_007", "part3_mold_parts_008"], "durationSeconds": 29.0}, "mediaAliases": {}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "05_bug_adds_wall": {"specBaseName": "05_bug_adds_wall", "dataPoints": {"type": "bug_to_wall", "bugLabel": "BUG", "newWall": {"label": "rejects negative IDs", "color": "#4A90D9"}, "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser"], "narrationSegments": ["part3_mold_parts_009"], "durationSeconds": 16.0}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 30}, "renderMode": "component"},
  "06_ratchet_timelapse": {"specBaseName": "06_ratchet_timelapse", "dataPoints": {"type": "ratchet_timelapse", "newWalls": [{"label": "handles empty array", "side": "left", "cycle": 1}, {"label": "timeout at 5s", "side": "right", "cycle": 2}, {"label": "rejects SQL injection", "side": "left", "cycle": 3}, {"label": "UTF-8 BOM stripped", "side": "right", "cycle": 4}], "wallCountRange": [5, 9], "narrationSegments": ["part3_mold_parts_010"], "durationSeconds": 9.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_split_traditional_vs_pdd": {"specBaseName": "07_split_traditional_vs_pdd", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "divider": {"color": "#FFFFFF", "width": 2, "opacity": 0.3}, "panels": {"left": {"header": "TRADITIONAL", "headerColor": "#F87171", "steps": ["Bug found", "Patch code", "Similar bug elsewhere", "Patch again", "Different bug", "Patch again..."], "infinite": true}, "right": {"header": "PDD", "headerColor": "#4ADE80", "steps": ["Bug found", "Add test (pdd bug)", "Regenerate (pdd fix)", "Bug impossible forever ✓"], "infinite": false}}, "narrationSegments": ["part3_mold_parts_011"], "durationSeconds": 8.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_bug_fork_road": {"specBaseName": "08_bug_fork_road", "dataPoints": {"type": "fork_diagram", "root": {"label": "Bug found", "color": "#EF4444"}, "branches": [{"label": "Code bug", "action": "Add a wall", "color": "#4A90D9", "side": "left"}, {"label": "Prompt defect", "action": "Change the mold itself", "color": "#D9944A", "side": "right"}], "narrationSegments": ["part3_mold_parts_012"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "09_five_generations": {"specBaseName": "09_five_generations", "dataPoints": {"type": "multi_generation", "generationCount": 5, "results": [{"gen": 1, "status": "fail", "icon": "x", "color": "#EF4444"}, {"gen": 2, "status": "fail", "icon": "x", "color": "#EF4444"}, {"gen": 3, "status": "partial", "icon": "warning", "color": "#FBBF24"}, {"gen": 4, "status": "partial", "icon": "warning", "color": "#FBBF24"}, {"gen": 5, "status": "pass", "icon": "check", "color": "#4ADE80"}], "label": "Generate five. Pick the one that passes all tests.", "narrationSegments": ["part3_mold_parts_013"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "10_z3_formal_proof": {"specBaseName": "10_z3_formal_proof", "dataPoints": {"type": "sidebar_annotation", "topic": "Z3 formal verification", "keyTerms": ["Z3", "SMT solver", "formal equivalence checking", "mathematical proof"], "provenWalls": [1, 3], "provenColor": "#A78BFA", "logos": [{"text": "Z3", "color": "#A78BFA"}, {"text": "SF", "color": "#7C3AED"}], "narrationSegments": ["part3_mold_parts_014"], "durationSeconds": 26.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "11_module_boundary": {"specBaseName": "11_module_boundary", "dataPoints": {"type": "system_diagram", "centralModule": {"name": "user_parser", "color": "#4A90D9", "governed": true}, "surroundingModules": [{"name": "auth_service", "governed": false}, {"name": "db_layer", "governed": false}, {"name": "api_router", "governed": false}, {"name": "cache", "governed": false}, {"name": "logger", "governed": false}, {"name": "config", "governed": false}], "label": "PDD operates at the module level.", "narrationSegments": ["part3_mold_parts_015"], "durationSeconds": 22.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "12_prompt_nozzle": {"specBaseName": "12_prompt_nozzle", "dataPoints": {"type": "prompt_nozzle", "nozzleLabels": ["intent", "requirements", "constraints"], "promptText": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.", "promptFile": "user_parser.prompt", "dualGeneration": true, "narrationSegments": ["part3_mold_parts_016"], "durationSeconds": 24.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "13_prompt_ratio": {"specBaseName": "13_prompt_ratio", "dataPoints": {"type": "compression_ratio", "promptLines": 15, "codeLines": 200, "ratio": "1:5 to 1:10", "contextComparison": {"left": {"tokens": 15000, "type": "raw_code", "modules": 1}, "right": {"tokens": 15000, "type": "prompts", "modules": 10}}, "narrationSegments": ["part3_mold_parts_017", "part3_mold_parts_018"], "durationSeconds": 18.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "14_veo_grounding_material": {"specBaseName": "14_veo_grounding_material", "dataPoints": {"type": "veo_clip", "clipId": "grounding_material_flow", "durationSeconds": 8, "characters": []}, "mediaAliases": {"defaultSrc": "veo/grounding_material_flow.mp4", "backgroundSrc": "veo/grounding_material_flow.mp4", "outputSrc": "veo/grounding_material_flow.mp4", "baseSrc": "veo/grounding_material_flow.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "15_grounding_styles": {"specBaseName": "15_grounding_styles", "dataPoints": {"type": "grounding_styles", "materialStreams": [{"label": "OOP", "color": "#4A90D9", "style": "angular"}, {"label": "Functional", "color": "#D9944A", "style": "smooth"}, {"label": "Your Team's Style", "color": "#4AD9A0", "style": "organic"}], "codeComparison": {"pathA": {"style": "OOP", "borderColor": "#4A90D9"}, "pathB": {"style": "Functional", "borderColor": "#D9944A"}}, "feedbackLoop": {"database": "Grounding Database", "stores": "(prompt, code) pair"}, "narrationSegments": ["part3_mold_parts_019"], "durationSeconds": 26.0}, "mediaAliases": {}, "overlayConfig": {"fadeInFrames": 60}, "renderMode": "component"},
  "16_three_components_pullback": {"specBaseName": "16_three_components_pullback", "dataPoints": {"type": "pipeline_pullback", "stages": [{"component": "Prompt", "encodes": "Intent", "color": "#D9944A"}, {"component": "Grounding", "encodes": "Style", "color": "#4AD9A0"}, {"component": "Tests", "encodes": "Correctness", "color": "#4A90D9"}, {"component": "Code", "encodes": "Output", "color": "#38BDF8"}], "narrationSegments": ["part3_mold_parts_020"], "durationSeconds": 9.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "17_component_table": {"specBaseName": "17_component_table", "dataPoints": {"type": "component_table", "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#D9944A"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#4AD9A0"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#4A90D9"}], "hierarchyRule": "When these conflict, tests win. Always.", "hierarchyOrder": ["Tests", "Prompt", "Grounding"], "narrationSegments": ["part3_mold_parts_021"], "durationSeconds": 10.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "18_code_output_finale": {"specBaseName": "18_code_output_finale", "dataPoints": {"type": "code_output_finale", "message": "The code is output. The mold is what matters.", "codeGlowFade": {"from": 0.2, "to": 0.0, "frames": [20, 40]}, "moldGlowIncrease": {"from": 0.4, "to": 0.6, "frames": [40, 60]}, "narrationSegments": ["part3_mold_parts_022"], "durationSeconds": 3.0}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const Part3MoldPartsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 345.88;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part3_mold_parts/narration.wav")} />
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
              <SlotScaledSequence intrinsicDurationInFrames={intrinsicDurationInFrames}>
                <VisualContractProvider contract={visualContract}>
                  <VisualMediaProvider media={visualMedia}>
                    <GeneratedContractVisual />
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

export default Part3MoldPartsSection;
