import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part3MoldThreeParts01SectionTitleCard } from "../Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "../Part3MoldThreeParts02MoldCrossSection";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part3MoldThreeParts01SectionTitleCard,
  "02_mold_cross_section": Part3MoldThreeParts02MoldCrossSection,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_mold_cross_section": 300,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell"}, {"shape": "mold_walls", "color": "#D9944A", "component": "test_walls"}, {"shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle"}, {"shape": "mold_material", "color": "#A78BFA", "component": "grounding_material"}], "narrationSegments": ["part3_mold_three_parts_001", "part3_mold_three_parts_002", "part3_mold_three_parts_003"]}, "overlayConfig": null, "renderMode": "component"},
  "02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints"}, {"id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification"}, {"id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_004", "part3_mold_three_parts_005", "part3_mold_three_parts_006"]}, "overlayConfig": null, "renderMode": "component"},
  "04_liquid_hits_wall": {"specBaseName": "04_liquid_hits_wall", "dataPoints": {"type": "veo_clip", "clipId": "liquid_hits_wall", "camera": {"framing": "extreme_close_up", "movement": "static_with_slight_drift", "dof": "very_shallow", "aperture": "f/2.0", "angle": "side_profile"}, "lighting": {"key": {"color": "#FFB347", "type": "self_luminous_liquid"}, "fill": {"color": "#B8C9E0", "opacity": 0.2, "type": "steel_reflection"}, "rim": {"color": "#FFFFFF", "opacity": 0.3, "type": "wall_edge_highlight"}, "contact": {"color": "#FF8C42", "opacity": 0.4, "type": "amber_pulse"}}, "narrationSegments": ["part3_mold_three_parts_009"]}, "overlayConfig": null, "renderMode": "component"},
  "05_research_annotations": {"specBaseName": "05_research_annotations", "dataPoints": {"type": "annotation_overlay", "diagramId": "research_annotations", "annotations": [{"id": "coderabbit_stat", "type": "warning", "stat": "1.7×", "text": "AI code: 1.7× more issues", "source": "CodeRabbit, 2025", "detail": "75% more logic errors, 8× more perf problems", "color": "#EF4444"}, {"id": "dora_stat", "type": "positive", "text": "AI + strong tests = amplified delivery", "source": "DORA, 2025", "color": "#4ADE80"}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_009", "part3_mold_three_parts_010"]}, "overlayConfig": null, "renderMode": "component"},
  "09_bug_fork_diagram": {"specBaseName": "09_bug_fork_diagram", "dataPoints": {"type": "animated_diagram", "diagramId": "bug_fork", "root": {"label": "Bug found", "color": "#EF4444"}, "branches": [{"id": "code_bug", "label": "Code bug — add a wall", "color": "#D9944A", "action": "add_test", "file": "test_user_parser.py"}, {"id": "prompt_defect", "label": "Prompt defect — change the mold", "color": "#2DD4BF", "action": "fix_specification", "file": "user_parser.prompt"}], "convergence": {"label": "Regenerate", "color": "#4ADE80"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_016"]}, "overlayConfig": null, "renderMode": "component"},
  "15_context_window_comparison": {"specBaseName": "15_context_window_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"header": "RAW CODE CONTEXT", "headerColor": "#94A3B8", "content": "dense_code", "tokenCount": 15000, "scope": "1 module's implementation", "thematicRole": "overwhelming_code"}, "rightPanel": {"header": "PROMPT CONTEXT", "headerColor": "#2DD4BF", "content": "prompt_blocks", "tokenCount": 15000, "scope": "10 modules' specifications", "thematicRole": "curated_prompts"}, "multiplier": "10×", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_mold_three_parts_024"]}, "overlayConfig": null, "renderMode": "component"},
  "16_grounding_material": {"specBaseName": "16_grounding_material", "dataPoints": {"type": "veo_clip", "clipId": "grounding_material", "camera": {"framing": "close_up", "movement": "static_with_slight_drift", "dof": "shallow", "aperture": "f/2.0", "angle": "side_profile_eye_level"}, "lighting": {"key": {"color": "#E2E8F0", "opacity": 0.3, "type": "overhead_neutral"}, "materials": [{"color": "#4A90D9", "style": "crystalline_oop", "opacity": 0.4}, {"color": "#4ADE80", "style": "organic_functional", "opacity": 0.3}, {"color": "#D9944A", "style": "warm_team_style", "opacity": 0.3}]}, "narrationSegments": ["part3_mold_three_parts_025"]}, "overlayConfig": null, "renderMode": "component"},
};

export const Part3MoldThreePartsSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 344.16;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default Part3MoldThreePartsSection;
