import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part3MoldThreeParts01SectionTitleCard } from "../Part3MoldThreeParts01SectionTitleCard";
import { Part3MoldThreeParts02MoldCrossSection } from "../Part3MoldThreeParts02MoldCrossSection";
import { Part3MoldThreeParts03TestWallsConstraint } from "../Part3MoldThreeParts03TestWallsConstraint";
import { Part3MoldThreeParts04ResearchAnnotationsAiQuality } from "../Part3MoldThreeParts04ResearchAnnotationsAiQuality";
import { Part3MoldThreeParts06RatchetSplitComparison } from "../Part3MoldThreeParts06RatchetSplitComparison";
import { Part3MoldThreeParts07FiveGenerationsZ3 } from "../Part3MoldThreeParts07FiveGenerationsZ3";
import { Part3MoldThreeParts08PromptCapitalSpecification } from "../Part3MoldThreeParts08PromptCapitalSpecification";
import { Part3MoldThreeParts10ThreeComponentsTable } from "../Part3MoldThreeParts10ThreeComponentsTable";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": Part3MoldThreeParts01SectionTitleCard,
  "02_mold_cross_section": Part3MoldThreeParts02MoldCrossSection,
  "03_test_walls_constraint": Part3MoldThreeParts03TestWallsConstraint,
  "04_research_annotations_ai_quality": Part3MoldThreeParts04ResearchAnnotationsAiQuality,
  "06_ratchet_split_comparison": Part3MoldThreeParts06RatchetSplitComparison,
  "07_five_generations_z3": Part3MoldThreeParts07FiveGenerationsZ3,
  "08_prompt_capital_specification": Part3MoldThreeParts08PromptCapitalSpecification,
  "10_three_components_table": Part3MoldThreeParts10ThreeComponentsTable,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 120,
  "02_mold_cross_section": 300,
  "03_test_walls_constraint": 360,
  "04_research_annotations_ai_quality": 450,
  "08_prompt_capital_specification": 600,
  "10_three_components_table": 480,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "05_bug_adds_wall": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "06_ratchet_split_comparison": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "07_five_generations_z3": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "08_prompt_capital_specification": { defaultSrc: "veo/bug_adds_wall.mp4", backgroundSrc: "veo/bug_adds_wall.mp4", outputSrc: "veo/bug_adds_wall.mp4", baseSrc: "veo/bug_adds_wall.mp4" },
  "09_grounding_feedback_loop": { defaultSrc: "veo/grounding_feedback_loop.mp4", backgroundSrc: "veo/grounding_feedback_loop.mp4", outputSrc: "veo/grounding_feedback_loop.mp4", baseSrc: "veo/grounding_feedback_loop.mp4" },
  "10_three_components_table": { defaultSrc: "veo/grounding_feedback_loop.mp4", backgroundSrc: "veo/grounding_feedback_loop.mp4", outputSrc: "veo/grounding_feedback_loop.mp4", baseSrc: "veo/grounding_feedback_loop.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 3, "sectionLabel": "PART 3", "titleLine1": "THE MOLD HAS", "titleLine2": "THREE PARTS", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "wall_segment", "color": "#D9944A", "component": "tests"}, {"shape": "injection_nozzle", "color": "#4A90D9", "component": "prompts"}, {"shape": "material_swatch", "color": "#5AAA6E", "component": "grounding"}], "narrationSegments": ["part3_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_mold_cross_section": {"specBaseName": "02_mold_cross_section", "dataPoints": {"type": "technical_diagram", "diagramId": "mold_cross_section", "regions": [{"id": "walls", "label": "Test Capital", "color": "#D9944A", "labels": ["null → None", "empty string → ''", "handles unicode", "latency < 100ms"]}, {"id": "nozzle", "label": "Prompt Capital", "color": "#4A90D9", "labels": ["intent", "requirements", "constraints"]}, {"id": "cavity", "label": "Grounding Capital", "color": "#5AAA6E", "labels": ["style", "patterns", "conventions"]}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_002"]}, "overlayConfig": null, "renderMode": "component"},
  "03_test_walls_constraint": {"specBaseName": "03_test_walls_constraint", "dataPoints": {"type": "fluid_simulation", "diagramId": "test_walls_constraint", "particleCount": 200, "liquidColor": "#4A90D9", "wallColor": "#D9944A", "focusWall": "null → None", "collisionEffects": ["flash", "ripple", "screen_shake"], "terminalCommands": ["pdd generate user_parser", "Generating...", "✓ All 12 tests passing"], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_003"]}, "overlayConfig": null, "renderMode": "component"},
  "04_research_annotations_ai_quality": {"specBaseName": "04_research_annotations_ai_quality", "dataPoints": {"type": "research_annotations", "annotations": [{"id": "coderabbit_2025", "mainText": "1.7× more issues", "color": "#EF4444", "subStats": ["75% more logic errors", "8× more performance problems"], "source": "CodeRabbit, 2025", "finding": "AI-generated code quality deficit"}, {"id": "dora_2025", "mainText": "Amplified delivery", "color": "#5AAA6E", "subStats": ["AI + strong tests = accelerated"], "source": "DORA, 2025", "finding": "Tests transform AI from liability to accelerant"}], "equation": {"left": "AI code + No tests = 1.7× issues", "right": "AI code + Strong tests = Amplified delivery", "differentiator": "The walls"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_004"]}, "overlayConfig": null, "renderMode": "component"},
  "05_bug_adds_wall": {"specBaseName": "05_bug_adds_wall", "dataPoints": {"type": "veo_clip", "clipId": "bug_adds_wall", "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Mid-30s software developer, dark hoodie, focused expression, mechanical keyboard, minimalist desk, dim room lit by monitor glow"}], "camera": {"framing": "medium_close_up", "movement": "push_in", "zoomPercent": 8, "dof": "moderate", "rackFocus": true}, "lighting": {"key": {"color": "#4A90D9", "position": "front", "type": "monitor_glow"}, "transition": {"from": "#EF4444", "to": "#5AAA6E", "trigger": "midpoint"}, "fill": {"color": "#D9944A", "position": "background_right", "type": "desk_lamp"}}, "narrationSegments": ["part3_005"], "narrationTimingSeconds": {"start": 41.0, "end": 49.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_ratchet_split_comparison": {"specBaseName": "06_ratchet_split_comparison", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "TRADITIONAL", "concept": "Bug → Patch → Repeat forever", "rows": ["Bug: null crash → Patch: add null check", "Same bug: different module → Patch again", "New bug: unicode → Patch: encode input", "Regression → Patch: add condition", "Performance bug → Patch: optimize", "Another null crash → Patch again..."], "background": "#0F172A", "statusColor": "#EF4444"}, "rightPanel": {"label": "PDD", "concept": "Bug → Add wall → Regenerate → Bug impossible forever", "rows": ["Bug found: null crash", "pdd bug user_parser → test wall added", "pdd fix user_parser → All tests pass ✓"], "background": "#0A0F1A", "statusColor": "#5AAA6E"}, "timelineBar": {"left": {"type": "rising_line", "label": "Patching effort"}, "right": {"type": "ratchet_staircase", "label": "Test accumulation"}}, "callout": "A bug fix helps one place. A test prevents that bug everywhere, forever.", "backgroundColor": "#000000", "narrationSegments": ["part3_006"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_five_generations_z3": {"specBaseName": "07_five_generations_z3", "dataPoints": {"type": "multi_beat", "beats": [{"id": "five_generations", "type": "code_panel_array", "panelCount": 5, "testResults": [{"panel": 1, "result": "fail", "reason": "2 tests failed"}, {"panel": 2, "result": "warning", "reason": "Performance warning"}, {"panel": 3, "result": "pass", "reason": "All 12 tests pass", "winner": true}, {"panel": 4, "result": "fail", "reason": "Null handling error"}, {"panel": 5, "result": "warning", "reason": "Style violations"}], "caption": "Generate five. Pick the one that passes all tests."}, {"id": "z3_formal_proof", "type": "proof_notation", "property": "∀ input ∈ String: parse(input) ∈ {Valid(id), None}", "solver": "Z3 SMT Solver", "comparison": "Synopsys Formality — chip verification", "result": "PROVEN", "annotation": "Not sampling. Mathematical proof."}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_007"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "08_prompt_capital_specification": {"specBaseName": "08_prompt_capital_specification", "dataPoints": {"type": "multi_beat", "beats": [{"id": "nozzle_labels", "type": "mold_region_focus", "region": "nozzle", "color": "#4A90D9", "promptContent": "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.", "file": "user_parser.prompt"}, {"id": "two_generations", "type": "code_comparison", "variants": ["class UserParser (OOP)", "def parse_user_id (functional)"], "sharedResult": "All tests pass", "caption": "What's locked is the behavior. The code is flexible; the contract is fixed."}, {"id": "compression_ratio", "type": "size_comparison", "ratio": "1:5 to 1:10", "promptLines": 12, "codeLines": 200, "contextAdvantage": "5-10×", "leftWindow": {"tokens": 15000, "content": "raw code"}, "rightWindow": {"tokens": 15000, "content": "10 module prompts"}}], "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_008"]}, "overlayConfig": null, "renderMode": "raw-media"},
  "09_grounding_feedback_loop": {"specBaseName": "09_grounding_feedback_loop", "dataPoints": {"type": "veo_clip", "clipId": "grounding_feedback_loop", "camera": {"framing": "close_up", "angle": "low_angle", "movement": "static_with_tilt", "dof": "shallow", "dutchAngle": 5, "slowMotion": true, "playbackRate": 0.5}, "lighting": {"key": {"color": "#D9944A", "type": "emissive_material"}, "fill": {"color": "#1E3A5F", "position": "overhead", "type": "industrial"}, "sparks": {"color": "#FFE4B5"}, "grade": "warm_industrial"}, "narrationSegments": ["part3_009"], "narrationTimingSeconds": {"start": 0.0, "end": 6.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "10_three_components_table": {"specBaseName": "10_three_components_table", "dataPoints": {"type": "summary_table", "tableId": "three_components", "rows": [{"component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#4A90D9"}, {"component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#5AAA6E"}, {"component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A", "emphasized": true}], "conflictRule": "When these conflict, tests win. Always.", "hierarchy": ["Tests", "Prompt", "Grounding"], "closingLine": "The code is output. The mold is what matters.", "backgroundColor": "#0A0F1A", "narrationSegments": ["part3_010"]}, "overlayConfig": null, "renderMode": "raw-media"},
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

export default Part3MoldThreePartsSection;
