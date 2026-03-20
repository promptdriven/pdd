import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { Closing01SockCallbackSplit } from "../Closing01SockCallbackSplit";
import { Closing03CodeRegenerateWorkflow } from "../Closing03CodeRegenerateWorkflow";
import { Closing04PddTriangle } from "../Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "../Closing05DissolveRegenerateLoop";
import { Closing06MoldGlowFinale } from "../Closing06MoldGlowFinale";
import { Closing07TheBeat } from "../Closing07TheBeat";
import { Closing08MoldIsWhatMatters } from "../Closing08MoldIsWhatMatters";
import { Closing09FinalTitleCard } from "../Closing09FinalTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_sock_callback_split": Closing01SockCallbackSplit,
  "03_code_regenerate_workflow": Closing03CodeRegenerateWorkflow,
  "04_pdd_triangle": Closing04PddTriangle,
  "05_dissolve_regenerate_loop": Closing05DissolveRegenerateLoop,
  "06_mold_glow_finale": Closing06MoldGlowFinale,
  "07_the_beat": Closing07TheBeat,
  "08_mold_is_what_matters": Closing08MoldIsWhatMatters,
  "09_final_title_card": Closing09FinalTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_sock_callback_split": 240,
  "03_code_regenerate_workflow": 300,
  "04_pdd_triangle": 300,
  "05_dissolve_regenerate_loop": 240,
  "06_mold_glow_finale": 240,
  "07_the_beat": 120,
  "08_mold_is_what_matters": 180,
  "09_final_title_card": 240,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_sock_callback_split": { leftSrc: "veo/sock_final_discard.mp4", defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "02_sock_discard_veo": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "03_code_regenerate_workflow": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "04_pdd_triangle": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "05_dissolve_regenerate_loop": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "06_mold_glow_finale": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "07_the_beat": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "08_mold_is_what_matters": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
  "09_final_title_card": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "01_sock_callback_split": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_sock_callback_split": {"specBaseName": "01_sock_callback_split", "dataPoints": {"type": "split_screen", "layout": "vertical_split", "splitPosition": 960, "leftPanel": {"label": "DISCARD", "content": "sock_final_discard_veo", "colorGrade": {"color": "#D4A043", "opacity": 0.03}, "costLabel": "$2", "costSubLabel": "new pair", "background": "#000000"}, "rightPanel": {"label": "REGENERATE", "content": "code_regenerate_callback_veo", "colorGrade": {"color": "#4A90D9", "opacity": 0.02}, "costLabel": "~30s", "costSubLabel": "regenerated", "terminalSnippet": "pdd bug → pdd fix → ✓", "background": "#000000"}, "embeddedVeoClips": ["sock_final_discard", "code_regenerate_callback"], "backgroundColor": "#000000", "narrationSegments": ["closing_001"]}, "overlayConfig": {"gradientOverlay": "bottom"}, "renderMode": "component"},
  "02_sock_discard_veo": {"specBaseName": "02_sock_discard_veo", "dataPoints": {"type": "veo_clip", "clipId": "sock_final_discard", "camera": {"framing": "close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#E8D5B8", "position": "overhead", "type": "household"}, "fill": "ambient", "grade": "warm_neutral"}, "embeddedIn": "01_sock_callback_split", "panel": "left", "narrationSegments": ["closing_001a"], "narrationTimingSeconds": {"start": 1455.0, "end": 1461.0}}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_code_regenerate_workflow": {"specBaseName": "03_code_regenerate_workflow", "dataPoints": {"type": "terminal_demo", "demoId": "closing_regenerate_workflow", "zones": {"codeBlock": {"file": "user_parser.py", "language": "python", "bugLine": 12, "action": "dissolve_and_regenerate"}, "testPanel": {"file": "test_user_parser.py", "existingTests": 4, "newTest": "test_null_injection", "finalStatus": "all_pass"}, "terminal": {"commands": ["pdd bug user_parser", "pdd fix user_parser"], "finalOutput": "All tests passing."}}, "annotation": "Never opened the file.", "backgroundColor": "#0A1628", "narrationSegments": ["closing_002"]}, "overlayConfig": null, "renderMode": "component"},
  "04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "geometric_diagram", "diagramId": "pdd_triangle", "shape": "equilateral_triangle", "center": [960, 520], "sideLength": 500, "nodes": [{"id": "prompt", "label": "PROMPT", "descriptor": "Encodes intent", "position": "top", "coordinates": [960, 280], "color": "#4A90D9"}, {"id": "tests", "label": "TESTS", "descriptor": "Preserve behavior", "position": "bottom_left", "coordinates": [710, 713], "color": "#D9944A"}, {"id": "grounding", "label": "GROUNDING", "descriptor": "Maintains style", "position": "bottom_right", "coordinates": [1210, 713], "color": "#5AAA6E"}], "centerContent": "generated_code_lines", "backgroundColor": "#0A1225", "narrationSegments": ["closing_003"]}, "overlayConfig": null, "renderMode": "component"},
  "05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "animated_loop", "diagramId": "dissolve_regenerate_loop", "baseTriangle": "pdd_triangle", "cycles": [{"id": 1, "duration_frames": 60, "speed": "slow"}, {"id": 2, "duration_frames": 50, "speed": "medium"}, {"id": 3, "duration_frames": 40, "speed": "fast"}], "particleEffect": {"type": "radial_scatter", "particlesPerLine": [6, 5, 4], "driftRadius": [120, 100, 80]}, "terminalHeartbeat": {"command": "pdd generate", "successMark": "✓"}, "backgroundColor": "#0A1225", "narrationSegments": ["closing_004"]}, "overlayConfig": null, "renderMode": "component"},
  "06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": {"type": "animated_diagram", "diagramId": "mold_glow_finale", "baseTriangle": "pdd_triangle", "glowIntensification": {"edgeLayers": 3, "nodeGrowth": {"from": 20, "to": 24}, "nodeColors": {"prompt": {"from": "#4A90D9", "to": "#6AB0F0"}, "tests": {"from": "#D9944A", "to": "#F0B86A"}, "grounding": {"from": "#5AAA6E", "to": "#7CC98E"}}}, "codeDimming": {"from": 0.15, "to": 0.04}, "thesisText": "The code is just plastic.", "particleField": {"count": 35, "colors": ["#4A90D9", "#D9944A", "#5AAA6E"], "direction": "up"}, "backgroundColor": "#080E1A", "narrationSegments": ["closing_005"]}, "overlayConfig": null, "renderMode": "component"},
  "07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "dramatic_pause", "diagramId": "the_beat", "baseTriangle": "pdd_triangle", "ghostState": {"edgeOpacity": 0.08, "edgeWidth": 1, "nodeRadius": 12, "nodeOpacity": 0.06}, "singleParticle": {"from": [960, 650], "to": [960, 350], "glintY": 520, "glintPeakOpacity": 0.25}, "narration": null, "backgroundColor": "#060A12", "vignette": {"edgeOpacity": 0.5}, "narrationSegments": ["closing_006"]}, "overlayConfig": null, "renderMode": "component"},
  "08_mold_is_what_matters": {"specBaseName": "08_mold_is_what_matters", "dataPoints": {"type": "title_card", "diagramId": "mold_is_what_matters", "baseTriangle": "pdd_triangle", "triangleState": "reignited_peak", "centerContent": null, "nodes": {"prompt": {"color": "#6AB0F0", "glowColor": "#4A90D9", "glowOpacity": 0.15}, "tests": {"color": "#F0B86A", "glowColor": "#D9944A", "glowOpacity": 0.15}, "grounding": {"color": "#7CC98E", "glowColor": "#5AAA6E", "glowOpacity": 0.15}}, "thesisText": "The mold is what matters.", "backgroundColor": "#060A12", "narrationSegments": ["closing_007"]}, "overlayConfig": null, "renderMode": "component"},
  "09_final_title_card": {"specBaseName": "09_final_title_card", "dataPoints": {"type": "title_card", "cardId": "final_title_card", "title": "Prompt-Driven Development", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "url": "pdd.dev", "ghostTriangle": {"edgeOpacity": 0.04, "nodeOpacity": 0.02}, "backgroundColor": "#060A12", "narrationSegments": ["closing_008"]}, "overlayConfig": null, "renderMode": "component"},
};

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 20.66;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("closing/narration.wav")} />
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

export default ClosingSection;
