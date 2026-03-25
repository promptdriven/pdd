import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Closing03CodeRegenerateWorkflow } from "../Closing03CodeRegenerateWorkflow";
import { Closing04PddTriangle } from "../Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "../Closing05DissolveRegenerateLoop";
import { Closing07TheBeat } from "../Closing07TheBeat";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "02_code_regenerate_workflow": Closing03CodeRegenerateWorkflow,
  "04_pdd_triangle": Closing04PddTriangle,
  "05_dissolve_regenerate_loop": Closing05DissolveRegenerateLoop,
  "07_the_beat": Closing07TheBeat,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "02_code_regenerate_workflow": 300,
  "04_pdd_triangle": 210,
  "05_dissolve_regenerate_loop": 240,
  "07_the_beat": 120,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_sock_callback_discard": { defaultSrc: "veo/sock_discard_closing.mp4", backgroundSrc: "veo/sock_discard_closing.mp4", outputSrc: "veo/sock_discard_closing.mp4", baseSrc: "veo/sock_discard_closing.mp4" },
  "03_developer_regenerate_clip": { defaultSrc: "veo/code_regenerate_closing.mp4", backgroundSrc: "veo/code_regenerate_closing.mp4", outputSrc: "veo/code_regenerate_closing.mp4", baseSrc: "veo/code_regenerate_closing.mp4" },
  "06_mold_glow_finale": { defaultSrc: "veo/mold_glow_finale.mp4", backgroundSrc: "veo/mold_glow_finale.mp4", outputSrc: "veo/mold_glow_finale.mp4", baseSrc: "veo/mold_glow_finale.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_sock_callback_discard": {"specBaseName": "01_sock_callback_discard", "dataPoints": {"type": "veo_clip", "clipId": "sock_discard_closing", "camera": {"framing": "medium_close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "natural_daylight", "position": "upper_right", "type": "window"}, "fill": "ambient", "grade": "neutral_cool"}, "callbackTo": "part1_economics/sock_metaphor", "narrationSegments": ["closing_001"]}, "mediaAliases": {"defaultSrc": "veo/sock_discard_closing.mp4", "backgroundSrc": "veo/sock_discard_closing.mp4", "outputSrc": "veo/sock_discard_closing.mp4", "baseSrc": "veo/sock_discard_closing.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "02_code_regenerate_workflow": {"specBaseName": "02_code_regenerate_workflow", "dataPoints": {"type": "code_animation", "chartId": "code_regenerate_workflow", "phases": [{"id": "bug_highlight", "frame": 0, "description": "Buggy code with red highlight on line 7"}, {"id": "test_add", "frame": 30, "description": "New test_edge_case fades in"}, {"id": "terminal_commands", "frame": 60, "description": "pdd bug → pdd fix sequence"}, {"id": "dissolve_regen", "frame": 90, "description": "Code dissolves, regenerates clean"}, {"id": "all_pass", "frame": 120, "description": "All tests passing checkmark"}], "terminalCommands": ["pdd bug user_parser", "pdd fix user_parser", "✓ All tests passing"], "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_001", "closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "03_developer_regenerate_clip": {"specBaseName": "03_developer_regenerate_clip", "dataPoints": {"type": "veo_clip", "clipId": "code_regenerate_closing", "camera": {"framing": "over_the_shoulder", "movement": "static_with_drift", "dof": "shallow", "drift": true}, "lighting": {"key": {"color": "#B0C4DE", "position": "front", "type": "monitor_glow"}, "fill": {"color": "#2A1F14", "type": "ambient"}, "grade": "cool_neutral"}, "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "Developer seated at modern workstation, seen from behind, mechanical keyboard, monitor glow lighting"}], "narrationSegments": ["closing_001", "closing_002"]}, "mediaAliases": {"defaultSrc": "veo/code_regenerate_closing.mp4", "backgroundSrc": "veo/code_regenerate_closing.mp4", "outputSrc": "veo/code_regenerate_closing.mp4", "baseSrc": "veo/code_regenerate_closing.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "animated_diagram", "chartId": "pdd_triangle", "vertices": [{"id": "prompt", "label": "PROMPT", "position": [960, 200], "color": "#60A5FA", "descriptor": "encode intent"}, {"id": "tests", "label": "TESTS", "position": [480, 750], "color": "#4ADE80", "descriptor": "preserve behavior"}, {"id": "grounding", "label": "GROUNDING", "position": [1440, 750], "color": "#D9944A", "descriptor": "maintain style"}], "centerElement": {"type": "generated_code", "position": [960, 520], "font": "JetBrains Mono"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "animated_diagram", "chartId": "dissolve_regenerate_loop", "cycles": 3, "cycleTints": ["#60A5FA", "#4ADE80", "#D9944A"], "triangle": {"persistent": true, "source": "pdd_triangle"}, "terminal": {"command": "pdd generate", "successIndicator": "✓"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_003", "closing_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": {"type": "veo_clip", "clipId": "mold_glow_finale", "camera": {"framing": "close_up", "movement": "static", "dof": "moderate", "drift": false}, "lighting": {"key": {"color": "#D4A043", "position": "internal", "type": "practical_glow"}, "fill": "minimal", "rim": {"color": "#60A5FA", "opacity": 0.1}, "grade": "high_contrast_warm"}, "callbackTo": "part2_injection_mold", "narrationSegments": ["closing_004"]}, "mediaAliases": {"defaultSrc": "veo/mold_glow_finale.mp4", "backgroundSrc": "veo/mold_glow_finale.mp4", "outputSrc": "veo/mold_glow_finale.mp4", "baseSrc": "veo/mold_glow_finale.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "beat", "chartId": "the_beat", "startAnchor": {"type": "segmentEnd", "segmentId": "closing_004"}, "endAnchor": {"type": "segmentStart", "segmentId": "closing_005"}, "ghostElements": [{"source": "pdd_triangle", "opacity": 0.02}], "backgroundColor": "#0A0F1A", "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_final_title_card": {"specBaseName": "08_final_title_card", "dataPoints": {"type": "title_card", "chartId": "final_title_card", "title": "Prompt-Driven Development", "titleFont": {"family": "Inter", "size": 52, "weight": 700, "color": "#E2E8F0"}, "titleGlow": {"color": "#D9944A", "opacity": 0.08, "blur": 60}, "url": "promptdrivendevelopment.com", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "commandFont": {"family": "JetBrains Mono", "size": 16, "color": "#64748B"}, "ghostElements": [{"source": "pdd_triangle", "opacity": 0.03, "scale": 0.4}], "backgroundColor": "#0A0F1A", "narrationSegments": ["closing_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 20.66;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE
    .filter((visual) => frame >= visual.start && frame < visual.end)
    .slice()
    .sort((left, right) => ((left.lane ?? 0) - (right.lane ?? 0)) || (left.start - right.start));

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

export default ClosingSection;
