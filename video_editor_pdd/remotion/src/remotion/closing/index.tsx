import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedContractVisual } from "../_shared/GeneratedContractVisual";
import { Closing04PddTriangle } from "../Closing04PddTriangle";
import { Closing05DissolveRegenerateLoop } from "../Closing05DissolveRegenerateLoop";
import { Closing06MoldGlowFinale } from "../Closing06MoldGlowFinale";
import { Closing07TheBeat } from "../Closing07TheBeat";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "04_pdd_triangle": Closing04PddTriangle,
  "05_dissolve_regenerate_loop": Closing05DissolveRegenerateLoop,
  "06_mold_glow_finale": Closing06MoldGlowFinale,
  "07_the_beat": Closing07TheBeat,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "04_pdd_triangle": 150,
  "05_dissolve_regenerate_loop": 240,
  "06_mold_glow_finale": 240,
  "07_the_beat": 120,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_sock_discard_callback": { defaultSrc: "veo/sock_discard_callback.mp4", backgroundSrc: "veo/sock_discard_callback.mp4", outputSrc: "veo/sock_discard_callback.mp4", baseSrc: "veo/sock_discard_callback.mp4" },
  "02_developer_regenerate_clip": { defaultSrc: "veo/developer_regenerate_closing.mp4", backgroundSrc: "veo/developer_regenerate_closing.mp4", outputSrc: "veo/developer_regenerate_closing.mp4", baseSrc: "veo/developer_regenerate_closing.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
  "08_final_title_card": { fadeOutFrames: 20 },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_sock_discard_callback": {"specBaseName": "01_sock_discard_callback", "dataPoints": {"type": "veo_clip", "clipId": "sock_discard_callback", "durationSeconds": 3, "narrationSegments": ["closing_001"]}, "mediaAliases": {"defaultSrc": "veo/sock_discard_callback.mp4", "backgroundSrc": "veo/sock_discard_callback.mp4", "outputSrc": "veo/sock_discard_callback.mp4", "baseSrc": "veo/sock_discard_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "02_developer_regenerate_clip": {"specBaseName": "02_developer_regenerate_clip", "dataPoints": {"type": "veo_clip", "clipId": "developer_regenerate_closing", "durationSeconds": 4, "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "A developer in their late 20s wearing a dark henley shirt, sitting at a modern desk with a mechanical keyboard and ultrawide monitor. Relaxed posture, warm desk lamp nearby."}], "narrationSegments": ["closing_001", "closing_002"]}, "mediaAliases": {"defaultSrc": "veo/developer_regenerate_closing.mp4", "backgroundSrc": "veo/developer_regenerate_closing.mp4", "outputSrc": "veo/developer_regenerate_closing.mp4", "baseSrc": "veo/developer_regenerate_closing.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_pdd_bug_fix_terminal": {"specBaseName": "03_pdd_bug_fix_terminal", "dataPoints": {"type": "terminal_animation", "commands": [{"cmd": "pdd bug email_validator", "output": "Test added: test_rejects_unicode_homoglyphs"}, {"cmd": "pdd fix email_validator", "output": "Regenerating... ✓ All tests pass"}], "terminalBg": "#111827", "backgroundColor": "#0A0F1A", "successColor": "#22C55E", "durationSeconds": 5, "narrationSegments": ["closing_001", "closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": {"type": "triangle_diagram", "vertices": [{"label": "PROMPT", "subtitle": "encode intent", "color": "#4A90D9", "position": [960, 200]}, {"label": "TESTS", "subtitle": "preserve behavior", "color": "#D9944A", "position": [520, 720]}, {"label": "GROUNDING", "subtitle": "maintain style", "color": "#5AAA6E", "position": [1400, 720]}], "edgeColor": "#334155", "centerCode": true, "backgroundColor": "#0A0F1A", "durationSeconds": 5, "narrationSegments": ["closing_002"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": {"type": "dissolve_regenerate_loop", "cycles": 2, "codeVariations": 2, "trianglePersists": true, "triangleOpacity": 0.3, "particleCount": "2-3 per character", "backgroundColor": "#0A0F1A", "successColor": "#22C55E", "durationSeconds": 5, "narrationSegments": ["closing_003"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": {"type": "mold_glow_diagram", "vertices": [{"label": "PROMPT", "color": "#4A90D9", "glowRadius": 20}, {"label": "TESTS", "color": "#D9944A", "glowRadius": 20}, {"label": "GROUNDING", "color": "#5AAA6E", "glowRadius": 20}], "codeOpacity": 0.2, "moldOverlay": true, "backgroundColor": "#0A0F1A", "durationSeconds": 4, "narrationSegments": ["closing_004"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": {"type": "dramatic_beat", "content": "empty", "backgroundFrom": "#0A0F1A", "backgroundTo": "#050810", "durationSeconds": 2, "narrationSegments": ["closing_005"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "08_final_title_card": {"specBaseName": "08_final_title_card", "dataPoints": {"type": "final_title_card", "title": "Prompt-Driven Development", "url": "promptdrivendevelopment.com", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "titleColor": "#E2E8F0", "titleGlow": "#4A90D9", "backgroundColor": "#0A0F1A", "commandBg": "#111827", "durationSeconds": 6, "narrationSegments": []}, "mediaAliases": {}, "overlayConfig": {"fadeOutFrames": 20}, "renderMode": "generated-media"},
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
