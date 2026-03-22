import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen06CodeBlinkPatched } from "../ColdOpen06CodeBlinkPatched";
import { ColdOpen07CodeRegeneration } from "../ColdOpen07CodeRegeneration";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "06_code_blink_patched": ColdOpen06CodeBlinkPatched,
  "07_code_regeneration": ColdOpen07CodeRegeneration,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_split_screen_hook": 240,
  "06_code_blink_patched": 150,
  "07_code_regeneration": 270,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_split_screen_hook": { defaultSrc: "veo/developer_ai_edit.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4" },
  "02_developer_ai_edit": { defaultSrc: "veo/developer_ai_edit.mp4", backgroundSrc: "veo/developer_ai_edit.mp4", outputSrc: "veo/developer_ai_edit.mp4", baseSrc: "veo/developer_ai_edit.mp4" },
  "03_grandmother_darning": { defaultSrc: "veo/grandmother_darning.mp4", backgroundSrc: "veo/grandmother_darning.mp4", outputSrc: "veo/grandmother_darning.mp4", baseSrc: "veo/grandmother_darning.mp4" },
  "05_sock_toss": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "06_code_blink_patched": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
  "07_code_regeneration": { defaultSrc: "veo/sock_toss.mp4", backgroundSrc: "veo/sock_toss.mp4", outputSrc: "veo/sock_toss.mp4", baseSrc: "veo/sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": {"type": "split_screen", "layout": "vertical_50_50", "leftClipId": "developer_ai_edit", "rightClipId": "grandmother_darning", "divider": {"width": 1, "color": "#FFFFFF20"}}, "overlayConfig": null, "renderMode": "component"},
  "02_developer_ai_edit": {"specBaseName": "02_developer_ai_edit", "dataPoints": {"type": "veo_clip", "clipId": "developer_ai_edit", "characters": [{"id": "developer", "label": "Developer", "referencePrompt": "Modern software developer, late 20s to early 30s, casual clothing, sitting at a desk with a large monitor in a dark room lit by screen glow, mechanical keyboard"}]}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_grandmother_darning": {"specBaseName": "03_grandmother_darning", "dataPoints": {"type": "veo_clip", "clipId": "grandmother_darning", "characters": [{"id": "great_grandmother", "label": "Great-Grandmother", "referencePrompt": "Elderly woman with weathered hands, 1950s domestic setting, cotton housedress, reading glasses, warm amber lamplight, darning a sock"}]}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_sock_toss": {"specBaseName": "05_sock_toss", "dataPoints": {"type": "veo_clip", "clipId": "sock_toss"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_code_blink_patched": {"specBaseName": "06_code_blink_patched", "dataPoints": {"type": "code_editor", "language": "typescript", "theme": "vscode_dark", "annotations": [{"line": 4, "text": "// FIXME: edge case from PR #847", "color": "#F44747"}, {"line": 12, "text": "// patched — original logic broke on null", "color": "#F44747"}, {"line": 18, "text": "// TODO: refactor this entire block", "color": "#F4A347"}], "cursorPosition": {"line": 23, "column": 0}, "cursorBlinkMs": 530}, "overlayConfig": null, "renderMode": "component"},
  "07_code_regeneration": {"specBaseName": "07_code_regeneration", "dataPoints": {"type": "code_regeneration", "language": "typescript", "theme": "vscode_dark", "patchedLineCount": 23, "cleanLineCount": 16, "generationGlow": "#00D9FF15", "terminalCommand": "pdd generate", "streamRate": "2_lines_per_frame"}, "overlayConfig": null, "renderMode": "component"},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 17.54;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("cold_open/narration.wav")} />
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

export default ColdOpenSection;
