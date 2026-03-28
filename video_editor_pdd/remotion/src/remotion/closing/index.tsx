import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Closing03PddTriangle } from "../Closing03PddTriangle";
import { Closing04DissolveRegenerateLoop } from "../Closing04DissolveRegenerateLoop";
import { Closing06TheBeat } from "../Closing06TheBeat";
import { Closing07FinalTitleCard } from "../Closing07FinalTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "03_pdd_triangle": Closing03PddTriangle,
  "04_dissolve_regenerate_loop": Closing04DissolveRegenerateLoop,
  "06_the_beat": Closing06TheBeat,
  "07_final_title_card": Closing07FinalTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "03_pdd_triangle": 180,
  "04_dissolve_regenerate_loop": 150,
  "06_the_beat": 60,
  "07_final_title_card": 180,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_veo_sock_discard": { defaultSrc: "veo/sock_discard_callback.mp4", backgroundSrc: "veo/sock_discard_callback.mp4", outputSrc: "veo/sock_discard_callback.mp4", baseSrc: "veo/sock_discard_callback.mp4" },
  "02_veo_developer_regenerate": { defaultSrc: "veo/developer_regenerate_closing.mp4", backgroundSrc: "veo/developer_regenerate_closing.mp4", outputSrc: "veo/developer_regenerate_closing.mp4", baseSrc: "veo/developer_regenerate_closing.mp4" },
  "05_veo_mold_glow_finale": { defaultSrc: "veo/mold_glow_finale.mp4", backgroundSrc: "veo/mold_glow_finale.mp4", outputSrc: "veo/mold_glow_finale.mp4", baseSrc: "veo/mold_glow_finale.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean | number>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_veo_sock_discard": {"specBaseName": "01_veo_sock_discard", "dataPoints": {"type": "veo_clip", "clipId": "sock_discard_callback", "durationSeconds": 3, "narrationSegments": ["closing_001"], "characters": []}, "mediaAliases": {"defaultSrc": "veo/sock_discard_callback.mp4", "backgroundSrc": "veo/sock_discard_callback.mp4", "outputSrc": "veo/sock_discard_callback.mp4", "baseSrc": "veo/sock_discard_callback.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "02_veo_developer_regenerate": {"specBaseName": "02_veo_developer_regenerate", "dataPoints": {"type": "veo_clip", "clipId": "developer_regenerate_closing", "durationSeconds": 4, "narrationSegments": ["closing_002"], "characters": [{"id": "developer_protagonist", "label": "Developer", "referencePrompt": "A 30-something software developer, gender-neutral, wearing a dark henley shirt. Modern desk with mechanical keyboard and single ultrawide monitor. Cool blue-white lighting from LED desk lamp and monitor glow."}]}, "mediaAliases": {"defaultSrc": "veo/developer_regenerate_closing.mp4", "backgroundSrc": "veo/developer_regenerate_closing.mp4", "outputSrc": "veo/developer_regenerate_closing.mp4", "baseSrc": "veo/developer_regenerate_closing.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "03_pdd_triangle": {"specBaseName": "03_pdd_triangle", "dataPoints": {"type": "remotion_animation", "componentId": "pdd_triangle", "durationFrames": 180, "fps": 30, "narrationSegments": ["closing_002", "closing_003"], "vertices": [{"label": "PROMPT", "position": [960, 180], "color": "#D9944A"}, {"label": "TESTS", "position": [683, 680], "color": "#4AD9A0"}, {"label": "GROUNDING", "position": [1237, 680], "color": "#4A90D9"}], "codeLines": ["def calculate_total(items):", "    return sum(i.price for i in items)", "", "def apply_discount(total, pct):", "    return total * (1 - pct)"]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "04_dissolve_regenerate_loop": {"specBaseName": "04_dissolve_regenerate_loop", "dataPoints": {"type": "remotion_animation", "componentId": "dissolve_regenerate_loop", "durationFrames": 150, "fps": 30, "narrationSegments": ["closing_003", "closing_004"], "codeVariants": [{"version": 1, "lines": ["def calculate_total(items):", "    return sum(i.price for i in items)", "", "def apply_discount(total, pct):", "    return total * (1 - pct)"]}, {"version": 2, "lines": ["def get_total(cart_items):", "    total = 0", "    for item in cart_items:", "        total += item.price", "    return total"]}, {"version": 3, "lines": ["def compute_sum(products):", "    prices = [p.price for p in products]", "    return functools.reduce(", "        operator.add, prices, 0", "    )"]}], "terminalCommands": [{"command": "pdd test", "result": "✓ All tests passed"}]}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "05_veo_mold_glow_finale": {"specBaseName": "05_veo_mold_glow_finale", "dataPoints": {"type": "veo_clip", "clipId": "mold_glow_finale", "durationSeconds": 4, "narrationSegments": ["closing_004", "closing_005"], "characters": []}, "mediaAliases": {"defaultSrc": "veo/mold_glow_finale.mp4", "backgroundSrc": "veo/mold_glow_finale.mp4", "outputSrc": "veo/mold_glow_finale.mp4", "baseSrc": "veo/mold_glow_finale.mp4"}, "overlayConfig": null, "renderMode": "raw-media"},
  "06_the_beat": {"specBaseName": "06_the_beat", "dataPoints": {"type": "remotion_animation", "componentId": "the_beat", "durationFrames": 60, "fps": 30, "narrationSegments": [], "note": "Silent pause between final narration and title card"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
  "07_final_title_card": {"specBaseName": "07_final_title_card", "dataPoints": {"type": "title_card", "componentId": "final_title_card", "durationFrames": 180, "fps": 30, "narrationSegments": [], "title": "Prompt-Driven Development", "commands": ["uv tool install pdd-cli", "pdd update your_module.py"], "url": "promptdrivendevelopment.com"}, "mediaAliases": {}, "overlayConfig": null, "renderMode": "component"},
};

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 15.42;
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
