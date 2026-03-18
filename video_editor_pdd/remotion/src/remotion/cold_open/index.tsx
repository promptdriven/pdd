import React from "react";
import { Sequence, useCurrentFrame, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { GeneratedMediaVisual } from "../_shared/GeneratedMediaVisual";
import { ColdOpen01SplitScreenHook } from "../ColdOpen01SplitScreenHook";
import { ColdOpen02ZoomOutAccumulated } from "../ColdOpen02ZoomOutAccumulated";
import { ColdOpen05CodeBlink } from "../ColdOpen05CodeBlink";
import { ColdOpen06StillPatchingBeat } from "../ColdOpen06StillPatchingBeat";
import { ColdOpen07PddTitleCard } from "../ColdOpen07PddTitleCard";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_split_screen_hook": ColdOpen01SplitScreenHook,
  "02_zoom_out_accumulated": ColdOpen02ZoomOutAccumulated,
  "05_code_blink": ColdOpen05CodeBlink,
  "06_still_patching_beat": ColdOpen06StillPatchingBeat,
  "07_pdd_title_card": ColdOpen07PddTitleCard,
};

const VISUAL_DURATIONS: Record<string, number> = {
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "03_grandmother_lamplight": { defaultSrc: "veo/grandmother_darning_lamplight.mp4", backgroundSrc: "veo/grandmother_darning_lamplight.mp4", outputSrc: "veo/grandmother_darning_lamplight.mp4", baseSrc: "veo/grandmother_darning_lamplight.mp4" },
  "04_sock_toss": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "05_code_blink": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "06_still_patching_beat": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
  "07_pdd_title_card": { defaultSrc: "veo/modern_sock_toss.mp4", backgroundSrc: "veo/modern_sock_toss.mp4", outputSrc: "veo/modern_sock_toss.mp4", baseSrc: "veo/modern_sock_toss.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
  "01_split_screen_hook": { gradientOverlay: "bottom" },
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_split_screen_hook": {"specBaseName": "01_split_screen_hook", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "02_zoom_out_accumulated": {"specBaseName": "02_zoom_out_accumulated", "dataPoints": null, "overlayConfig": null},
  "03_grandmother_lamplight": {"specBaseName": "03_grandmother_lamplight", "dataPoints": null, "overlayConfig": null},
  "04_sock_toss": {"specBaseName": "04_sock_toss", "dataPoints": null, "overlayConfig": null},
  "05_code_blink": {"specBaseName": "05_code_blink", "dataPoints": null, "overlayConfig": null},
  "06_still_patching_beat": {"specBaseName": "06_still_patching_beat", "dataPoints": null, "overlayConfig": null},
  "07_pdd_title_card": {"specBaseName": "07_pdd_title_card", "dataPoints": null, "overlayConfig": null},
};

export const ColdOpenSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 0.362667;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
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

export default ColdOpenSection;
