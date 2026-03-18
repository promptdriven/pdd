import React from "react";
import { Sequence, useCurrentFrame, OffthreadVideo, staticFile } from "remotion";
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
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "01_sock_callback_split": { defaultSrc: "veo/sock_final_discard.mp4", backgroundSrc: "veo/sock_final_discard.mp4", outputSrc: "veo/sock_final_discard.mp4", baseSrc: "veo/sock_final_discard.mp4" },
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
  "01_sock_callback_split": {"specBaseName": "01_sock_callback_split", "dataPoints": null, "overlayConfig": {"gradientOverlay": "bottom"}},
  "02_sock_discard_veo": {"specBaseName": "02_sock_discard_veo", "dataPoints": null, "overlayConfig": null},
  "03_code_regenerate_workflow": {"specBaseName": "03_code_regenerate_workflow", "dataPoints": null, "overlayConfig": null},
  "04_pdd_triangle": {"specBaseName": "04_pdd_triangle", "dataPoints": null, "overlayConfig": null},
  "05_dissolve_regenerate_loop": {"specBaseName": "05_dissolve_regenerate_loop", "dataPoints": null, "overlayConfig": null},
  "06_mold_glow_finale": {"specBaseName": "06_mold_glow_finale", "dataPoints": null, "overlayConfig": null},
  "07_the_beat": {"specBaseName": "07_the_beat", "dataPoints": null, "overlayConfig": null},
  "08_mold_is_what_matters": {"specBaseName": "08_mold_is_what_matters", "dataPoints": null, "overlayConfig": null},
  "09_final_title_card": {"specBaseName": "09_final_title_card", "dataPoints": null, "overlayConfig": null},
};

export const ClosingSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 20.992;
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

export default ClosingSection;
