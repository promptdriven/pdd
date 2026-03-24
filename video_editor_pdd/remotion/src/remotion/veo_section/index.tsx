import React from "react";
import { Sequence, useCurrentFrame, Audio, OffthreadVideo, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { VeoSection01TitleCard } from "../VeoSection01TitleCard";
import { VeoSection02KeyVisual } from "../veo_section_02_key_visual";
import { VeoSection03SplitSummary } from "../veo_section_03_split_summary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "veo_section_01_title_card": VeoSection01TitleCard,
  "veo_section_02_key_visual": VeoSection02KeyVisual,
  "veo_section_03_split_summary": VeoSection03SplitSummary,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "veo_section_01_title_card": 51,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section_02_key_visual": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section_03_split_summary": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "04_veo_broll": { defaultSrc: "veo/04_veo_broll.mp4", backgroundSrc: "veo/04_veo_broll.mp4", outputSrc: "veo/04_veo_broll.mp4", baseSrc: "veo/04_veo_broll.mp4" },
  "05_veo_cutaway": { defaultSrc: "veo/05_veo_cutaway.mp4", backgroundSrc: "veo/05_veo_cutaway.mp4", outputSrc: "veo/05_veo_cutaway.mp4", baseSrc: "veo/05_veo_cutaway.mp4" },
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "veo_section_02_key_visual": {"specBaseName": "02_key_visual", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "veo_section_03_split_summary": {"specBaseName": "03_split_summary", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "04_veo_broll": {"specBaseName": "04_veo_broll", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "raw-media"},
  "05_veo_cutaway": {"specBaseName": "05_veo_cutaway", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "raw-media"},
};

export const VeoSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.12;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("veo_section/narration.wav")} />
      {activeVisuals.length === 0 ? <OffthreadVideo src={staticFile("veo_section.mp4")} style={{ width: "100%", height: "100%" }} /> : null}
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

export default VeoSectionSection;
