import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02KeyVisual } from "./animation_section_02_key_visual";
import { AnimationSection03SplitSummary } from "./animation_section_03_split_summary";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection02KeyVisual } from "./veo_section_02_key_visual";
import { VeoSection03SplitSummary } from "./veo_section_03_split_summary";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section:veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:veo_section_02_key_visual": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:veo_section_03_split_summary": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section:animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "animation_section:animation_section_02_key_visual": {"specBaseName": "02_key_visual", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "animation_section:animation_section_03_split_summary": {"specBaseName": "03_split_summary", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "veo_section:veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "veo_section:veo_section_02_key_visual": {"specBaseName": "02_key_visual", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
  "veo_section:veo_section_03_split_summary": {"specBaseName": "03_split_summary", "dataPoints": {"series": [{"label": "A", "value": 1}, {"label": "B", "value": 2}]}, "overlayConfig": null, "renderMode": "component"},
};

const AnimationSection01TitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:animation_section_01_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:animation_section_01_title_card"] ?? null}>
      <AnimationSection01TitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection02KeyVisualPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:animation_section_02_key_visual"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:animation_section_02_key_visual"] ?? null}>
      <AnimationSection02KeyVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection03SplitSummaryPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:animation_section_03_split_summary"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:animation_section_03_split_summary"] ?? null}>
      <AnimationSection03SplitSummary />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection01TitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:veo_section_01_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_01_title_card"] ?? null}>
      <VeoSection01TitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection02KeyVisualPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:veo_section_02_key_visual"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_02_key_visual"] ?? null}>
      <VeoSection02KeyVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection03SplitSummaryPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:veo_section_03_split_summary"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:veo_section_03_split_summary"] ?? null}>
      <VeoSection03SplitSummary />
    </VisualMediaProvider>
  </VisualContractProvider>
);

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={214}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={214}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section01-title-card"
        component={AnimationSection01TitleCardPreview}
        durationInFrames={45}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section02-key-visual"
        component={AnimationSection02KeyVisualPreview}
        durationInFrames={150}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="animation-section03-split-summary"
        component={AnimationSection03SplitSummaryPreview}
        durationInFrames={150}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section01-title-card"
        component={VeoSection01TitleCardPreview}
        durationInFrames={51}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section02-key-visual"
        component={VeoSection02KeyVisualPreview}
        durationInFrames={150}
        fps={30}
        width={1280}
        height={720}
      />
      <Composition
        id="veo-section03-split-summary"
        component={VeoSection03SplitSummaryPreview}
        durationInFrames={150}
        fps={30}
        width={1280}
        height={720}
      />
    </>
  );
};
