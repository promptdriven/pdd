import React from "react";
import { Composition } from "remotion";
import { VisualMediaProvider, VisualContractProvider } from "./_shared/visual-runtime";
import "./_shared/load-inter-font";

import { AnimationSectionSection } from "./animation_section";
import { VeoSectionSection } from "./veo_section";
import { AnimationSection01TitleCard } from "./AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "./AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareMorph } from "./AnimationSection03CircleToSquareMorph";
import { AnimationSection04SquareSlideRight } from "./AnimationSection04SquareSlideRight";
import { AnimationSection05SplitComparison } from "./AnimationSection05SplitComparison";
import { AnimationSection06ParticleBurst } from "./AnimationSection06ParticleBurst";
import { AnimationSection07SectionOutro } from "./AnimationSection07SectionOutro";
import { AnimationSection08KeyVisual } from "./AnimationSection08KeyVisual";
import { AnimationSection09SplitSummary } from "./AnimationSection09SplitSummary";
import { VeoSection01TitleCard } from "./VeoSection01TitleCard";
import { VeoSection04WaveDataOverlay } from "./VeoSection04WaveDataOverlay";
import { VeoSection05SplitNatureComparison } from "./VeoSection05SplitNatureComparison";
import { VeoSection06VeoPipelineInfographic } from "./VeoSection06VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "./VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "./VeoSection08SectionEndCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section:veo_section_01_title_card": { defaultSrc: "veo_section.mp4", backgroundSrc: "veo_section.mp4", outputSrc: "veo_section.mp4", baseSrc: "veo_section.mp4" },
  "veo_section:04_wave_data_overlay": { defaultSrc: "veo/03_aerial_forest_canopy.mp4", backgroundSrc: "veo/03_aerial_forest_canopy.mp4", outputSrc: "veo/03_aerial_forest_canopy.mp4", baseSrc: "veo/03_aerial_forest_canopy.mp4" },
  "veo_section:05_split_nature_comparison": { leftSrc: "veo/02_ocean_wave_sunset.mp4", defaultSrc: "veo/02_ocean_wave_sunset.mp4", rightSrc: "veo/03_aerial_forest_canopy.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4", revealSrc: "veo/03_aerial_forest_canopy.mp4" },
  "veo_section:06_veo_pipeline_infographic": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "veo_section:07_narration_overlay_intro": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "veo_section:08_section_end_card": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section:animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Animation Section", "subtitle": "Integration Test"}, "overlayConfig": null},
  "animation_section:02_blue_circle_pulse": {"specBaseName": "02_blue_circle_pulse", "dataPoints": {"circle": {"centerX": 960, "centerY": 540, "baseRadius": 60, "pulseRadius": 80, "color": "#3B82F6"}, "glow": {"radius": 120, "color": "rgba(59, 130, 246, 0.2)"}}, "overlayConfig": null},
  "animation_section:03_circle_to_square_morph": {"specBaseName": "03_circle_to_square_morph", "dataPoints": {"shape": {"size": 120, "borderRadiusStart": 60, "borderRadiusEnd": 12, "colorStart": "#3B82F6", "colorEnd": "#6366F1"}, "ghostTrail": {"count": 3, "opacities": [0.15, 0.1, 0.05], "frameOffsets": [0, 4, 8]}}, "overlayConfig": null},
  "animation_section:04_square_slide_right": {"specBaseName": "04_square_slide_right", "dataPoints": {"slide": {"fromX": 960, "toX": 1440, "y": 540, "anticipationOffset": -10, "overshoot": 20, "streakMaxLength": 200}, "square": {"size": 120, "borderRadius": 12, "color": "#6366F1"}}, "overlayConfig": null},
  "animation_section:05_split_comparison": {"specBaseName": "05_split_comparison", "dataPoints": {"layout": {"panelWidth": 960, "dividerWidth": 2, "dividerMaxOpacity": 0.6}, "shapes": {"circle": {"x": 480, "y": 440, "radius": 80, "color": "#3B82F6"}, "square": {"x": 480, "y": 440, "size": 120, "borderRadius": 12, "color": "#6366F1"}}}, "overlayConfig": null},
  "animation_section:06_particle_burst": {"specBaseName": "06_particle_burst", "dataPoints": {"particles": {"count": 40, "minRadius": 4, "maxRadius": 8, "minDistance": 150, "maxDistance": 500, "angleJitter": 5, "seed": 42}, "flash": {"peakOpacity": 0.15}, "colorPalette": ["#3B82F6", "#6366F1", "#8B5CF6", "#FFFFFF"]}, "overlayConfig": null},
  "animation_section:07_section_outro": {"specBaseName": "07_section_outro", "dataPoints": {"checkmark": {"path": "M8 24 L20 36 L40 12", "pathLength": 48, "strokeColor": "#22C55E", "strokeWidth": 3, "size": 48, "centerX": 960, "centerY": 480}, "text": {"content": "Section Complete", "centerY": 560}}, "overlayConfig": null},
  "animation_section:08_key_visual": {"specBaseName": "08_key_visual", "dataPoints": {"bars": [{"value": 0.35, "maxHeight": 126, "color": "#38BDF8"}, {"value": 0.55, "maxHeight": 198, "color": "#22C55E"}, {"value": 0.8, "maxHeight": 288, "color": "#38BDF8"}, {"value": 0.6, "maxHeight": 216, "color": "#22C55E"}], "barWidth": 120, "barGap": 36, "containerHeight": 420, "barBaseHeight": 360}, "overlayConfig": null},
  "animation_section:09_split_summary": {"specBaseName": "09_split_summary", "dataPoints": {"divider": {"startX": 640, "endX": 720, "width": 6, "color": "#38BDF8"}, "panels": {"left": {"background": "#0F172A", "label": "Before"}, "right": {"background": "#111827", "label": "After"}}}, "overlayConfig": null},
  "veo_section:veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Veo Section", "subtitle": "AI-Generated Cinematic Footage", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
  "veo_section:04_wave_data_overlay": {"specBaseName": "04_wave_data_overlay", "dataPoints": {"wave_height_m": 0.8, "wave_period_s": 6.2, "water_temp_c": 22, "waveform": {"amplitude": 0.8, "frequency": 1.2, "samples": 120}}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "veo_section:05_split_nature_comparison": {"specBaseName": "05_split_nature_comparison", "dataPoints": {"left": {"label": "Ocean · Sunset", "source": "ocean_wave_sunset_still.jpg", "scene": "beach at golden hour"}, "right": {"label": "Forest · Canopy", "source": "aerial_forest_canopy_still.jpg", "scene": "aerial forest with dappled light"}}, "overlayConfig": null},
  "veo_section:06_veo_pipeline_infographic": {"specBaseName": "06_veo_pipeline_infographic", "dataPoints": {"pipeline_steps": [{"id": "prompt", "label": "Text Prompt", "color": "#6366F1", "icon": "text-cursor"}, {"id": "model", "label": "Veo Model", "color": "#8B5CF6", "icon": "brain"}, {"id": "output", "label": "Video Output", "color": "#10B981", "icon": "play"}], "arrows": [{"from": "prompt", "to": "model"}, {"from": "model", "to": "output"}]}, "overlayConfig": null},
  "veo_section:07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": {"narration_text": "Veo-generated clips with narration overlay", "word_count": 6, "waveform_bars": 40, "accent_color": "#C9A84C", "background_source": "ocean_wave_sunset_still.jpg"}, "overlayConfig": null},
  "veo_section:08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": {"title": "Veo Section Complete", "subtitle": "2 Veo clips · 3 Remotion overlays", "stats": {"veo_clips": 2, "remotion_overlays": 3}, "background": "#0B1120", "accent": "#C9A84C", "checkmark_color": "#10B981"}, "overlayConfig": null},
};

const AnimationSection01TitleCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:animation_section_01_title_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:animation_section_01_title_card"] ?? null}>
      <AnimationSection01TitleCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection02BlueCirclePulsePreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:02_blue_circle_pulse"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:02_blue_circle_pulse"] ?? null}>
      <AnimationSection02BlueCirclePulse />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection03CircleToSquareMorphPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:03_circle_to_square_morph"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:03_circle_to_square_morph"] ?? null}>
      <AnimationSection03CircleToSquareMorph />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection04SquareSlideRightPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:04_square_slide_right"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:04_square_slide_right"] ?? null}>
      <AnimationSection04SquareSlideRight />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection05SplitComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:05_split_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:05_split_comparison"] ?? null}>
      <AnimationSection05SplitComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection06ParticleBurstPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:06_particle_burst"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:06_particle_burst"] ?? null}>
      <AnimationSection06ParticleBurst />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection07SectionOutroPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:07_section_outro"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:07_section_outro"] ?? null}>
      <AnimationSection07SectionOutro />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection08KeyVisualPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:08_key_visual"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:08_key_visual"] ?? null}>
      <AnimationSection08KeyVisual />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const AnimationSection09SplitSummaryPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["animation_section:09_split_summary"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["animation_section:09_split_summary"] ?? null}>
      <AnimationSection09SplitSummary />
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
const VeoSection04WaveDataOverlayPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:04_wave_data_overlay"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:04_wave_data_overlay"] ?? null}>
      <VeoSection04WaveDataOverlay />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection05SplitNatureComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:05_split_nature_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:05_split_nature_comparison"] ?? null}>
      <VeoSection05SplitNatureComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection06VeoPipelineInfographicPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:06_veo_pipeline_infographic"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:06_veo_pipeline_infographic"] ?? null}>
      <VeoSection06VeoPipelineInfographic />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection07NarrationOverlayIntroPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:07_narration_overlay_intro"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:07_narration_overlay_intro"] ?? null}>
      <VeoSection07NarrationOverlayIntro />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection08SectionEndCardPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:08_section_end_card"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:08_section_end_card"] ?? null}>
      <VeoSection08SectionEndCard />
    </VisualMediaProvider>
  </VisualContractProvider>
);

const PREVIEW_DURATION = 150; // 5s at 30fps

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="AnimationSection"
        component={AnimationSectionSection}
        durationInFrames={234}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={235}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section01-title-card"
        component={AnimationSection01TitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section02-blue-circle-pulse"
        component={AnimationSection02BlueCirclePulsePreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section03-circle-to-square-morph"
        component={AnimationSection03CircleToSquareMorphPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section04-square-slide-right"
        component={AnimationSection04SquareSlideRightPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section05-split-comparison"
        component={AnimationSection05SplitComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section06-particle-burst"
        component={AnimationSection06ParticleBurstPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section07-section-outro"
        component={AnimationSection07SectionOutroPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section08-key-visual"
        component={AnimationSection08KeyVisualPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="animation-section09-split-summary"
        component={AnimationSection09SplitSummaryPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section01-title-card"
        component={VeoSection01TitleCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section04-wave-data-overlay"
        component={VeoSection04WaveDataOverlayPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section05-split-nature-comparison"
        component={VeoSection05SplitNatureComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section06-veo-pipeline-infographic"
        component={VeoSection06VeoPipelineInfographicPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section07-narration-overlay-intro"
        component={VeoSection07NarrationOverlayIntroPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section08-section-end-card"
        component={VeoSection08SectionEndCardPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
