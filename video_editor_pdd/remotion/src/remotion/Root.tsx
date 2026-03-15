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
import { VeoSection03WaveDataOverlay } from "./VeoSection03WaveDataOverlay";
import { VeoSection04SplitNatureComparison } from "./VeoSection04SplitNatureComparison";
import { VeoSection05VeoPipelineInfographic } from "./VeoSection05VeoPipelineInfographic";
import { VeoSection07NarrationOverlayIntro } from "./VeoSection07NarrationOverlayIntro";
import { VeoSection08SectionEndCard } from "./VeoSection08SectionEndCard";

const PREVIEW_VISUAL_MEDIA: Record<string, Record<string, string>> = {
  "veo_section:veo_section_01_title_card": { defaultSrc: "veo/veo_section.mp4", backgroundSrc: "veo/veo_section.mp4", outputSrc: "veo/veo_section.mp4", baseSrc: "veo/veo_section.mp4" },
  "veo_section:03_wave_data_overlay": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "veo_section:04_split_nature_comparison": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4", leftSrc: "veo/02_ocean_wave_sunset.mp4", rightSrc: "veo/06_aerial_forest_canopy.mp4", revealSrc: "veo/06_aerial_forest_canopy.mp4" },
  "veo_section:05_veo_pipeline_infographic": { defaultSrc: "veo/02_ocean_wave_sunset.mp4", backgroundSrc: "veo/02_ocean_wave_sunset.mp4", outputSrc: "veo/02_ocean_wave_sunset.mp4", baseSrc: "veo/02_ocean_wave_sunset.mp4" },
  "veo_section:07_narration_overlay_intro": { defaultSrc: "veo/06_aerial_forest_canopy.mp4", backgroundSrc: "veo/06_aerial_forest_canopy.mp4", outputSrc: "veo/06_aerial_forest_canopy.mp4", baseSrc: "veo/06_aerial_forest_canopy.mp4" },
  "veo_section:08_section_end_card": { defaultSrc: "veo/06_aerial_forest_canopy.mp4", backgroundSrc: "veo/06_aerial_forest_canopy.mp4", outputSrc: "veo/06_aerial_forest_canopy.mp4", baseSrc: "veo/06_aerial_forest_canopy.mp4" },
};

const PREVIEW_VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section:animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Animation Section", "subtitle": "Integration Test", "accentLineWidth": 320, "backgroundColor": "#0F172A", "titleColor": "#FFFFFF", "subtitleColor": "#94A3B8", "accentLineColor": "rgba(255, 255, 255, 0.8)"}, "overlayConfig": null},
  "animation_section:02_blue_circle_pulse": {"specBaseName": "02_blue_circle_pulse", "dataPoints": {"center": [960, 540], "baseRadius": 60, "pulseRadii": [80, 78], "color": "#3B82F6", "glowBlur": 30, "glowOffsetRadius": 20, "pulseCount": 2, "backgroundGradient": {"center": "#0F172A", "edge": "#020617"}}, "overlayConfig": null},
  "animation_section:03_circle_to_square_morph": {"specBaseName": "03_circle_to_square_morph", "dataPoints": {"center": [960, 540], "startShape": {"size": 120, "borderRadius": 60, "color": "#3B82F6"}, "endShape": {"size": 130, "borderRadius": 12, "color": "#6366F1"}, "ghostTrails": {"opacities": [0.6, 0.35, 0.15], "lagFrames": 3}}, "overlayConfig": null},
  "animation_section:04_square_slide_right": {"specBaseName": "04_square_slide_right", "dataPoints": {"startX": 960, "endX": 1440, "y": 540, "anticipationPx": 20, "overshootPx": 30, "shapeSize": 130, "borderRadius": 12, "shapeColor": "#6366F1", "streakMaxWidth": 280, "streakHeight": 6, "streakOpacity": 0.4, "scaleFactors": {"anticipation": 0.97, "slideStretch": 1.03, "normal": 1.0}}, "overlayConfig": null},
  "animation_section:05_split_comparison": {"specBaseName": "05_split_comparison", "dataPoints": {"leftPanel": {"background": "#1E3A5F", "shape": "circle", "shapeColor": "#3B82F6", "radius": 50, "label": "Before"}, "rightPanel": {"background": "#312E81", "shape": "roundedSquare", "shapeColor": "#6366F1", "size": 100, "borderRadius": 12, "label": "After"}, "divider": {"color": "#FFFFFF", "opacity": 0.6, "width": 2}, "float": {"amplitude": 5, "period": 20}}, "overlayConfig": null},
  "animation_section:06_particle_burst": {"specBaseName": "06_particle_burst", "dataPoints": {"origin": [960, 540], "particleCount": 40, "seed": 42, "colors": ["#3B82F6", "#6366F1", "#8B5CF6", "#E2E8F0"], "radiusRange": [3, 8], "speedRange": [200, 600], "maxDistance": 300, "fadeStartRatio": 0.6, "flash": {"maxRadius": 120, "contractedRadius": 60, "peakOpacity": 0.8, "color": "#FFFFFF"}}, "overlayConfig": null},
  "animation_section:07_section_outro": {"specBaseName": "07_section_outro", "dataPoints": {"checkmark": {"center": [960, 500], "path": "M 25 45 L 42 62 L 75 28", "color": "#22C55E", "strokeWidth": 6, "pathLength": 180, "shortLeg": 60, "longLeg": 120, "glowBlur": 20, "glowOpacity": 0.2}, "text": {"content": "Section Complete", "y": 600, "fontSize": 32, "fontWeight": 500, "maxOpacity": 0.9, "scaleFrom": 0.95}, "fadeToBlack": {"startFrame": 28, "targetColor": "#000000"}}, "overlayConfig": null},
  "animation_section:08_key_visual": {"specBaseName": "08_key_visual", "dataPoints": {"bars": [{"label": "A", "height": 300, "color": "#38BDF8"}, {"label": "B", "height": 420, "color": "#22C55E"}, {"label": "C", "height": 260, "color": "#38BDF8"}, {"label": "D", "height": 500, "color": "#22C55E"}], "barWidth": 120, "barGap": 30, "maxHeight": 500, "containerWidth": 600, "containerBottomY": 880, "barBorderRadius": "8px 8px 0 0", "staggerFrames": 3, "growDuration": 8, "backgroundColor": "#0A1628"}, "overlayConfig": null},
  "animation_section:09_split_summary": {"specBaseName": "09_split_summary", "dataPoints": {"leftBackground": "#0F172A", "leftOpacity": 0.9, "rightBackground": "#020617", "rightOpacity": 1.0, "divider": {"startX": 640, "endX": 720, "color": "#38BDF8", "width": 3, "glowBlur": 24, "glowOpacity": 0.3, "glowWidth": 20}, "label": {"text": "Split Summary", "x": 80, "y": 60, "fontSize": 20, "fontWeight": 600, "color": "#FFFFFF", "opacity": 0.7}}, "overlayConfig": null},
  "veo_section:veo_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Veo Section", "subtitle": "AI-Generated Cinematic Footage", "background": "#0B1120", "accent": "#C9A84C"}, "overlayConfig": null},
  "veo_section:03_wave_data_overlay": {"specBaseName": "03_wave_data_overlay", "dataPoints": {"waveform": {"amplitude": 0.8, "frequency": 1.2, "samples": 120}, "stats": [{"label": "Wave Height", "value": "0.8m", "icon": "wave"}, {"label": "Wave Period", "value": "6.2s", "icon": "clock"}, {"label": "Water Temp", "value": "22°C", "icon": "thermometer"}]}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "veo_section:04_split_nature_comparison": {"specBaseName": "04_split_nature_comparison", "dataPoints": {"panels": [{"side": "left", "label": "Ocean · Sunset", "source": "veo/04_veo_broll.mp4"}, {"side": "right", "label": "Forest · Canopy", "source": "veo/05_veo_cutaway.mp4"}], "divider_color": "#C9A84C"}, "overlayConfig": null},
  "veo_section:05_veo_pipeline_infographic": {"specBaseName": "05_veo_pipeline_infographic", "dataPoints": {"pipeline_steps": [{"label": "Prompt", "icon": "text", "x": 330}, {"label": "Veo AI", "icon": "sparkle", "x": 870}, {"label": "Clip", "icon": "film", "x": 1410}], "arrow_style": {"stroke": "#C9A84C", "dash_pattern": "8 4", "particle_count": 2}}, "overlayConfig": {"gradientOverlay": "bottom"}},
  "veo_section:07_narration_overlay_intro": {"specBaseName": "07_narration_overlay_intro", "dataPoints": {"caption": "It uses Veo-generated clips with narration overlay.", "words": ["It", "uses", "Veo-generated", "clips", "with", "narration", "overlay."], "word_timings_frames": [10, 17, 24, 31, 38, 45, 52], "waveform_bars": 5, "panel_height": 200, "active_color": "#C9A84C", "inactive_color": "rgba(255,255,255,0.5)"}, "overlayConfig": {"lowerThirdText": "It uses Veo-generated clips with narration overlay."}},
  "veo_section:08_section_end_card": {"specBaseName": "08_section_end_card", "dataPoints": {"title": "Veo Section Complete", "icon": "checkmark", "background": "#0B1120", "accent": "#C9A84C", "checkmark_size": 80, "rule_width": 200}, "overlayConfig": null},
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
const VeoSection03WaveDataOverlayPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:03_wave_data_overlay"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:03_wave_data_overlay"] ?? null}>
      <VeoSection03WaveDataOverlay />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection04SplitNatureComparisonPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:04_split_nature_comparison"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:04_split_nature_comparison"] ?? null}>
      <VeoSection04SplitNatureComparison />
    </VisualMediaProvider>
  </VisualContractProvider>
);
const VeoSection05VeoPipelineInfographicPreview: React.FC = () => (
  <VisualContractProvider contract={PREVIEW_VISUAL_CONTRACTS["veo_section:05_veo_pipeline_infographic"] ?? null}>
    <VisualMediaProvider media={PREVIEW_VISUAL_MEDIA["veo_section:05_veo_pipeline_infographic"] ?? null}>
      <VeoSection05VeoPipelineInfographic />
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
        durationInFrames={238}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="VeoSection"
        component={VeoSectionSection}
        durationInFrames={239}
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
        id="veo-section03-wave-data-overlay"
        component={VeoSection03WaveDataOverlayPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section04-split-nature-comparison"
        component={VeoSection04SplitNatureComparisonPreview}
        durationInFrames={PREVIEW_DURATION}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="veo-section05-veo-pipeline-infographic"
        component={VeoSection05VeoPipelineInfographicPreview}
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
