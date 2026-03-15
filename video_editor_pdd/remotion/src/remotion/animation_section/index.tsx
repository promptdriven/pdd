import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { AnimationSection01TitleCard } from "../AnimationSection01TitleCard";
import { AnimationSection02BlueCirclePulse } from "../AnimationSection02BlueCirclePulse";
import { AnimationSection03CircleToSquareMorph } from "../AnimationSection03CircleToSquareMorph";
import { AnimationSection04SquareSlideRight } from "../AnimationSection04SquareSlideRight";
import { AnimationSection05SplitComparison } from "../AnimationSection05SplitComparison";
import { AnimationSection06ParticleBurst } from "../AnimationSection06ParticleBurst";
import { AnimationSection07SectionOutro } from "../AnimationSection07SectionOutro";
import { AnimationSection08KeyVisual } from "../AnimationSection08KeyVisual";
import { AnimationSection09SplitSummary } from "../AnimationSection09SplitSummary";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "animation_section_01_title_card": AnimationSection01TitleCard,
  "02_blue_circle_pulse": AnimationSection02BlueCirclePulse,
  "03_circle_to_square_morph": AnimationSection03CircleToSquareMorph,
  "04_square_slide_right": AnimationSection04SquareSlideRight,
  "05_split_comparison": AnimationSection05SplitComparison,
  "06_particle_burst": AnimationSection06ParticleBurst,
  "07_section_outro": AnimationSection07SectionOutro,
  "08_key_visual": AnimationSection08KeyVisual,
  "09_split_summary": AnimationSection09SplitSummary,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "animation_section_01_title_card": 45,
  "02_blue_circle_pulse": 30,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Animation Section", "subtitle": "Integration Test", "accentLineWidth": 320, "backgroundColor": "#0F172A", "titleColor": "#FFFFFF", "subtitleColor": "#94A3B8", "accentLineColor": "rgba(255, 255, 255, 0.8)"}, "overlayConfig": null},
  "02_blue_circle_pulse": {"specBaseName": "02_blue_circle_pulse", "dataPoints": {"center": [960, 540], "baseRadius": 60, "pulseRadii": [80, 78], "color": "#3B82F6", "glowBlur": 30, "glowOffsetRadius": 20, "pulseCount": 2, "backgroundGradient": {"center": "#0F172A", "edge": "#020617"}}, "overlayConfig": null},
  "03_circle_to_square_morph": {"specBaseName": "03_circle_to_square_morph", "dataPoints": {"center": [960, 540], "startShape": {"size": 120, "borderRadius": 60, "color": "#3B82F6"}, "endShape": {"size": 130, "borderRadius": 12, "color": "#6366F1"}, "ghostTrails": {"opacities": [0.6, 0.35, 0.15], "lagFrames": 3}}, "overlayConfig": null},
  "04_square_slide_right": {"specBaseName": "04_square_slide_right", "dataPoints": {"startX": 960, "endX": 1440, "y": 540, "anticipationPx": 20, "overshootPx": 30, "shapeSize": 130, "borderRadius": 12, "shapeColor": "#6366F1", "streakMaxWidth": 280, "streakHeight": 6, "streakOpacity": 0.4, "scaleFactors": {"anticipation": 0.97, "slideStretch": 1.03, "normal": 1.0}}, "overlayConfig": null},
  "05_split_comparison": {"specBaseName": "05_split_comparison", "dataPoints": {"leftPanel": {"background": "#1E3A5F", "shape": "circle", "shapeColor": "#3B82F6", "radius": 50, "label": "Before"}, "rightPanel": {"background": "#312E81", "shape": "roundedSquare", "shapeColor": "#6366F1", "size": 100, "borderRadius": 12, "label": "After"}, "divider": {"color": "#FFFFFF", "opacity": 0.6, "width": 2}, "float": {"amplitude": 5, "period": 20}}, "overlayConfig": null},
  "06_particle_burst": {"specBaseName": "06_particle_burst", "dataPoints": {"origin": [960, 540], "particleCount": 40, "seed": 42, "colors": ["#3B82F6", "#6366F1", "#8B5CF6", "#E2E8F0"], "radiusRange": [3, 8], "speedRange": [200, 600], "maxDistance": 300, "fadeStartRatio": 0.6, "flash": {"maxRadius": 120, "contractedRadius": 60, "peakOpacity": 0.8, "color": "#FFFFFF"}}, "overlayConfig": null},
  "07_section_outro": {"specBaseName": "07_section_outro", "dataPoints": {"checkmark": {"center": [960, 500], "path": "M 25 45 L 42 62 L 75 28", "color": "#22C55E", "strokeWidth": 6, "pathLength": 180, "shortLeg": 60, "longLeg": 120, "glowBlur": 20, "glowOpacity": 0.2}, "text": {"content": "Section Complete", "y": 600, "fontSize": 32, "fontWeight": 500, "maxOpacity": 0.9, "scaleFrom": 0.95}, "fadeToBlack": {"startFrame": 28, "targetColor": "#000000"}}, "overlayConfig": null},
  "08_key_visual": {"specBaseName": "08_key_visual", "dataPoints": {"bars": [{"label": "A", "height": 300, "color": "#38BDF8"}, {"label": "B", "height": 420, "color": "#22C55E"}, {"label": "C", "height": 260, "color": "#38BDF8"}, {"label": "D", "height": 500, "color": "#22C55E"}], "barWidth": 120, "barGap": 30, "maxHeight": 500, "containerWidth": 600, "containerBottomY": 880, "barBorderRadius": "8px 8px 0 0", "staggerFrames": 3, "growDuration": 8, "backgroundColor": "#0A1628"}, "overlayConfig": null},
  "09_split_summary": {"specBaseName": "09_split_summary", "dataPoints": {"leftBackground": "#0F172A", "leftOpacity": 0.9, "rightBackground": "#020617", "rightOpacity": 1.0, "divider": {"startX": 640, "endX": 720, "color": "#38BDF8", "width": 3, "glowBlur": 24, "glowOpacity": 0.3, "glowWidth": 20}, "label": {"text": "Split Summary", "x": 80, "y": 60, "fontSize": 20, "fontWeight": 600, "color": "#FFFFFF", "opacity": 0.7}}, "overlayConfig": null},
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.914667;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("animation_section/narration.wav")} />
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
            ) : null}
          </Sequence>
        );
      })}
    </Sequence>
  );
};

export default AnimationSectionSection;
