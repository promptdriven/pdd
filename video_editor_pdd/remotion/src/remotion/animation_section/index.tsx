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
  "07_section_outro": 21,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "animation_section_01_title_card": {"specBaseName": "01_title_card", "dataPoints": {"title": "Animation Section", "subtitle": "Integration Test"}, "overlayConfig": null},
  "02_blue_circle_pulse": {"specBaseName": "02_blue_circle_pulse", "dataPoints": {"circle": {"centerX": 960, "centerY": 540, "baseRadius": 60, "pulseRadius": 80, "color": "#3B82F6"}, "glow": {"radius": 120, "color": "rgba(59, 130, 246, 0.2)"}}, "overlayConfig": null},
  "03_circle_to_square_morph": {"specBaseName": "03_circle_to_square_morph", "dataPoints": {"shape": {"size": 120, "borderRadiusStart": 60, "borderRadiusEnd": 12, "colorStart": "#3B82F6", "colorEnd": "#6366F1"}, "ghostTrail": {"count": 3, "opacities": [0.15, 0.1, 0.05], "frameOffsets": [0, 4, 8]}}, "overlayConfig": null},
  "04_square_slide_right": {"specBaseName": "04_square_slide_right", "dataPoints": {"slide": {"fromX": 960, "toX": 1440, "y": 540, "anticipationOffset": -10, "overshoot": 20, "streakMaxLength": 200}, "square": {"size": 120, "borderRadius": 12, "color": "#6366F1"}}, "overlayConfig": null},
  "05_split_comparison": {"specBaseName": "05_split_comparison", "dataPoints": {"layout": {"panelWidth": 960, "dividerWidth": 2, "dividerMaxOpacity": 0.6}, "shapes": {"circle": {"x": 480, "y": 440, "radius": 80, "color": "#3B82F6"}, "square": {"x": 480, "y": 440, "size": 120, "borderRadius": 12, "color": "#6366F1"}}}, "overlayConfig": null},
  "06_particle_burst": {"specBaseName": "06_particle_burst", "dataPoints": {"particles": {"count": 40, "minRadius": 4, "maxRadius": 8, "minDistance": 150, "maxDistance": 500, "angleJitter": 5, "seed": 42}, "flash": {"peakOpacity": 0.15}, "colorPalette": ["#3B82F6", "#6366F1", "#8B5CF6", "#FFFFFF"]}, "overlayConfig": null},
  "07_section_outro": {"specBaseName": "07_section_outro", "dataPoints": {"checkmark": {"path": "M8 24 L20 36 L40 12", "pathLength": 48, "strokeColor": "#22C55E", "strokeWidth": 3, "size": 48, "centerX": 960, "centerY": 480}, "text": {"content": "Section Complete", "centerY": 560}}, "overlayConfig": null},
  "08_key_visual": {"specBaseName": "08_key_visual", "dataPoints": {"bars": [{"value": 0.35, "maxHeight": 126, "color": "#38BDF8"}, {"value": 0.55, "maxHeight": 198, "color": "#22C55E"}, {"value": 0.8, "maxHeight": 288, "color": "#38BDF8"}, {"value": 0.6, "maxHeight": 216, "color": "#22C55E"}], "barWidth": 120, "barGap": 36, "containerHeight": 420, "barBaseHeight": 360}, "overlayConfig": null},
  "09_split_summary": {"specBaseName": "09_split_summary", "dataPoints": {"divider": {"startX": 640, "endX": 720, "width": 6, "color": "#38BDF8"}, "panels": {"left": {"background": "#0F172A", "label": "Before"}, "right": {"background": "#111827", "label": "After"}}}, "overlayConfig": null},
};

export const AnimationSectionSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 7.786667;
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
