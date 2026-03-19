import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { WhereToStart01SectionTitleCard } from "../WhereToStart01SectionTitleCard";
import { WhereToStart02LegacyCodebaseReveal } from "../WhereToStart02LegacyCodebaseReveal";
import { WhereToStart03ModuleHighlightUpdate } from "../WhereToStart03ModuleHighlightUpdate";
import { WhereToStart04SourceOfTruthShift } from "../WhereToStart04SourceOfTruthShift";
import { WhereToStart05RegenerateCompareLoop } from "../WhereToStart05RegenerateCompareLoop";
import { WhereToStart06SpreadingGlowMigration } from "../WhereToStart06SpreadingGlowMigration";
import { WhereToStart07NoBigBangCallout } from "../WhereToStart07NoBigBangCallout";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": WhereToStart01SectionTitleCard,
  "02_legacy_codebase_reveal": WhereToStart02LegacyCodebaseReveal,
  "03_module_highlight_update": WhereToStart03ModuleHighlightUpdate,
  "04_source_of_truth_shift": WhereToStart04SourceOfTruthShift,
  "05_regenerate_compare_loop": WhereToStart05RegenerateCompareLoop,
  "06_spreading_glow_migration": WhereToStart06SpreadingGlowMigration,
  "07_no_big_bang_callout": WhereToStart07NoBigBangCallout,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "03_module_highlight_update": 240,
  "04_source_of_truth_shift": 180,
  "05_regenerate_compare_loop": 180,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": null, "overlayConfig": null},
  "02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": null, "overlayConfig": null},
  "03_module_highlight_update": {"specBaseName": "03_module_highlight_update", "dataPoints": null, "overlayConfig": null},
  "04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": null, "overlayConfig": null},
  "05_regenerate_compare_loop": {"specBaseName": "05_regenerate_compare_loop", "dataPoints": null, "overlayConfig": null},
  "06_spreading_glow_migration": {"specBaseName": "06_spreading_glow_migration", "dataPoints": null, "overlayConfig": null},
  "07_no_big_bang_callout": {"specBaseName": "07_no_big_bang_callout", "dataPoints": null, "overlayConfig": null},
};

export const WhereToStartSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 32.08;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("where_to_start/narration.wav")} />
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

export default WhereToStartSection;
