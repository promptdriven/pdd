import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { WhereToStart01SectionTitleCard } from "../WhereToStart01SectionTitleCard";
import { WhereToStart02LegacyCodebaseReveal } from "../WhereToStart02LegacyCodebaseReveal";
import { WhereToStart04SourceOfTruthShift } from "../WhereToStart04SourceOfTruthShift";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "01_section_title_card": WhereToStart01SectionTitleCard,
  "02_legacy_codebase_reveal": WhereToStart02LegacyCodebaseReveal,
  "04_source_of_truth_shift": WhereToStart04SourceOfTruthShift,
};

const VISUAL_DURATIONS: Record<string, number> = {
  "01_section_title_card": 90,
  "02_legacy_codebase_reveal": 150,
  "04_source_of_truth_shift": 180,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionId": "where_to_start", "sectionNumber": 6, "sectionLabel": "PART 6", "title": "WHERE TO START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "codebase_tree", "color": "#334155", "style": "file_tree"}], "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "code_visualization", "chartId": "legacy_codebase_reveal", "panels": 5, "fileNames": ["auth_handler.py", "payment_processor.py", "user_service.py", "legacy_router.py", "config.py"], "warningComments": ["// don't touch", "// here be dragons", "// TODO: fix this someday", "// nobody knows why this works"], "lineCount": "~47,000", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": {"type": "code_transformation", "chartId": "source_of_truth_shift", "transformedModules": [{"name": "auth_handler.py", "state": "complete"}, {"name": "payment_processor.py", "state": "animating"}], "pendingModules": ["user_service.py", "legacy_router.py", "config.py", "db_connector.py", "email_sender.py", "cache_layer.py"], "workflow": ["module", "prompt", "tests", "regenerate", "compare"], "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "07_transition_to_closing": {"specBaseName": "07_transition_to_closing", "dataPoints": {"type": "transition", "transitionId": "where_to_start_to_closing", "echoes": [{"source": "no_big_bang_callout", "opacity": 0.06}, {"source": "sock_metaphor", "opacity": 0.05}], "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
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
                  <VisualMediaProvider media={visualContract?.renderMode === "component" ? null : visualMedia}>
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
