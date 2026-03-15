import React from "react";
import { Sequence, useCurrentFrame, Audio, staticFile } from "remotion";
import { VISUAL_SEQUENCE } from "./constants";
import { SlotScaledSequence, VisualMediaProvider, VisualContractProvider } from "../_shared/visual-runtime";
import { Part2ParadigmShiftMain } from "../part2_paradigm_shift_main";

const COMPONENT_MAP: Record<string, React.ComponentType<any>> = {
  "part2_paradigm_shift_main": Part2ParadigmShiftMain,
};

const VISUAL_DURATIONS: Record<string, number> = {
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "07_netlist_zoom_unreviewable": {"specBaseName": "07_netlist_zoom_unreviewable", "dataPoints": {"chipLayout": {"gateColor": "#2AA198", "wireColor": "rgba(42, 161, 152, 0.1)", "zoomLevels": [1, 10, 100, 1000]}, "codeDiff": {"totalLines": 10247, "addBackground": "rgba(34, 197, 94, 0.12)", "deleteBackground": "rgba(239, 68, 68, 0.12)", "addTextColor": "#A3BE8C", "deleteTextColor": "#EF4444", "scrollLinesPerSecond": 100}, "resolution": {"prompt": {"filename": "email_validator.prompt", "lineCount": 8, "background": "rgba(74, 144, 217, 0.1)", "borderColor": "#4A90D9"}, "tests": {"testCount": 7, "allPassing": true, "background": "rgba(34, 197, 94, 0.08)", "borderColor": "#22C55E"}, "label": "Review the spec. Verify the output."}, "backgroundColor": "#0A0A0F"}, "overlayConfig": null},
  "part2_paradigm_shift_main": {"specBaseName": "main", "dataPoints": null, "overlayConfig": null},
};

export const Part2ParadigmShiftSection: React.FC = () => {
  const fps = 30;
  const durationSeconds = 0;
  const frame = useCurrentFrame();
  const activeVisuals = VISUAL_SEQUENCE.filter((visual) => frame >= visual.start && frame < visual.end);

  return (
    <Sequence from={0} durationInFrames={Math.max(1, Math.ceil(durationSeconds * fps))}>
      <Audio src={staticFile("part2_paradigm_shift/narration.wav")} />
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

export default Part2ParadigmShiftSection;
