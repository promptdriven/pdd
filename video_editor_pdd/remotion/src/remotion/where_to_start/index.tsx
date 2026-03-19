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
  "02_legacy_codebase_reveal": 150,
  "03_module_highlight_update": 240,
  "04_source_of_truth_shift": 180,
  "05_regenerate_compare_loop": 180,
};

const VISUAL_MEDIA: Record<string, Record<string, string>> = {
};

const VISUAL_OVERLAYS: Record<string, Record<string, string | boolean>> = {
};

const VISUAL_CONTRACTS: Record<string, Record<string, unknown> | null> = {
  "01_section_title_card": {"specBaseName": "01_section_title_card", "dataPoints": {"type": "title_card", "sectionNumber": 6, "sectionLabel": "WHERE TO START", "titleLine1": "WHERE TO", "titleLine2": "START", "backgroundColor": "#0A0F1A", "ghostElements": [{"shape": "network_graph", "color": "#94A3B8", "component": "codebase_topology"}, {"shape": "highlighted_node", "color": "#4A90D9", "component": "starting_point"}], "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "02_legacy_codebase_reveal": {"specBaseName": "02_legacy_codebase_reveal", "dataPoints": {"type": "codebase_visualization", "blockCount": 40, "edgeCount": 60, "debtRatio": 0.3, "annotations": [{"text": "// don't touch", "position": [380, 320]}, {"text": "// here be dragons", "position": [1100, 250]}, {"text": "// legacy", "position": [720, 580]}, {"text": "// temporary fix (2019)", "position": [1350, 650]}], "colorScheme": {"clean": "#1E293B", "debt": "#2A1F1F", "annotation": "#EF4444"}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_001"]}, "overlayConfig": null, "renderMode": "component"},
  "03_module_highlight_update": {"specBaseName": "03_module_highlight_update", "dataPoints": {"type": "workflow_animation", "workflow": "pdd_update", "sourceFile": "auth_handler.py", "outputFile": "auth_handler.prompt", "promptLines": ["# Auth Handler", "Authenticate incoming requests using JWT.", "Validate token signature and expiration.", "Extract user_id and role from claims.", "Return None on invalid or expired tokens."], "terminalCommands": ["pdd update auth_handler.py", "✓ Created auth_handler.prompt"], "particleStream": {"from": [640, 420], "to": [1100, 380], "count": 25}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "04_source_of_truth_shift": {"specBaseName": "04_source_of_truth_shift", "dataPoints": {"type": "value_migration", "before": {"sourceOfTruth": "auth_handler.py", "role": "code", "state": "active"}, "after": {"sourceOfTruth": "auth_handler.prompt", "role": "specification", "state": "glowing"}, "tests": [{"name": "JWT verify", "status": "passing"}, {"name": "expiry check", "status": "passing"}, {"name": "null safety", "status": "passing"}], "terminalCommand": "pdd test auth_handler", "terminalResult": "3/3 passing", "callout": "The prompt is your new source of truth.", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "05_regenerate_compare_loop": {"specBaseName": "05_regenerate_compare_loop", "dataPoints": {"type": "workflow_pipeline", "steps": [{"label": "Generate prompt", "command": "pdd update", "icon": "prompt_doc"}, {"label": "Add tests", "command": "pdd bug", "icon": "wall_icons"}, {"label": "Regenerate", "command": "pdd fix", "icon": "terminal"}, {"label": "Compare", "command": "pdd test", "icon": "diff_view"}], "loopFrom": 3, "loopTo": 1, "loopLabel": "iterate", "progressBar": true, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_002"]}, "overlayConfig": null, "renderMode": "component"},
  "06_spreading_glow_migration": {"specBaseName": "06_spreading_glow_migration", "dataPoints": {"type": "migration_animation", "totalModules": 40, "conversionWaves": [{"frame": 0, "modules": ["auth_handler"], "cumulative": 1}, {"frame": 20, "modules": ["session_manager", "token_validator"], "cumulative": 3}, {"frame": 60, "modules": ["user_parser", "role_checker"], "cumulative": 5}, {"frame": 110, "modules": ["api_router", "middleware_chain", "rate_limiter"], "cumulative": 8}], "moduleStates": {"unconverted": {"fill": "#1E293B", "border": "#334155"}, "converting": {"border": "#4A90D9", "glowOpacity": 0.2}, "converted": {"fill": "#0F172A", "border": "#4A90D9", "glowOpacity": 0.08}}, "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
  "07_no_big_bang_callout": {"specBaseName": "07_no_big_bang_callout", "dataPoints": {"type": "callout_card", "lines": [{"text": "One module at a time.", "weight": 600, "size": 28}, {"text": "No big bang. No rewrite.", "weight": 400, "size": 22}, {"text": "A gradual migration of where value lives — from code to specification.", "weight": 400, "size": 18, "highlights": [{"word": "code", "color": "#64748B"}, {"word": "specification", "color": "#4A90D9", "glow": true}]}], "ghostBackground": "codebase_topology_blurred", "backgroundColor": "#0A0F1A", "narrationSegments": ["where_to_start_003"]}, "overlayConfig": null, "renderMode": "component"},
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
