#!/usr/bin/env python3
"""Generate section-level Remotion compositions that sync audio with visuals.

Creates constants.ts, component TSX, and index.ts for each section wrapper.
These compositions play the section narration audio and sequence through
sub-compositions (Remotion animations + Veo video clips) keyed to timestamps.
"""

import json
import math
import os
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
REMOTION_SRC = PROJECT_ROOT / "remotion" / "src" / "remotion"
TTS_OUTPUT = PROJECT_ROOT / "outputs" / "tts"

FPS = 30


def s2f(seconds: float) -> int:
    return round(seconds * FPS)


# Section definitions with visual sequence mapping
SECTIONS = {
    "part1": {
        "folder": "S01-Economics",
        "component": "Part1Economics",
        "prefix": "PART1",
        "audio_file": "part1_economics_narration.wav",
        "tts_dir": "01-economics",
        # Map Whisper segment ranges to visual compositions
        # format: (seg_start, seg_end, composition_id_or_veo, description)
        "visual_sequence": [
            (0, 4, "SockPriceChart", "Sock economics: nostalgia → economics → 1950 → flipped → irrational"),
            (5, 8, "CodeCostChart", "Code economics: look at code → expensive → patched → rational"),
            (9, 18, "CodeCostChart", "AI enters: interesting → faster → cursor/claude → real → feel it"),
            (19, 24, "CrossingPoint", "Reveal: dashed line → debt → accumulates → 60% speedup → debt ate rest"),
            (25, 44, "ContextRot", "Context rot: something else → small=brilliant → window → grows → keyhole → guesses wrong"),
            (45, 51, "DeveloperEditZoomout", "Regeneration: doesn't have problem → fits window → crossed both lines → no debt"),
            (52, 56, "veo:07_split_screen_sepia", "Best darning needles: cursor/claude → fantastic → still darning → accumulation"),
            (57, 64, "PieChart", "Maintenance costs: 80-90% → maintaining → compound → reset"),
            (65, 75, "PartsEject", "Paradigm shift: what changed → mold once → unlimited parts → defect?"),
            (76, 81, "ValueAura", "Fix the mold → every part → real shift → where value lives"),
        ],
    },
    "part2": {
        "folder": "S02-ParadigmShift",
        "component": "Part2ParadigmShift",
        "prefix": "PART2",
        "audio_file": "part2_paradigm_shift_narration.wav",
        "tts_dir": "02-paradigm-shift",
        "visual_sequence": [
            (0, 1, "veo:01_factory_floor", "Crafting vs molding: value in object vs specification"),
            (2, 2, "MoldToPrompt", "PDD: prompt is your mold, code is plastic"),
            (3, 5, "PromptGeneratesCode", "Three components intro: precise → mold has three parts"),
            (6, 9, "CrossSectionIntro", "Test capital: tests are walls → constraint → sees tests → cannot violate"),
            (10, 12, "AddTestWall", "Bug found: don't patch → add wall → permanent"),
            (13, 14, "RatchetTimelapse", "Ratchet effect: tests accumulate → constrains all future"),
            (15, 16, "TraditionalVsPdd", "Traditional vs PDD: bug fix one place vs everywhere forever"),
        ],
    },
    "part3": {
        "folder": "S03-MoldThreeParts",
        "component": "Part3MoldThreeParts",
        "prefix": "PART3",
        "audio_file": "part3_mold_narration.wav",
        "tts_dir": "03-mold-has-three-parts",
        "visual_sequence": [
            (0, 3, "PromptTextFlows", "Prompt capital: specification → doesn't define walls → asking for and why"),
            (4, 8, "PromptVariations", "Subtle: implementation varies → behavior locked → flexible → contract fixed"),
            (9, 10, "PromptGovernsCode", "Compression: smaller than code → what and why not how"),
            (11, 18, "GroundingPanel", "Grounding: properties → learned → style → conventions → automatically"),
            (19, 22, "ThreeComponents", "Integration: prompt+tests+grounding → complete spec → code is output → mold matters"),
            (23, 28, "veo:split_3d_vs_mold", "Precision tradeoff: 3D printing → no mold → every point → walls constrain"),
            (29, 37, "PrecisionGraph", "PDD mapping: few tests → specify everything → many tests → intent only → accumulation"),
            (38, 44, "LongPrompt", "Compound returns: patch → local returns → one bug → sub-linear"),
            (45, 49, "ShortPromptTests", "PDD returns: test today → constrains tomorrow → permanent wall → compound vs diminishing"),
        ],
    },
    "part4": {
        "folder": "S04-PrecisionTradeoff",
        "component": "Part4PrecisionTradeoff",
        "prefix": "PART4",
        "audio_file": "part4_precision_narration.wav",
        "tts_dir": "04-precision-tradeoff",
        "visual_sequence": [
            (0, 1, "veo:07_split_screen_sepia", "Grandmother: not stupid → economics rational"),
            (2, 6, "GraphAnimateCurve", "You: not stupid → economics changed → became darning socks"),
            (7, 8, "BothGenerateFinal", "Transition beat"),
            (9, 14, "CrossSectionIntro", "Doesn't eliminate → elevates → mold designers → materials → physics"),
            (15, 20, "PromptGovernsCode", "PDD developers → specification level → not writing → specifying → contract → shift"),
        ],
    },
    "part5": {
        "folder": "S05-CompoundReturns",
        "component": "Part5CompoundReturns",
        "prefix": "PART5",
        "audio_file": "part5_compound_narration.wav",
        "tts_dir": "05-compound-returns",
        "visual_sequence": [
            (0, 1, "CodeOutputMoldGlows", "Code still there → live in specification → verified disposable"),
            (2, 2, "CodeOutputMoldGlows", "Transition"),
            (3, 5, "CodeOutputMoldGlows", "Mental shift: don't patch socks → cheap → prompts encode intent"),
            (6, 7, "ThreeComponents", "Tests preserve behavior → grounding maintains style"),
            (8, 8, "CodeOutputMoldGlows", "Code generated, verified, disposable"),
        ],
    },
    "closing": {
        "folder": "S06-Closing",
        "component": "ClosingSection",
        "prefix": "CLOSING",
        "audio_file": "closing_narration.wav",
        "tts_dir": "06-closing",
        "visual_sequence": [
            (0, 0, "CodeOutputMoldGlows", "The code is just plastic"),
            (1, 1, "ThreeComponents", "The mold is what matters"),
            (2, 2, "ThreeComponents", "Hold"),
        ],
    },
}

# Composition import info: (folder_name, component_name, default_props_name)
COMPOSITION_IMPORTS = {
    "SockPriceChart": ("02-SockPriceChart", "SockPriceChart", "defaultSockPriceChartProps"),
    "ThresholdHighlight": ("03-ThresholdHighlight", "ThresholdHighlight", "defaultThresholdHighlightProps"),
    "LinesDiverge": ("04-LinesDiverge", "LinesDiverge", "defaultLinesDivergeProps"),
    "CodeCostChart": ("05-CodeCostChart", "CodeCostChart", "defaultCodeCostChartProps"),
    "AIMilestones": ("06-AIMilestones", "AIMilestones", "defaultAIMilestonesProps"),
    "ContextRot": ("07-ContextRot", "ContextRot", "defaultContextRotProps"),
    "CrossingPoint": ("08-CrossingPoint", "CrossingPoint", "defaultCrossingPointProps"),
    "DeveloperEditZoomout": ("09-DeveloperEditZoomout", "DeveloperEditZoomout", "defaultDeveloperEditZoomoutProps"),
    "PieChart": ("12-PieChart", "PieChart", "defaultPieChartProps"),
    "PieToCurve": ("13-PieToCurve", "PieToCurve", "defaultPieToCurveProps"),
    "PartsEject": ("14-PartsEject", "PartsEject", "defaultPartsEjectProps"),
    "DefectDiscovered": ("15-DefectDiscovered", "DefectDiscovered", "defaultDefectDiscoveredProps"),
    "PerfectParts": ("16-PerfectParts", "PerfectParts", "defaultPerfectPartsProps"),
    "ValueAura": ("17-ValueAura", "ValueAura", "defaultValueAuraProps"),
    "PlasticRegenerates": ("18-PlasticRegenerates", "PlasticRegenerates", "defaultPlasticRegeneratesProps"),
    "MoldToPrompt": ("19-MoldToPrompt", "MoldToPrompt", "defaultMoldToPromptProps"),
    "PromptGeneratesCode": ("20-PromptGeneratesCode", "PromptGeneratesCode", "defaultPromptGeneratesCodeProps"),
    "CrossSectionIntro": ("21-CrossSectionIntro", "CrossSectionIntro", "defaultCrossSectionIntroProps"),
    "WallsIlluminate": ("22-WallsIlluminate", "WallsIlluminate", "defaultWallsIlluminateProps"),
    "LiquidInjection": ("23-LiquidInjection", "LiquidInjection", "defaultLiquidInjectionProps"),
    "FocusSingleWall": ("24-FocusSingleWall", "FocusSingleWall", "defaultFocusSingleWallProps"),
    "BugDiscovered": ("25-BugDiscovered", "BugDiscovered", "defaultBugDiscoveredProps"),
    "AddTestWall": ("26-AddTestWall", "AddTestWall", "defaultAddTestWallProps"),
    "CodeRegenerates": ("27-CodeRegenerates", "CodeRegenerates", "defaultCodeRegeneratesProps"),
    "RatchetTimelapse": ("28-RatchetTimelapse", "RatchetTimelapse", "defaultRatchetTimelapseProps"),
    "TraditionalVsPdd": ("29-TraditionalVsPdd", "TraditionalVsPdd", "defaultTraditionalVsPddProps"),
    "InjectionNozzle": ("30-InjectionNozzle", "InjectionNozzle", "defaultInjectionNozzleProps"),
    "PromptTextFlows": ("31-PromptTextFlows", "PromptTextFlows", "defaultPromptTextFlowsProps"),
    "PromptVariations": ("32-PromptVariations", "PromptVariations", "defaultPromptVariationsProps"),
    "PromptGovernsCode": ("33-PromptGovernsCode", "PromptGovernsCode", "defaultPromptGovernsCodeProps"),
    "GroundingPanel": ("34-GroundingPanel", "GroundingPanel", "defaultGroundingPanelProps"),
    "GroundingComparison": ("35-GroundingComparison", "GroundingComparison", "defaultGroundingComparisonProps"),
    "GroundingDatabase": ("36-GroundingDatabase", "GroundingDatabase", "defaultGroundingDatabaseProps"),
    "ThreeComponents": ("37-ThreeComponents", "ThreeComponents", "defaultThreeComponentsProps"),
    "CodeOutputMoldGlows": ("38-CodeOutputMoldGlows", "CodeOutputMoldGlows", "defaultCodeOutputMoldGlowsProps"),
    "PrinterFocus": ("39-3DPrinterFocus", "PrinterFocus", "defaultPrinterFocusProps"),
    "MoldFlowFocus": ("40-MoldFlowFocus", "MoldFlowFocus", "defaultMoldFlowFocusProps"),
    "PrecisionGraph": ("41-PrecisionGraph", "PrecisionGraph", "defaultPrecisionGraphProps"),
    "GraphAnimateCurve": ("42-GraphAnimateCurve", "GraphAnimateCurve", "defaultGraphAnimateCurveProps"),
    "LongPrompt": ("43-LongPrompt", "LongPrompt", "defaultLongPromptProps"),
    "ShortPromptTests": ("44-ShortPromptTests", "ShortPromptTests", "defaultShortPromptTestsProps"),
    "BothGenerateFinal": ("45-BothGenerateFinal", "BothGenerateFinal", "defaultBothGenerateFinalProps"),
}


def load_timestamps(section_key: str) -> dict:
    """Load word_timestamps.json for a section."""
    tts_dir = SECTIONS[section_key]["tts_dir"]
    path = TTS_OUTPUT / tts_dir / "word_timestamps.json"
    with open(path) as f:
        return json.load(f)


def generate_constants(section_key: str) -> str:
    """Generate constants.ts for a section composition."""
    section = SECTIONS[section_key]
    ts_data = load_timestamps(section_key)
    segments = ts_data["segments"]
    duration = ts_data["duration"]
    prefix = section["prefix"]
    duration_seconds = math.ceil(duration) + 2  # 2s buffer

    # Build BEATS entries from visual sequence
    beats_lines = []
    for i, (seg_start, seg_end, comp_id, desc) in enumerate(section["visual_sequence"]):
        # Get timestamp from the first segment in the range
        start_time = segments[seg_start]["start"] if seg_start < len(segments) else 0
        end_time = segments[min(seg_end, len(segments) - 1)]["end"] if seg_end < len(segments) else duration
        start_text = segments[seg_start]["text"][:50] if seg_start < len(segments) else ""

        beat_name = f"VISUAL_{i:02d}_START"
        beat_end = f"VISUAL_{i:02d}_END"
        beats_lines.append(f'  // Visual {i}: {comp_id} — "{start_text}..."')
        beats_lines.append(f"  {beat_name}: s2f({start_time}),  // {s2f(start_time)} frames")
        beats_lines.append(f"  {beat_end}: s2f({end_time}),  // {s2f(end_time)} frames")
        beats_lines.append("")

    # Build narration breakdown comment
    narration_lines = []
    for i, seg in enumerate(segments):
        text = seg["text"][:55]
        narration_lines.append(f"//  {seg['start']:6.1f}s [{i:2d}] \"{text}...\"" if len(seg["text"]) > 55 else f"//  {seg['start']:6.1f}s [{i:2d}] \"{text}\"")

    return f'''import {{ z }} from "zod";

// ── Audio-synced timing ────────────────────────────────────────────
// Section: {ts_data.get("section", section_key)}
// Audio: {section["audio_file"]} ({duration:.1f}s)
// Generated from word_timestamps.json — Whisper segment boundaries
//
// Narration segments:
{chr(10).join(narration_lines)}

export const {prefix}_FPS = {FPS};
export const {prefix}_DURATION_SECONDS = {duration_seconds};
export const {prefix}_DURATION_FRAMES = {prefix}_FPS * {prefix}_DURATION_SECONDS;
export const {prefix}_WIDTH = 1920;
export const {prefix}_HEIGHT = 1080;

// Helper: seconds to frames
const s2f = (seconds: number) => Math.round(seconds * {prefix}_FPS);

export const BEATS = {{
{chr(10).join(beats_lines)}}};

// Visual sequence: maps BEATS ranges to composition IDs
export const VISUAL_SEQUENCE = [
{chr(10).join(f'  {{ start: BEATS.VISUAL_{i:02d}_START, end: BEATS.VISUAL_{i:02d}_END, id: "{comp_id}", desc: "{desc[:60]}" }},' for i, (_, _, comp_id, desc) in enumerate(section["visual_sequence"]))}
];

// Props schema
export const {section["component"]}Props = z.object({{
  showTitle: z.boolean().default(true),
}});

export const default{section["component"]}Props: z.infer<typeof {section["component"]}Props> = {{
  showTitle: true,
}};

export type {section["component"]}PropsType = z.infer<typeof {section["component"]}Props>;
'''


def generate_component(section_key: str) -> str:
    """Generate the main component TSX for a section."""
    section = SECTIONS[section_key]
    comp_name = section["component"]
    prefix = section["prefix"]

    # Collect unique composition IDs used (excluding veo: prefixed ones)
    used_compositions = set()
    has_veo = False
    for _, _, comp_id, _ in section["visual_sequence"]:
        if comp_id.startswith("veo:"):
            has_veo = True
        else:
            used_compositions.add(comp_id)

    # Build imports for used compositions (component + default props)
    comp_imports = []
    for comp_id in sorted(used_compositions):
        if comp_id in COMPOSITION_IMPORTS:
            folder, name, default_props = COMPOSITION_IMPORTS[comp_id]
            comp_imports.append(f'import {{ {name}, {default_props} }} from "../{folder}";')

    # Build Remotion imports (only include OffthreadVideo if needed)
    remotion_imports = ["AbsoluteFill", "Audio", "Sequence", "staticFile", "useCurrentFrame"]
    if has_veo:
        remotion_imports.insert(3, "OffthreadVideo")

    # Build visual switch cases
    switch_cases = []
    for i, (_, _, comp_id, desc) in enumerate(section["visual_sequence"]):
        if comp_id.startswith("veo:"):
            veo_file = comp_id.replace("veo:", "")
            switch_cases.append(f'''
      {{/* Visual {i}: Veo clip - {desc[:50]} */}}
      {{activeVisual === {i} && (
        <AbsoluteFill>
          <OffthreadVideo
            src={{staticFile("{veo_file}.mp4")}}
            style={{{{ width: "100%", height: "100%" }}}}
          />
        </AbsoluteFill>
      )}}''')
        else:
            default_props = COMPOSITION_IMPORTS[comp_id][2] if comp_id in COMPOSITION_IMPORTS else None
            props_spread = f" {{...{default_props}}}" if default_props else ""
            switch_cases.append(f'''
      {{/* Visual {i}: {comp_id} - {desc[:50]} */}}
      {{activeVisual === {i} && (
        <Sequence from={{BEATS.VISUAL_{i:02d}_START}} durationInFrames={{BEATS.VISUAL_{i:02d}_END - BEATS.VISUAL_{i:02d}_START}}>
          <{comp_id}{props_spread} />
        </Sequence>
      )}}''')

    remotion_import_str = ",\n  ".join(remotion_imports)

    return f'''import React from "react";
import {{
  {remotion_import_str},
}} from "remotion";
import {{ BEATS, VISUAL_SEQUENCE, {comp_name}PropsType }} from "./constants";
{chr(10).join(comp_imports)}

export const {comp_name}: React.FC<{comp_name}PropsType> = () => {{
  const frame = useCurrentFrame();

  // Determine which visual is active based on frame position
  let activeVisual = 0;
  for (let i = VISUAL_SEQUENCE.length - 1; i >= 0; i--) {{
    if (frame >= VISUAL_SEQUENCE[i].start) {{
      activeVisual = i;
      break;
    }}
  }}

  return (
    <AbsoluteFill style={{{{ backgroundColor: "#0a0a1a" }}}}>
      {{/* Narration audio */}}
      <Audio src={{staticFile("{section['audio_file']}")}} />

      {{/* Visual compositions sequenced by BEATS */}}
      {chr(10).join(switch_cases)}
    </AbsoluteFill>
  );
}};
'''


def generate_index(section_key: str) -> str:
    """Generate index.ts for a section composition."""
    section = SECTIONS[section_key]
    comp_name = section["component"]
    prefix = section["prefix"]

    return f'''export {{ {comp_name} }} from "./{comp_name}";
export {{
  {prefix}_FPS,
  {prefix}_DURATION_FRAMES,
  {prefix}_WIDTH,
  {prefix}_HEIGHT,
  {comp_name}Props,
  default{comp_name}Props,
}} from "./constants";
'''


def generate_all():
    """Generate all section composition files."""
    for section_key, section in SECTIONS.items():
        folder = REMOTION_SRC / section["folder"]
        folder.mkdir(parents=True, exist_ok=True)

        # Generate constants.ts
        constants = generate_constants(section_key)
        (folder / "constants.ts").write_text(constants)
        print(f"  {section['folder']}/constants.ts")

        # Generate component
        component = generate_component(section_key)
        (folder / f"{section['component']}.tsx").write_text(component)
        print(f"  {section['folder']}/{section['component']}.tsx")

        # Generate index.ts
        index = generate_index(section_key)
        (folder / "index.ts").write_text(index)
        print(f"  {section['folder']}/index.ts")

    print(f"\nGenerated {len(SECTIONS)} section compositions.")
    print("\nNext: Update Root.tsx to register the new compositions.")


if __name__ == "__main__":
    generate_all()
