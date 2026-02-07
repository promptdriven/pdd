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
# Visual sequences map Whisper segment ranges (from word_timestamps.json)
# to visual compositions, matched against spec READMEs.
# NOTE: TTS was generated from an earlier script version; some spec narration
# lines are missing from the actual audio. Visuals match what audio says.
SECTIONS = {
    "cold_open": {
        "folder": "S00-ColdOpen",
        "component": "ColdOpenSection",
        "prefix": "COLD_OPEN",
        "audio_file": "cold_open_narration.wav",
        "tts_dir": "00-cold-open",
        # 5 Whisper segments, 16.1s
        # Script: COLD OPEN: THE SOCK HOOK (0:00 - 2:00)
        "visual_sequence": [
            # [VISUAL: Split screen. Developer/Cursor + Grandmother darning]
            (0, 0, "veo:07_split_screen_sepia", "If you use Cursor, Claude Code, Copilot, getting good"),
            # [VISUAL: Zoom out on both sides, accumulated weight of repair]
            (1, 1, "veo:07_split_screen_sepia", "Great-grandmother figured out sixty years ago"),
            # [VISUAL: Hard cut modern day. Toss sock, grab fresh pair.]
            (2, 2, "veo:07_split_screen_sepia", "When socks got cheap enough she stopped"),
            # [VISUAL: Code function deletes and regenerates clean]
            (3, 3, "veo:07_split_screen_sepia", "Code just got that cheap"),
            # [VISUAL: Title card: Prompt-Driven Development]
            (4, 4, "veo:07_split_screen_sepia", "So why are we still patching"),
        ],
    },
    "part1": {
        "folder": "S01-Economics",
        "component": "Part1Economics",
        "prefix": "PART1",
        "audio_file": "part1_economics_narration.wav",
        "tts_dir": "01-economics",
        # 117 Whisper segments, 432.9s
        # Spec: 1.1-1.13 (SockPriceChart → PieToCurve)
        # Script: PART 1: THE ECONOMICS OF DARNING (2:00 - 6:30)
        "visual_sequence": [
            # [VISUAL: Price chart animation. 1950: wool sock costs about an hour of wages]
            (0, 0, "SockPriceChart", "This isn't nostalgia, it's economics"),
            # [VISUAL: Crossing point highlights. Label: The Threshold]
            (1, 2, "ThresholdHighlight", "In 1950 wool sock cost real money, darning made sense"),
            # [VISUAL: Lines diverge dramatically. By 2020, socks essentially free]
            (3, 5, "LinesDiverge", "Mid-1960s math flipped, darning became irrational"),
            # [VISUAL: Transition to similar chart for code]
            (6, 6, "CodeCostChart", "Now look at code"),
            # [VISUAL: Key dates on falling generate line: Codex, GPT-4, Claude]
            (7, 10, "AIMilestones", "For decades generating expensive, you patched, rational"),
            # [VISUAL: Post-2020, amber patch line drops; AI made patching faster]
            (11, 16, "CodeCostChart", "AI made patching faster too, Cursor Claude Copilot"),
            # [VISUAL: Focus on immediate patch line dropping]
            (17, 18, "CodeCostChartMini", "Each patch getting faster, that's real, you feel it"),
            # [VISUAL: Camera pulls back, debt EXPANDS, dashed total cost barely moves]
            (19, 22, "CrossingPoint", "But watch dashed line, debt accumulates faster"),
            # [VISUAL: Annotations: GitHub 55%, Uplevel 0%, 41% more bugs]
            (23, 33, "CrossingPoint", "GitHub 55% speedup, Uplevel 800 devs no change"),
            # [VISUAL: Annotations: GitClear +44% churn, -60% refactoring]
            (34, 39, "CrossingPoint", "GitClear 44% churn, refactoring -60%, piling on"),
            # [VISUAL: Zoom into debt area: Code Complexity + Context Rot layers]
            (40, 41, "ContextRot", "Something else hiding in debt, AI-specific"),
            # [VISUAL: Context window over small codebase, covers ~80%]
            (42, 47, "ContextRot", "Small codebase AI brilliant, context covers everything"),
            # [VISUAL: Codebase grid grows, context window stays same size]
            (48, 51, "ContextRot", "Codebases grow, window stays same, millions of tokens"),
            # [VISUAL: Red/green blocks: irrelevant inside, needed outside window]
            (52, 59, "ContextRot", "AI guesses relevance, vector search fails, agentic slow"),
            # [VISUAL: Performance vs Context Length graph, degrades 14-85%]
            (60, 68, "ContextRot", "EMNLP: performance degrades with length, context rot"),
            # [VISUAL: Patch line FORKS: small codebase down, large stays flat]
            (69, 72, "CrossingPoint", "AI patching two stories, small codebase transformative"),
            # [VISUAL: Large-codebase flat, METR 19% slower, 39-point gap]
            (73, 80, "CrossingPoint", "Large codebase 19% slower, 39-point perception gap"),
            # [VISUAL: Arrow from small fork to large: every patch adds code]
            (81, 83, "CrossingPoint", "Every patch makes codebase bigger, pushes to worse world"),
            # [VISUAL: Generate line pulses: small modules, clear prompts]
            (84, 90, "veo:veo_developer_edit", "Regeneration no problem, prompt fits, no retrieval no rot"),
            # [VISUAL: Side-by-side: agentic patching (noisy) vs PDD (clean)]
            (91, 99, "veo:veo_developer_edit", "NL is models deepest fluency, 250 lines lowest defects"),
            # [VISUAL: Generate line crosses below both lines. "We are here."]
            (100, 103, "CrossingPoint", "Generation crossed below both lines, debt resets"),
            # [VISUAL: Split screen: Developer with Cursor / Grandma with needle]
            (104, 107, "veo:07_split_screen_sepia", "Best darning needles ever, still accumulation"),
            # [VISUAL: Pie chart: Initial Dev 10-20%, Maintenance 80-90%]
            (108, 113, "PieChart", "80-90% cost is maintenance, McKinsey Stripe tech debt"),
            # [VISUAL: Pie morphs to compound interest curve, regeneration flat]
            (114, 116, "PieToCurve", "Costs compound literally, unless you regenerate"),
        ],
    },
    "part2": {
        "folder": "S02-ParadigmShift",
        "component": "Part2ParadigmShift",
        "prefix": "PART2",
        "audio_file": "part2_paradigm_shift_narration.wav",
        "tts_dir": "02-paradigm-shift",
        # 31 Whisper segments, 177.1s
        # Spec: 2.1-2.11 (factory floor → prompt generates code)
        # Script: PART 2: THE PARADIGM SHIFT (6:30 - 10:30)
        "visual_sequence": [
            # [VISUAL: Factory floor. Industrial. Injection molding machine.]
            (0, 1, "veo:01_factory_floor", "Pattern across industries, deeper shift in how things made"),
            # [VISUAL: Close-up injection mold. Liquid plastic flows into mold.]
            (2, 3, "veo:02_mold_closeup", "Consider injection molding, crafted to designed molds"),
            # [VISUAL: Mold opens, perfect parts eject. Counter: 1...10...10000]
            (4, 5, "PartsEject", "Make mold once, unlimited parts, refine once all improve"),
            # [VISUAL: Defect in molded part]
            (6, 6, "veo:veo_defect_discovered", "When there's a defect, don't patch individual parts"),
            # [VISUAL: Engineer adjusts mold. New parts all perfect.]
            (7, 7, "PerfectParts", "Fix the mold, fix applies to every future part"),
            # [VISUAL: Split craftsman/mold. Glowing aura on mold/chair.]
            (8, 9, "ValueAura", "Real shift: migration of where value lives"),
            # [VISUAL: In molding, value in specification. Part disposable.]
            (10, 11, "PlasticRegenerates", "Molding value in specification, disposable, regenerate"),
            # [VISUAL: 1980s electronics lab, hand-drawn circuits]
            (12, 12, "veo:07_craftsman_vs_mold", "Not just plastics, chip industry hit this exact wall"),
            # [VISUAL: Hand-drawn schematic zooms out, impossibly dense]
            (13, 16, "MoldToPrompt", "1980s drew gates by hand, moved to Verilog in 1985"),
            # [VISUAL: Schematic dissolves, Verilog code, Synopsys processes]
            (17, 19, "MoldToPrompt", "Synthesis non-deterministic, different gates every time"),
            # [VISUAL: Verification toolchain, formal equivalence checking]
            (20, 23, "MoldToPrompt", "Synopsys wrapped verification, SAT/SMT proof, same function"),
            # [VISUAL: Timeline: Transistors→Schematics→RTL→Behavioral→NL]
            (24, 27, "MoldToPrompt", "By 1990 schematic, mid-90s half switched, all use HDL now"),
            # [VISUAL: Verilog morphs to PROMPT, netlist to code, tests appear]
            (28, 30, "PromptGeneratesCode", "Same transition for software, prompt is mold, tests lock"),
        ],
    },
    "part3": {
        "folder": "S03-MoldThreeParts",
        "component": "Part3MoldThreeParts",
        "prefix": "PART3",
        "audio_file": "part3_mold_narration.wav",
        "tts_dir": "03-mold-has-three-parts",
        # 40 Whisper segments, 292.1s
        # Spec: 3.1-3.18 (cross section → code output mold glows)
        # Script: PART 3: THE MOLD HAS THREE PARTS (10:30 - 16:00)
        "visual_sequence": [
            # [VISUAL: Cross-section of injection mold. Three regions highlight.]
            (0, 1, "CrossSectionIntro", "Get precise, mold has three components, three capitals"),
            # [VISUAL: Walls illuminate with labels: null->None, empty string, etc]
            (2, 3, "WallsIlluminate", "First tests, tests are walls, constraint, boundary"),
            # [VISUAL: Liquid injected, hits walls, stops. Walls matter.]
            (4, 7, "LiquidInjection", "Walls matter, CodeRabbit 1.7x issues, DORA confirms"),
            # [VISUAL: Focus single wall "null->None", liquid stops]
            (8, 9, "FocusSingleWall", "Walls not optional, model sees tests, cannot violate"),
            # [VISUAL: Bug discovered! Red alert.]
            (10, 10, "BugDiscovered", "Bug found, you don't patch the code"),
            # [VISUAL: New wall materializes for bug condition. Code regenerates.]
            (11, 12, "AddTestWall", "Add a wall, permanent, bug can never occur again"),
            # [VISUAL: Time-lapse: more bugs, more walls, mold gets precise]
            (13, 13, "RatchetTimelapse", "Ratchet effect, tests only accumulate, mold more precise"),
            # [VISUAL: Split: Traditional (patch cycle) vs PDD (add test, regen)]
            (14, 14, "TraditionalVsPdd", "Traditional fix one place, PDD prevents bug everywhere"),
            # [VISUAL: Synopsys Formality + Z3 logos, same math]
            (15, 17, "TraditionalVsPdd", "Synopsys uses SAT/SMT, PDD uses Z3, same class solver"),
            # [VISUAL: Side-by-side: Synopsys FEC vs PDD+Z3, mathematical proof]
            (18, 22, "TraditionalVsPdd", "Z3 proves for all inputs, symbolic reasoning, same math"),
            # [VISUAL: Injection nozzle highlights: intent, requirements, constraints]
            (23, 24, "InjectionNozzle", "Second the prompt, specification of what you want"),
            # [VISUAL: Text flows into mold: Parse user IDs...]
            (25, 25, "PromptTextFlows", "Prompt defines what and why, implementation can vary"),
            # [VISUAL: Same prompt generates code twice, different but both pass]
            (26, 26, "PromptVariations", "Behavior locked, code flexible, contract fixed"),
            # [VISUAL: Prompt glows, small (10-15 lines) governs 200-line file]
            (27, 27, "PromptGovernsCode", "Good prompt 1/5 to 1/10 size, what and why not how"),
            # [VISUAL: Two context windows: code-filled vs prompt-filled]
            (28, 33, "PromptGovernsCode", "Context window: prompts are NL, 30x more training data"),
            # [VISUAL: Grounding panel: OOP, Functional, Your Team's Style]
            (34, 34, "GroundingPanel", "Third grounding, determines properties of what fills mold"),
            # [VISUAL: Same prompt, different grounding: OOP vs functional output]
            (35, 35, "GroundingComparison", "Grounding learned from past generations"),
            # [VISUAL: Successful gen flows into Grounding Database]
            (36, 37, "GroundingDatabase", "Style patterns conventions, feeds back into system"),
            # [VISUAL: All three working together: prompt+grounding+tests->code]
            (38, 38, "ThreeComponents", "Prompt+tests+grounding, complete specification"),
            # [VISUAL: Code emerges clean. Code fades. Mold continues to glow.]
            (39, 39, "CodeOutputMoldGlows", "Code is output, mold is what matters"),
        ],
    },
    "part4": {
        "folder": "S04-PrecisionTradeoff",
        "component": "Part4PrecisionTradeoff",
        "prefix": "PART4",
        "audio_file": "part4_precision_narration.wav",
        "tts_dir": "04-precision-tradeoff",
        # 16 Whisper segments, 58.8s
        # Spec: 4.1-4.8 (split 3D vs mold → both generate final)
        # Script: PART 4: THE PRECISION TRADEOFF (16:00 - 18:00)
        "visual_sequence": [
            # [VISUAL: Split screen. LEFT: 3D printer. RIGHT: Injection mold.]
            (0, 0, "veo:split_3d_vs_mold", "Something subtle that changes how you think about prompts"),
            # [VISUAL: Focus on 3D printer, coordinate grid, every point specified]
            (1, 3, "veo:veo_3d_printer_focus", "3D printing no mold, every point precise, specification precise"),
            # [VISUAL: Focus on injection mold, liquid flows until walls constrain]
            (4, 5, "veo:veo_mold_flow_focus", "Injection molding precision comes from walls, flows constrained"),
            # [VISUAL: Graph: X=Number of Tests, Y=Required Prompt Precision]
            (6, 6, "PrecisionGraph", "This maps directly to PDD"),
            # [VISUAL: Animate along curve: few tests = detailed prompt]
            (7, 8, "LongPrompt", "Few tests prompt specifies everything, edge cases, errors"),
            # [VISUAL: Many tests = minimal prompt, surrounded by test walls]
            (9, 10, "ShortPromptTests", "Many tests prompt only needs intent, tests handle constraints"),
            # [VISUAL: Both scenarios generate correct output]
            (11, 13, "GraphAnimateCurve", "Test accumulation not just catching bugs, simpler prompts"),
            # [VISUAL: "More tests, less prompt. The walls do the precision work."]
            (14, 15, "BothGenerateFinal", "More walls less to specify, mold does precision work"),
        ],
    },
    "part5": {
        "folder": "S05-CompoundReturns",
        "component": "Part5CompoundReturns",
        "prefix": "PART5",
        "audio_file": "part5_compound_narration.wav",
        "tts_dir": "05-compound-returns",
        # 23 Whisper segments, 84.9s
        # Script: PART 5: COMPOUND RETURNS (18:00 - 20:15)
        "visual_sequence": [
            # [VISUAL: Graph with two curves: Patching vs PDD]
            (0, 0, "GraphAnimateCurve", "Let's talk about compound returns"),
            # [VISUAL: Patching curve: local returns, linear then flatten]
            (1, 7, "GraphAnimateCurve", "Patch code local returns, 1.7x issues, risks more patches"),
            # [VISUAL: Patching curve wobbles, dips at conflicts]
            (8, 10, "GraphAnimateCurve", "Returns linear at best, cost compounding, 1.52T annually"),
            # [VISUAL: PDD curve: each test compounds, constrains all future]
            (11, 13, "ShortPromptTests", "PDD test returns compound, constrains future, permanent wall"),
            # [VISUAL: Investment table: Patching vs PDD returns]
            (14, 15, "BothGenerateFinal", "Every mold investment compounds, patching diminishes"),
            # [VISUAL: Return to grandmother and modern person with socks]
            (16, 17, "veo:07_split_screen_sepia", "Great-grandmother rational for darning, economics made sense"),
            # [VISUAL: Return to developer with Cursor]
            (18, 19, "veo:07_split_screen_sepia", "Not stupid for patching, economics made it rational"),
            # [VISUAL: Economics chart. Crossing point pulses.]
            (20, 22, "CrossingPoint", "Economics changed, rational becomes darning socks"),
        ],
    },
    "closing": {
        "folder": "S06-Closing",
        "component": "ClosingSection",
        "prefix": "CLOSING",
        "audio_file": "closing_narration.wav",
        "tts_dir": "06-closing",
        # 10 Whisper segments, 33.5s
        # Script: CLOSING (20:15 - 21:30)
        "visual_sequence": [
            # [VISUAL: Complete system, prompts+tests glow, code is output]
            (0, 0, "CodeOutputMoldGlows", "So here's the mental shift"),
            # [VISUAL: Sock metaphor returns. Holey sock discarded, fresh pair.]
            (1, 2, "veo:07_split_screen_sepia", "Don't patch socks, socks got cheap, irrational"),
            # [VISUAL: Code with bug, add test, regenerate. pdd bug -> pdd fix]
            (3, 3, "CodeOutputMoldGlows", "Code just got that cheap"),
            # [VISUAL: Triangle: PROMPT (top), TESTS (left), GROUNDING (right)]
            (4, 6, "ThreeComponents", "Prompts encode intent, tests preserve, grounding maintains"),
            # [VISUAL: Code dissolves and regenerates repeatedly, always passes]
            (7, 7, "CodeOutputMoldGlows", "Code is generated verified and disposable"),
            # [VISUAL: Final frame. Mold glows. Plastic part unremarkable.]
            (8, 9, "CodeOutputMoldGlows", "The code is just plastic, the mold is what matters"),
        ],
    },
}

# Composition import info: (folder_name, component_name, default_props_name)
COMPOSITION_IMPORTS = {
    "ColdOpenSplitScreen": ("01-ColdOpen", "ColdOpenSplitScreen", "defaultColdOpenProps"),
    "SockPriceChart": ("02-SockPriceChart", "SockPriceChart", "defaultSockPriceChartProps"),
    "CodeCostChartMini": ("05a-CodeCostChartMini", "CodeCostChartMini", "defaultCodeCostChartMiniProps"),
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
