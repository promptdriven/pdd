# Part 3: The Mold Has Three Parts (8:45 - 13:45)

This section explains the three components of the PDD "mold" metaphor: tests (walls), prompts (specification), and grounding (material properties). This is the technical heart of the video, establishing how PDD works in practice.

Total runtime: ~5 minutes.

## Section Breakdown

| Section | File | Tool | Duration | Description |
|---------|------|------|----------|-------------|
| 3.1 | `01_cross_section_intro.md` | Remotion | ~15s | Mold cross-section, 3 regions highlight |
| 3.2 | `02_walls_illuminate.md` | Remotion | ~15s | Test walls light up with labels |
| 3.3 | `03_liquid_injection.md` | Remotion | ~15s | Code generation flows, constrained by walls |
| 3.4 | `04_focus_single_wall.md` | Remotion | ~10s | Closeup: liquid hits "null→None" wall |
| 3.5 | `05_bug_discovered.md` | **Hybrid** | ~15s | Red alert on code, "BUG" label |
| 3.6 | `06_add_test_wall.md` | Remotion | ~20s | New wall materializes, `pdd bug` shown |
| 3.7 | `07_code_regenerates.md` | Remotion | ~15s | Code regenerates, `pdd fix` shown |
| 3.8 | `08_ratchet_timelapse.md` | Remotion | ~25s | Time-lapse wall accumulation, ratchet click |
| 3.9 | `09_traditional_vs_pdd.md` | Remotion | ~15s | Split screen comparison |
| 3.10 | `10_injection_nozzle.md` | Remotion | ~15s | Prompt capital intro, nozzle highlights |
| 3.11 | `11_prompt_text_flows.md` | Remotion | ~15s | Prompt text flows + `user_parser.prompt` visible |
| 3.12 | `12_prompt_variations.md` | Remotion | ~15s | Same prompt → different valid outputs |
| 3.13 | `13_prompt_governs_code.md` | Remotion | ~15s | Small prompt governs 200-line file |
| 3.14 | `14_grounding_panel.md` | Remotion | ~15s | Material properties panel |
| 3.15 | `15_grounding_comparison.md` | Remotion | ~20s | OOP vs Functional split |
| 3.16 | `16_grounding_database.md` | Remotion | ~15s | Success flows to grounding database |
| 3.17 | `17_three_components.md` | Remotion | ~25s | All three working together |
| 3.18 | `18_code_output_mold_glows.md` | Remotion | ~20s | Code fades, mold continues glowing |

## Tool Distribution

**Remotion (17 sections):** Abstract animations, diagrams, flows, technical visualizations
**Hybrid (1 section):** Bug discovery - video base with Remotion overlay

## Key Metaphor Mapping

| Mold Component | PDD Component | Visual Representation |
|----------------|---------------|----------------------|
| Mold Walls | Tests | Amber barriers that constrain flow |
| Injection Nozzle | Prompt | Blue glowing input point |
| Material Properties | Grounding | Green-tinted style patterns |
| Liquid Plastic | Generated Code | Gray fluid that takes shape |

## Narration Text (Part 3)

### Introduction (01)
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete. In PDD, the mold has three components. Three types of capital you're accumulating."

### Test Capital: The Walls (02-09)
> "First: tests. Tests are the walls of your mold."
>
> "Each test is a constraint. A boundary the generated code cannot cross."
>
> "When the model generates code, it sees these tests. The code it produces must pass them. It literally cannot generate code that violates these walls."
>
> "Now here's where it gets interesting. When you find a bug... you don't patch the code. You add a wall. That wall is permanent. That bug can never occur again—not in this generation, not in any future generation."
>
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."
>
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

### Prompt Capital: The Specification (10-13)
> "Second: the prompt. Your specification of what you want."
>
> "The prompt doesn't define the walls—tests do that. The prompt defines what you're asking for and why."
>
> "And here's something subtle: the exact implementation can vary. What's locked is the behavior. The code is flexible; the contract is fixed."
>
> "A good prompt is much smaller than the code it generates. You're specifying what and why, not how."

### Grounding Capital: The Material (14-16)
> "Third: grounding. This determines the properties of what fills the mold."
>
> "Grounding is learned from your past generations. When you successfully generate and fix code, that knowledge feeds back into the system."
>
> "Your style. Your patterns. Your team's conventions. Grounding captures all of it and applies it automatically to future generations."

### Integration (17-18)
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."
>
> "The code is output. The mold is what matters."

## Color Palette (Part 3)

- **Test Walls (Amber):** #D9944A - warm constraint color
- **Prompt (Blue):** #4A90D9 - cool specification color
- **Grounding (Green):** #5AAA6E - organic style color
- **Generated Code:** Gray (#A0A0A0) with blue tint
- **Bug/Defect:** Red (#D94A4A)
- **Mold structure:** Steel gray (#8A9BA8)
- **Background:** Dark (#1a1a2e)

## PDD Commands Shown

| Timestamp | Section | Command Shown |
|-----------|---------|---------------|
| ~9:45 | 05 - Bug discovered | `pdd bug user_parser` |
| ~10:00 | 06 - Add test wall | "Creating failing test..." output |
| ~10:15 | 07 - Code regenerates | `pdd fix user_parser` |
| ~10:30 | 08 - Ratchet timelapse | `pdd test` with scrolling output |
| ~11:00 | 11 - Prompt flows | `user_parser.prompt` visible |
| ~11:30 | 12 - Variations | `pdd generate user_parser.prompt` (twice) |
| ~12:15 | 16 - Grounding database | Arrow to cloud after `pdd fix` |

## Visual Style Notes

- Technical, precise diagrams for mold cross-section
- Fluid animations for code generation flow
- Satisfying "click" visual/sound for wall materialization
- Ratchet mechanical effect for test accumulation
- Clean split-screen for traditional vs PDD comparison
- Subtle terminal overlays in bottom-right corner
