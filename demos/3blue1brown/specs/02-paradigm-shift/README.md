# Part 2: The Paradigm Shift (6:30 - 10:30)

This section introduces the injection molding metaphor - the key conceptual framework for understanding PDD. The shift from "crafting objects" to "designing molds" mirrors the shift from "writing code" to "writing specifications."

Total runtime: ~4 minutes.

## Section Breakdown

| Section | File | Tool | Duration | Description |
|---------|------|------|----------|-------------|
| 2.1 | `01_factory_floor.md` | **Veo 3.1** | ~15s | Industrial factory floor, injection molding machine |
| 2.2 | `02_mold_closeup.md` | **Veo 3.1** | ~15s | Close-up: liquid plastic flows into precise mold |
| 2.3 | `03_parts_eject.md` | Remotion | ~20s | Parts eject with counter: 1...10...100...10,000 |
| 2.4 | `04_defect_discovered.md` | **Hybrid** | ~10s | Defect in part, zoom in on flaw |
| 2.5 | `05_engineer_fixes_mold.md` | **Veo 3.1** | ~15s | Engineer adjusts the mold itself (not the part) |
| 2.6 | `06_perfect_parts.md` | Remotion | ~10s | New parts eject, all perfect, defective discarded |
| 2.7 | `07_craftsman_vs_mold.md` | **Veo 3.1** | ~15s | Split: craftsman carving wood vs injection mold |
| 2.8 | `08_value_aura.md` | Remotion | ~15s | Glowing aura shows where value lives |
| 2.9 | `09_plastic_regenerates.md` | Remotion | ~10s | Plastic part dissolves, instantly regenerates |
| 2.10 | `10_mold_to_prompt.md` | Remotion | ~20s | Mold morphs into PROMPT document, plastic → code |
| 2.11 | `11_prompt_generates_code.md` | Remotion | ~15s | Prompt pulses, code flows, tests appear as walls |

## Tool Distribution

**Remotion (6 sections):** Abstract animations, counters, morphing transitions, glowing effects
**Veo 3.1 (4 sections):** Factory footage, human engineer, physical objects
**Hybrid (1 section):** Video with animated overlay

## Key Metaphor Mapping

| Manufacturing | Software (PDD) |
|---------------|----------------|
| Injection Mold | Prompt + Tests |
| Liquid Plastic | LLM Generation |
| Molded Part | Generated Code |
| Mold Walls | Test Constraints |
| Fixing the Mold | Adding Tests |
| Discarding Defective Part | Regenerating Code |

## Narration Text (Part 2)

> There's a pattern here that shows up across industries. Not just cheaper materials--a deeper shift in *how things are made*.
>
> Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds.
>
> Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically.
>
> And when there's a defect? You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again.
>
> This is the real shift. Not "cheaper material." A migration of where value lives.
>
> In crafting, value lives in the object. You protect the object. Losing the chair is losing everything.
>
> In molding, value lives in the specification--the mold. The plastic part? Disposable. Regenerate it at will.
>
> And it's not just plastics. The chip industry hit this exact wall.
>
> In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up. So in 1985, they moved up--from schematics to Verilog. A hardware description language. You described what you wanted the chip to *do*, and a synthesis tool generated the gates.
>
> But here's the thing: synthesis was non-deterministic. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time.
>
> What Synopsys did was wrap a verification toolchain around the generator. Formal equivalence checking--using SAT and SMT solvers to produce mathematical proof that the output, whatever it looked like, behaved identically to the spec. The gates were different every time. The function was the same every time.
>
> By 1990, most designs were still schematic-based. By the mid-1990s, half had switched. Today, all but the most trivial chips use HDL. Every time component counts exceeded what the current abstraction could handle, the industry moved up a level. The designer stopped specifying *how* and started specifying *what*.
>
> This is that same transition. For software.
>
> The prompt is your mold. The code is just plastic. And just like chip synthesis--the code is different every generation. But the tests lock the behavior. The process is deterministic.

## Color Palette (Part 2 Specific)

- **Mold/Metal:** Cool steel gray (#8A9BA8)
- **Liquid Plastic:** Warm amber (#D9944A) - connects to "maintenance" color
- **Prompt Glow:** Cool blue (#4A90D9)
- **Value Aura:** White/gold gradient
- **Defect Highlight:** Red (#D94A4A)

## Missing Spec Coverage

The following main script content in Part 2 does not yet have corresponding spec files:
- **Chip Design History (lines 198-216):** 1980s electronics lab, hand-drawn schematics, Verilog introduction (1985), Synopsys synthesis non-determinism, formal equivalence checking, abstraction timeline (transistors -> schematics -> RTL -> behavioral -> natural language)
- **Transition to Software (lines 218-225):** Verilog morphs to PROMPT document, gate-level netlist morphs to code, Synopsys checkmark morphs to test suite
