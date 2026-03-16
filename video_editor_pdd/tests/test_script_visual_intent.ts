import {
  findMatchingScriptSectionVisualIntent,
  parseScriptSectionVisualIntent,
  resolveSectionHasVeoIntent,
  resolveSectionVisualIntent,
  resolveSectionVeoPromptFromScript,
} from "../app/api/pipeline/_lib/script-visual-intent";

describe("script visual intent helpers", () => {
  const mainScript = `
# Demo Script

## Animation Section
**[VISUAL: Animated chart with axes and labels.]**
[Remotion] Build an animated chart.

## Veo Section
This block includes cinematic footage.
[veo: Ocean wave at sunset]

## Cinematic Section
**[VISUAL: A developer at a keyboard in a dim office while rain streaks the window.]**
**[VISUAL: Close-up on hands typing. Hard cut to a city street at night.]**

## Part 3: Closing Thoughts
[title:] Final takeaway.
  `.trim();

  it("parses script sections and captures veo markers", () => {
    const sections = parseScriptSectionVisualIntent(mainScript);

    expect(sections).toHaveLength(4);
    expect(sections[0].heading).toBe("Animation Section");
    expect(sections[0].veoMarkers).toEqual([]);
    expect(sections[1].veoMarkers).toEqual(["Ocean wave at sunset"]);
  });

  it("matches a project section by normalized id and label", () => {
    const sections = parseScriptSectionVisualIntent(mainScript);

    const match = findMatchingScriptSectionVisualIntent(sections, {
      id: "animation_section",
      label: "Animation Section",
    });

    expect(match?.heading).toBe("Animation Section");
  });

  it("returns false when the matched script section has no veo markers", () => {
    expect(
      resolveSectionHasVeoIntent(mainScript, {
        id: "animation_section",
        label: "Animation Section",
      })
    ).toBe(false);
  });

  it("infers hybrid/veo-friendly intent from cinematic visual descriptions even without explicit veo markers", () => {
    expect(
      resolveSectionHasVeoIntent(mainScript, {
        id: "cinematic_section",
        label: "Cinematic Section",
      })
    ).toBe(true);

    expect(
      resolveSectionVisualIntent(mainScript, {
        id: "cinematic_section",
        label: "Cinematic Section",
      })
    ).toMatchObject({
      mode: "hybrid",
      explicitVeo: false,
    });
  });

  it("returns the first veo prompt from the matched script section", () => {
    expect(
      resolveSectionVeoPromptFromScript(mainScript, {
        id: "veo_section",
        label: "Veo Section",
      })
    ).toBe("Ocean wave at sunset");
  });

  it("returns null when no matching script section can be found", () => {
    expect(
      resolveSectionHasVeoIntent(mainScript, {
        id: "totally_different",
        label: "Totally Different",
      })
    ).toBeNull();
  });
});
