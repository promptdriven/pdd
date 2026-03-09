import {
  findMatchingScriptSectionVisualIntent,
  parseScriptSectionVisualIntent,
  resolveSectionHasVeoIntent,
  resolveSectionVeoPromptFromScript,
} from "../app/api/pipeline/_lib/script-visual-intent";

describe("script visual intent helpers", () => {
  const mainScript = `
# Demo Script

## Animation Section
This block is all Remotion and title cards.
[Remotion] Build an animated chart.

## Veo Section
This block includes cinematic footage.
[veo: Ocean wave at sunset]

## Part 3: Closing Thoughts
[title:] Final takeaway.
  `.trim();

  it("parses script sections and captures veo markers", () => {
    const sections = parseScriptSectionVisualIntent(mainScript);

    expect(sections).toHaveLength(3);
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
