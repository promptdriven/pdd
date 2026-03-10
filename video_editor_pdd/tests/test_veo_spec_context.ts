import {
  extractVeoMarker,
  listResolvedVeoClipSpecs,
  isVeoMarkdownSpec,
  selectCanonicalVeoMarkdownSpec,
  selectCanonicalVeoPromptSpec,
} from "@/lib/veo-spec-context";

describe("veo spec context helpers", () => {
  it("extracts a non-empty [veo:] marker prompt from markdown", () => {
    expect(
      extractVeoMarker("[veo: A cinematic slow-motion ocean wave at sunset]")
    ).toBe("A cinematic slow-motion ocean wave at sunset");
  });

  it("ignores blank [veo:] markers", () => {
    expect(extractVeoMarker("[veo:]")).toBeNull();
  });

  it("selects the first sorted markdown spec associated with Veo, even when its marker is blank", () => {
    const selection = selectCanonicalVeoMarkdownSpec([
      {
        path: "specs/section/07_abstract_flow.md",
        content: "[veo: Abstract cyan particles in a dark void]",
      },
      {
        path: "specs/section/04_blank.md",
        content: "[veo:]",
      },
      {
        path: "specs/section/02_chart.md",
        content: "[Remotion]\n# Not a Veo clip",
      },
      {
        path: "specs/section/05_ocean.md",
        content: "[veo: Ocean wave at sunset]",
      },
    ]);

    expect(selection).toEqual({
      path: "specs/section/04_blank.md",
    });
  });

  it("returns null when no markdown spec is associated with Veo", () => {
    expect(
      selectCanonicalVeoMarkdownSpec([
        { path: "specs/section/01_title.md", content: "[title:]" },
        { path: "specs/section/02_chart.md", content: "[Remotion]\n# Chart" },
      ])
    ).toBeNull();
  });

  it("detects Veo markdown specs via blank markers or tool labels", () => {
    expect(isVeoMarkdownSpec("[veo:]")).toBe(true);
    expect(isVeoMarkdownSpec("**Tool:** Veo\n# Forest aerial")).toBe(true);
    expect(isVeoMarkdownSpec("[Remotion]\n# Not Veo")).toBe(false);
  });

  it("selects the first markdown spec with a non-empty prompt for clip generation", () => {
    const selection = selectCanonicalVeoPromptSpec([
      {
        path: "specs/section/04_blank.md",
        content: "[veo:]",
      },
      {
        path: "specs/section/05_ocean.md",
        content: "[veo: Ocean wave at sunset]",
      },
    ]);

    expect(selection).toEqual({
      path: "specs/section/05_ocean.md",
      prompt: "Ocean wave at sunset",
    });
  });

  it("resolves one generated clip per Veo markdown spec when prompts and clip sources are declared in the spec JSON", () => {
    const clips = listResolvedVeoClipSpecs([
      {
        path: "specs/veo_section/02_ocean_wave_sunset.md",
        content: [
          "[veo:]",
          "```json",
          '{',
          '  "veoPrompt": "Ocean wave at sunset",',
          '  "clipSource": "veo/ocean_wave_sunset.mp4"',
          '}',
          "```",
        ].join("\n"),
      },
      {
        path: "specs/veo_section/04_forest_canopy_aerial.md",
        content: [
          "[veo:]",
          "```json",
          '{',
          '  "veoPrompt": "Forest canopy aerial",',
          '  "clipSource": "veo/forest_canopy_aerial.mp4"',
          '}',
          "```",
        ].join("\n"),
      },
    ]);

    expect(clips).toEqual([
      {
        id: "ocean_wave_sunset",
        path: "specs/veo_section/02_ocean_wave_sunset.md",
        prompt: "Ocean wave at sunset",
        filename: "ocean_wave_sunset.mp4",
        chainFromPrevious: false,
      },
      {
        id: "forest_canopy_aerial",
        path: "specs/veo_section/04_forest_canopy_aerial.md",
        prompt: "Forest canopy aerial",
        filename: "forest_canopy_aerial.mp4",
        chainFromPrevious: false,
      },
    ]);
  });

  it("allows an explicit Veo spec to opt into frame chaining", () => {
    const clips = listResolvedVeoClipSpecs([
      {
        path: "specs/veo_section/04_forest_canopy_aerial.md",
        content: [
          "[veo:]",
          "```json",
          '{',
          '  "veoPrompt": "Forest canopy aerial",',
          '  "clipSource": "veo/forest_canopy_aerial.mp4",',
          '  "chainFromPrevious": true',
          '}',
          "```",
        ].join("\n"),
      },
    ]);

    expect(clips).toEqual([
      {
        id: "forest_canopy_aerial",
        path: "specs/veo_section/04_forest_canopy_aerial.md",
        prompt: "Forest canopy aerial",
        filename: "forest_canopy_aerial.mp4",
        chainFromPrevious: true,
      },
    ]);
  });
});
