import {
  expandSegmentRange,
  fillMissingAudioSyncSectionGroups,
  normalizeAudioSyncSectionGroups,
  prepareAudioSyncAutomation,
  reconcileAudioSyncSectionGroups,
  toSegmentRangeSectionGroups,
} from "@/components/stages/_lib/audio-sync-automation";

describe("normalizeAudioSyncSectionGroups", () => {
  it("expands persisted segment ranges into ordered segment IDs", () => {
    expect(
      normalizeAudioSyncSectionGroups({
        cold_open: {
          startSegment: "cold_open_001",
          endSegment: "cold_open_003",
        },
      })
    ).toEqual({
      cold_open: ["cold_open_001", "cold_open_002", "cold_open_003"],
    });
  });

  it("preserves array-based section groups", () => {
    expect(
      normalizeAudioSyncSectionGroups({
        intro: ["intro_001", "intro_002"],
      })
    ).toEqual({
      intro: ["intro_001", "intro_002"],
    });
  });
});

describe("fillMissingAudioSyncSectionGroups", () => {
  const sections = [
    { id: "cold_open", label: "Cold Open" },
    { id: "part1_economics", label: "Part 1" },
  ] as any;

  it("fills only missing section groups from TTS segment IDs", () => {
    const result = fillMissingAudioSyncSectionGroups({
      sections,
      existingGroups: {
        cold_open: ["cold_open_001"],
      },
      segments: [
        { id: "cold_open_001" },
        { id: "part1_economics_001" },
        { id: "part1_economics_002" },
      ],
    });

    expect(result.groups).toEqual({
      cold_open: ["cold_open_001"],
      part1_economics: ["part1_economics_001", "part1_economics_002"],
    });
    expect(result.filledSections).toEqual(["part1_economics"]);
    expect(result.changed).toBe(true);
  });

  it("matches the longest section id prefix first", () => {
    const result = fillMissingAudioSyncSectionGroups({
      sections: [
        { id: "part1", label: "Part 1" },
        { id: "part1_economics", label: "Part 1 Economics" },
      ] as any,
      existingGroups: {},
      segments: [{ id: "part1_economics_001" }],
    });

    expect(result.groups.part1_economics).toEqual(["part1_economics_001"]);
    expect(result.groups.part1).toBeUndefined();
  });
});

describe("reconcileAudioSyncSectionGroups", () => {
  const sections = [
    { id: "cold_open", label: "Cold Open" },
    { id: "part3_mold_parts", label: "Part 3" },
  ] as any;

  it("prunes obsolete groups and replaces them with manifest-derived current groups", () => {
    const result = reconcileAudioSyncSectionGroups({
      sections,
      existingGroups: {
        cold_open: ["cold_open_001", "cold_open_002"],
        part3_mold_has_three_parts: [
          "part3_mold_has_three_parts_001",
          "part3_mold_has_three_parts_002",
        ],
      },
      segments: [
        { id: "cold_open_001" },
        { id: "cold_open_002" },
        { id: "part3_mold_parts_001" },
        { id: "part3_mold_parts_002" },
      ],
    });

    expect(result.groups).toEqual({
      cold_open: ["cold_open_001", "cold_open_002"],
      part3_mold_parts: ["part3_mold_parts_001", "part3_mold_parts_002"],
    });
    expect(result.filledSections).toEqual(["part3_mold_parts"]);
    expect(result.removedSections).toEqual(["part3_mold_has_three_parts"]);
    expect(result.changed).toBe(true);
  });

  it("preserves current groups when no manifest segments are available for that section", () => {
    const result = reconcileAudioSyncSectionGroups({
      sections,
      existingGroups: {
        cold_open: ["cold_open_001"],
        part3_mold_parts: ["part3_mold_parts_001", "part3_mold_parts_002"],
      },
      segments: [{ id: "cold_open_001" }],
    });

    expect(result.groups).toEqual({
      cold_open: ["cold_open_001"],
      part3_mold_parts: ["part3_mold_parts_001", "part3_mold_parts_002"],
    });
    expect(result.removedSections).toEqual([]);
    expect(result.changed).toBe(false);
  });
});

describe("toSegmentRangeSectionGroups", () => {
  it("converts segment arrays back to persisted ranges", () => {
    expect(
      toSegmentRangeSectionGroups({
        part1_economics: ["part1_economics_004", "part1_economics_005"],
      })
    ).toEqual({
      part1_economics: {
        startSegment: "part1_economics_004",
        endSegment: "part1_economics_005",
      },
    });
  });
});

describe("prepareAudioSyncAutomation", () => {
  it("detects and saves missing section groups before Stage 5 automation runs", async () => {
    const fetchImpl = jest
      .fn()
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          sections: [
            { id: "cold_open", label: "Cold Open" },
            { id: "part1_economics", label: "Part 1" },
          ],
          audioSync: {
            sectionGroups: {
              cold_open: {
                startSegment: "cold_open_001",
                endSegment: "cold_open_002",
              },
            },
            silenceGapDefault: 0.3,
          },
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          segments: [
            { id: "cold_open_001" },
            { id: "cold_open_002" },
            { id: "part1_economics_001" },
            { id: "part1_economics_002" },
          ],
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({ ok: true }),
      });

    const result = await prepareAudioSyncAutomation(fetchImpl as unknown as typeof fetch);

    expect(result).toEqual({
      changed: true,
      filledSections: ["part1_economics"],
      unmatchedSegments: [],
    });
    expect(fetchImpl).toHaveBeenNthCalledWith(1, "/api/project");
    expect(fetchImpl).toHaveBeenNthCalledWith(2, "/api/pipeline/tts-render/segments");
    expect(fetchImpl).toHaveBeenNthCalledWith(
      3,
      "/api/project",
      expect.objectContaining({
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          audioSync: {
            sectionGroups: {
              cold_open: {
                startSegment: "cold_open_001",
                endSegment: "cold_open_002",
              },
              part1_economics: {
                startSegment: "part1_economics_001",
                endSegment: "part1_economics_002",
              },
            },
            silenceGapDefault: 0.3,
          },
        }),
      })
    );
  });

  it("reconciles stale section groups to the current project sections before Stage 5 automation runs", async () => {
    const fetchImpl = jest
      .fn()
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          sections: [
            { id: "cold_open", label: "Cold Open" },
            { id: "part3_mold_parts", label: "Part 3" },
          ],
          audioSync: {
            sectionGroups: {
              cold_open: {
                startSegment: "cold_open_001",
                endSegment: "cold_open_002",
              },
              part3_mold_has_three_parts: {
                startSegment: "part3_mold_has_three_parts_001",
                endSegment: "part3_mold_has_three_parts_002",
              },
            },
            silenceGapDefault: 0.3,
          },
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({
          segments: [
            { id: "cold_open_001" },
            { id: "cold_open_002" },
            { id: "part3_mold_parts_001" },
            { id: "part3_mold_parts_002" },
          ],
        }),
      })
      .mockResolvedValueOnce({
        ok: true,
        json: async () => ({ ok: true }),
      });

    const result = await prepareAudioSyncAutomation(fetchImpl as unknown as typeof fetch);

    expect(result).toEqual({
      changed: true,
      filledSections: ["part3_mold_parts"],
      removedSections: ["part3_mold_has_three_parts"],
      unmatchedSegments: [],
    });
    expect(fetchImpl).toHaveBeenNthCalledWith(
      3,
      "/api/project",
      expect.objectContaining({
        method: "PUT",
        body: JSON.stringify({
          audioSync: {
            sectionGroups: {
              cold_open: {
                startSegment: "cold_open_001",
                endSegment: "cold_open_002",
              },
              part3_mold_parts: {
                startSegment: "part3_mold_parts_001",
                endSegment: "part3_mold_parts_002",
              },
            },
            silenceGapDefault: 0.3,
          },
        }),
      })
    );
  });

  it("skips detection and save when all section groups already exist", async () => {
    const fetchImpl = jest.fn().mockResolvedValueOnce({
      ok: true,
      json: async () => ({
        sections: [{ id: "cold_open", label: "Cold Open" }],
        audioSync: {
          sectionGroups: {
            cold_open: {
              startSegment: "cold_open_001",
              endSegment: "cold_open_002",
            },
          },
        },
      }),
    });

    const result = await prepareAudioSyncAutomation(fetchImpl as unknown as typeof fetch);

    expect(result).toEqual({
      changed: false,
      filledSections: [],
      unmatchedSegments: [],
    });
    expect(fetchImpl).toHaveBeenCalledTimes(1);
  });
});
