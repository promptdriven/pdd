import {
  expandSegmentRange,
  fillMissingAudioSyncSectionGroups,
  normalizeAudioSyncSectionGroups,
  prepareAudioSyncAutomation,
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
