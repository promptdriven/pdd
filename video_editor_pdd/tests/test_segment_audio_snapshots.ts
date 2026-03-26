import {
  captureSegmentAudioSnapshots,
  restoreSegmentAudioSnapshots,
} from "@/components/stages/_lib/segment-audio-snapshots";

describe("segment audio snapshot helpers", () => {
  it("captures current segment audio as base64 snapshots", async () => {
    const bytes = new Uint8Array([82, 73, 70, 70]);
    const fetchImpl = jest.fn().mockResolvedValue({
      ok: true,
      arrayBuffer: async () => bytes.buffer,
    });

    const snapshots = await captureSegmentAudioSnapshots({
      segmentIds: ["part1_economics_005"],
      fetchImpl,
      now: () => 123,
    });

    expect(fetchImpl).toHaveBeenCalledWith(
      "/api/audio/tts/part1_economics_005.wav?v=123",
      { cache: "no-store" },
    );
    expect(snapshots).toEqual({
      part1_economics_005: "UklGRg==",
    });
  });

  it("restores snapshots through the segment-audio restore route", async () => {
    const fetchImpl = jest.fn().mockResolvedValue({
      ok: true,
      json: async () => ({ restoredCount: 1 }),
    });

    await expect(
      restoreSegmentAudioSnapshots({
        snapshots: {
          part1_economics_005: "UklGRg==",
        },
        fetchImpl,
      }),
    ).resolves.toBeUndefined();

    expect(fetchImpl).toHaveBeenCalledWith("/api/pipeline/tts-render/audio", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        segments: [
          {
            segmentId: "part1_economics_005",
            audioBase64: "UklGRg==",
          },
        ],
      }),
    });
  });
});
