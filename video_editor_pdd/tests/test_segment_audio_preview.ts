import {
  loadSegmentPreviewAudio,
  resetSegmentPreviewAudio,
  type PreviewAudioElement,
} from "@/components/stages/_lib/segment-audio-preview";

function createAudioStub(): PreviewAudioElement {
  return {
    currentTime: 0,
    src: "",
    pause: jest.fn(),
    load: jest.fn(),
    play: jest.fn().mockResolvedValue(undefined),
    removeAttribute: jest.fn(function (this: PreviewAudioElement, name: string) {
      if (name === "src") {
        this.src = "";
      }
    }),
  };
}

describe("segment audio preview helpers", () => {
  it("loads preview audio through a no-store fetch and blob URL", async () => {
    const audio = createAudioStub();
    const fetchImpl = jest.fn().mockResolvedValue({
      ok: true,
      blob: async () => new Blob(["speech"]),
    });
    const createObjectURL = jest.fn().mockReturnValue("blob:preview");
    const revokeObjectURL = jest.fn();

    const objectUrl = await loadSegmentPreviewAudio({
      audio,
      segmentId: "part1_economics_005",
      previousObjectUrl: "blob:stale",
      fetchImpl,
      createObjectURL,
      revokeObjectURL,
      now: () => 123,
    });

    expect(fetchImpl).toHaveBeenCalledWith("/api/audio/tts/part1_economics_005.wav?v=123", {
      cache: "no-store",
    });
    expect(revokeObjectURL).toHaveBeenCalledWith("blob:stale");
    expect(audio.src).toBe("blob:preview");
    expect(audio.load).toHaveBeenCalled();
    expect(audio.play).toHaveBeenCalled();
    expect(objectUrl).toBe("blob:preview");
  });

  it("revokes the new blob URL when playback setup fails", async () => {
    const audio = createAudioStub();
    (audio.play as jest.Mock).mockRejectedValue(new Error("decode failed"));
    const fetchImpl = jest.fn().mockResolvedValue({
      ok: true,
      blob: async () => new Blob(["speech"]),
    });
    const createObjectURL = jest.fn().mockReturnValue("blob:preview");
    const revokeObjectURL = jest.fn();

    await expect(
      loadSegmentPreviewAudio({
        audio,
        segmentId: "part1_economics_005",
        previousObjectUrl: null,
        fetchImpl,
        createObjectURL,
        revokeObjectURL,
      })
    ).rejects.toThrow("decode failed");

    expect(revokeObjectURL).toHaveBeenCalledWith("blob:preview");
    expect(audio.removeAttribute).toHaveBeenCalledWith("src");
  });

  it("resets preview audio and revokes the current blob URL", () => {
    const audio = createAudioStub();
    audio.src = "blob:preview";
    const revokeObjectURL = jest.fn();

    const result = resetSegmentPreviewAudio(audio, "blob:preview", revokeObjectURL);

    expect(audio.pause).toHaveBeenCalled();
    expect(audio.currentTime).toBe(0);
    expect(audio.removeAttribute).toHaveBeenCalledWith("src");
    expect(audio.load).toHaveBeenCalled();
    expect(revokeObjectURL).toHaveBeenCalledWith("blob:preview");
    expect(result).toBeNull();
  });
});
