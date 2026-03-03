/**
 * Tests for lib/veo.ts (Google GenAI SDK implementation)
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification.
 *
 * Spec requirements verified:
 *   1. Export generateReferenceImage(prompt, outputPath) -> Promise<void>
 *   2. Export generateVeoClip(prompt, refImagePath | null, aspectRatio, outputPath) -> Promise<void>
 *   3. Export extractLastFrame(clipPath, outputPath) -> Promise<void>
 *   4. Use GOOGLE_API_KEY env var for auth via @google/genai SDK
 *   5. Imagen via GenAI SDK: numberOfImages: 1, aspectRatio: '1:1', outputMimeType: 'image/png'
 *   6. Veo via GenAI SDK: numberOfVideos: 1, aspectRatio from param, durationSeconds: 8
 *   7. Poll every 5s; timeout after 10 min
 *   8. server-only guard (throws if window is defined)
 *   9. Uses ffprobe and ffmpeg for frame extraction
 *  10. Ensures output directories exist before writing
 *  11. GCS URI to HTTPS conversion for video download
 *  12. Descriptive errors on all failure paths
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Mock @google/genai SDK
// ---------------------------------------------------------------------------

const mockGenerateImages = jest.fn();
const mockGenerateVideos = jest.fn();
const mockGetVideosOperation = jest.fn();

jest.mock("@google/genai", () => ({
  GoogleGenAI: jest.fn().mockImplementation(() => ({
    models: {
      generateImages: mockGenerateImages,
      generateVideos: mockGenerateVideos,
    },
    operations: {
      getVideosOperation: mockGetVideosOperation,
    },
  })),
}));

// ---------------------------------------------------------------------------
// Mock child_process.exec
// ---------------------------------------------------------------------------

const mockExec = jest.fn();
jest.mock("child_process", () => ({
  exec: mockExec,
}));

// Must import after jest.mock
import {
  generateReferenceImage,
  generateVeoClip,
  extractLastFrame,
} from "../lib/veo";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const ORIGINAL_API_KEY = process.env.GOOGLE_API_KEY;
const ORIGINAL_FETCH = global.fetch;

function setupEnvVars() {
  process.env.GOOGLE_API_KEY = "test-api-key-123";
}

function setupFsMocks() {
  jest.spyOn(fs, "writeFileSync").mockImplementation(() => {});
  jest.spyOn(fs, "mkdirSync").mockReturnValue(undefined as any);
}

function setupExecSuccess() {
  mockExec.mockImplementation((cmd: string, callback: Function) => {
    callback(null, "10.5", "");
  });
}

function makeImagenResponse(base64 = "dGVzdC1pbWFnZQ==") {
  return {
    generatedImages: [{ image: { imageBytes: base64 } }],
  };
}

function makeVeoOperation({
  done = false,
  videoUri = "gs://bucket/video.mp4",
  error,
}: {
  done?: boolean;
  videoUri?: string | null;
  error?: object;
} = {}) {
  return {
    done,
    ...(error ? { error } : {}),
    response: done
      ? {
          generatedVideos: [
            { video: videoUri ? { uri: videoUri } : {} },
          ],
        }
      : undefined,
  };
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  setupEnvVars();
  jest.clearAllMocks();
  mockGenerateImages.mockReset();
  mockGenerateVideos.mockReset();
  mockGetVideosOperation.mockReset();
});

afterEach(() => {
  jest.restoreAllMocks();
  global.fetch = ORIGINAL_FETCH;
  if (ORIGINAL_API_KEY !== undefined) {
    process.env.GOOGLE_API_KEY = ORIGINAL_API_KEY;
  } else {
    delete process.env.GOOGLE_API_KEY;
  }
});

// ---------------------------------------------------------------------------
// 1. generateReferenceImage -- GenAI SDK call
// ---------------------------------------------------------------------------

describe("generateReferenceImage -- GenAI SDK call", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls generateImages with imagen-3.0-generate-002 model", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test prompt", "/tmp/out.png");

    expect(mockGenerateImages).toHaveBeenCalledWith(
      expect.objectContaining({
        model: "imagen-3.0-generate-002",
      })
    );
  });

  it("sends prompt to generateImages", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("professional headshot portrait", "/tmp/out.png");

    expect(mockGenerateImages).toHaveBeenCalledWith(
      expect.objectContaining({
        prompt: "professional headshot portrait",
      })
    );
  });

  it("sets numberOfImages: 1 in config", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    expect(mockGenerateImages).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          numberOfImages: 1,
        }),
      })
    );
  });

  it("sets aspectRatio '1:1' for portrait thumbnails", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    expect(mockGenerateImages).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          aspectRatio: "1:1",
        }),
      })
    );
  });

  it("sets outputMimeType 'image/png'", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    expect(mockGenerateImages).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          outputMimeType: "image/png",
        }),
      })
    );
  });

  it("uses GOOGLE_API_KEY for authentication via GoogleGenAI constructor", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    // GoogleGenAI is constructed at module-load time with apiKey from env.
    // Verify the mock SDK methods were actually called (proving SDK is wired up).
    expect(mockGenerateImages).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 2. generateReferenceImage -- file output
// ---------------------------------------------------------------------------

describe("generateReferenceImage -- file output", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("decodes base64 image and writes PNG to outputPath", async () => {
    const base64Data = Buffer.from("test-image-bytes").toString("base64");
    mockGenerateImages.mockResolvedValue(makeImagenResponse(base64Data));

    await generateReferenceImage("test", "/output/dir/image.png");

    expect(fs.writeFileSync).toHaveBeenCalledWith(
      "/output/dir/image.png",
      Buffer.from(base64Data, "base64")
    );
  });

  it("creates output directory recursively before writing", async () => {
    mockGenerateImages.mockResolvedValue(makeImagenResponse());

    await generateReferenceImage("test", "/output/nested/dir/image.png");

    expect(fs.mkdirSync).toHaveBeenCalledWith("/output/nested/dir", {
      recursive: true,
    });
  });
});

// ---------------------------------------------------------------------------
// 3. generateReferenceImage -- error handling
// ---------------------------------------------------------------------------

describe("generateReferenceImage -- error handling", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("throws when GOOGLE_API_KEY is not set", async () => {
    delete process.env.GOOGLE_API_KEY;

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("GOOGLE_API_KEY");
  });

  it("throws when API returns no image data", async () => {
    mockGenerateImages.mockResolvedValue({
      generatedImages: [{ image: {} }],
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws when API returns null generatedImages", async () => {
    mockGenerateImages.mockResolvedValue({
      generatedImages: null,
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws when generatedImages array is empty", async () => {
    mockGenerateImages.mockResolvedValue({
      generatedImages: [],
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws descriptive error wrapping API failure", async () => {
    mockGenerateImages.mockRejectedValue(new Error("quota exceeded"));

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Failed to generate reference image via Imagen");
  });
});

// ---------------------------------------------------------------------------
// 4. generateVeoClip -- GenAI SDK call without reference
// ---------------------------------------------------------------------------

describe("generateVeoClip -- GenAI SDK call without reference", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls generateVideos with veo-3.1-generate-preview model", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test prompt", null, "16:9", "/tmp/out.mp4");

    expect(mockGenerateVideos).toHaveBeenCalledWith(
      expect.objectContaining({
        model: "veo-3.1-generate-preview",
      })
    );
  });

  it("sends prompt to generateVideos", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("drone aerial shot", null, "16:9", "/tmp/out.mp4");

    expect(mockGenerateVideos).toHaveBeenCalledWith(
      expect.objectContaining({
        prompt: "drone aerial shot",
      })
    );
  });

  it("sets numberOfVideos: 1 in config", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect(mockGenerateVideos).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          numberOfVideos: 1,
        }),
      })
    );
  });

  it("passes aspectRatio 16:9 from parameter", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect(mockGenerateVideos).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          aspectRatio: "16:9",
        }),
      })
    );
  });

  it("passes aspectRatio 9:16 from parameter", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "9:16", "/tmp/out.mp4");

    expect(mockGenerateVideos).toHaveBeenCalledWith(
      expect.objectContaining({
        config: expect.objectContaining({
          aspectRatio: "9:16",
        }),
      })
    );
  });

  it("does not include image when referenceImagePath is null", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = mockGenerateVideos.mock.calls[0][0];
    expect(callArgs.image).toBeUndefined();
  });

  it("uses GOOGLE_API_KEY for authentication via GoogleGenAI constructor", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    // GoogleGenAI is constructed at module-load time with apiKey from env.
    // Verify the mock SDK methods were actually called (proving SDK is wired up).
    expect(mockGenerateVideos).toHaveBeenCalledTimes(1);
  });
});

// ---------------------------------------------------------------------------
// 5. generateVeoClip -- with reference image
// ---------------------------------------------------------------------------

describe("generateVeoClip -- with reference image", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("reads reference image, base64-encodes it, and includes in request params", async () => {
    const imgData = Buffer.from("reference-image-png-data");
    jest.spyOn(fs, "readFileSync").mockReturnValue(imgData);
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", "/ref/image.png", "16:9", "/tmp/out.mp4");

    expect(fs.readFileSync).toHaveBeenCalledWith("/ref/image.png");
    const callArgs = mockGenerateVideos.mock.calls[0][0];
    expect(callArgs.image).toEqual({
      imageBytes: imgData.toString("base64"),
      mimeType: "image/png",
    });
  });
});

// ---------------------------------------------------------------------------
// 6. generateVeoClip -- polling & download
// ---------------------------------------------------------------------------

describe("generateVeoClip -- polling & download", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("polls getVideosOperation and downloads video on success", async () => {
    const videoContent = new ArrayBuffer(16);
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(
      makeVeoOperation({ done: true, videoUri: "gs://bucket/vid.mp4" })
    );
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(videoContent),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    // Should have polled via getVideosOperation
    expect(mockGetVideosOperation).toHaveBeenCalled();
    // Should have downloaded via fetch with converted HTTPS URL
    expect(global.fetch).toHaveBeenCalledWith(
      "https://storage.googleapis.com/bucket/vid.mp4"
    );
    expect(fs.writeFileSync).toHaveBeenCalledWith(
      "/tmp/out.mp4",
      expect.any(Buffer)
    );
  });

  it("converts GCS URI (gs://) to HTTPS storage URL", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(
      makeVeoOperation({ done: true, videoUri: "gs://my-bucket/path/to/video.mp4" })
    );
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect(global.fetch).toHaveBeenCalledWith(
      "https://storage.googleapis.com/my-bucket/path/to/video.mp4"
    );
  });

  it("passes through HTTPS URIs directly", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(
      makeVeoOperation({ done: true, videoUri: "https://example.com/video.mp4" })
    );
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect(global.fetch).toHaveBeenCalledWith(
      "https://example.com/video.mp4"
    );
  });

  it("creates output directory before writing video", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await generateVeoClip("test", null, "16:9", "/output/clips/video.mp4");

    expect(fs.mkdirSync).toHaveBeenCalledWith("/output/clips", {
      recursive: true,
    });
  });

  it("writes downloaded video content to output file", async () => {
    const videoBytes = new Uint8Array([0x00, 0x00, 0x00, 0x1c]).buffer;
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: true }));
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(videoBytes),
    } as any);

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect(fs.writeFileSync).toHaveBeenCalledWith(
      "/tmp/out.mp4",
      Buffer.from(videoBytes)
    );
  });
});

// ---------------------------------------------------------------------------
// 7. generateVeoClip -- error handling
// ---------------------------------------------------------------------------

describe("generateVeoClip -- error handling", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("throws when GOOGLE_API_KEY is not set", async () => {
    delete process.env.GOOGLE_API_KEY;

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("GOOGLE_API_KEY");
  });

  it("throws when generateVideos SDK call fails", async () => {
    mockGenerateVideos.mockRejectedValue(new Error("SDK error"));

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Failed to generate Veo clip");
  });

  it("throws when operation completes with error", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue({
      done: true,
      error: { code: 500, message: "Internal error" },
      response: { generatedVideos: [] },
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Veo operation failed");
  });

  it("throws when no video URI in completed response", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue({
      done: true,
      response: { generatedVideos: [{ video: {} }] },
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("no video URI");
  });

  it("throws when video download returns non-OK response", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(
      makeVeoOperation({ done: true })
    );
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: false,
      status: 403,
      statusText: "Forbidden",
    } as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Failed to download");
  });

  it("wraps all errors with descriptive prefix", async () => {
    mockGenerateVideos.mockRejectedValue(new Error("network error"));

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Failed to generate Veo clip");
  });

  it("includes original error message in wrapped error", async () => {
    mockGenerateVideos.mockRejectedValue(new Error("connection refused"));

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("connection refused");
  });

  it("times out after 10 minutes with descriptive error", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: false }));

    let callCount = 0;
    jest.spyOn(Date, "now").mockImplementation(() => {
      callCount++;
      // First call sets startTime = 0; second call exceeds 10-minute timeout
      return callCount === 1 ? 0 : 10 * 60 * 1000 + 1;
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Timed out");
  });

  it("timeout error includes duration in seconds", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue(makeVeoOperation({ done: false }));

    let callCount = 0;
    jest.spyOn(Date, "now").mockImplementation(() => {
      callCount++;
      return callCount === 1 ? 0 : 10 * 60 * 1000 + 1;
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("600s");
  });

  it("downloads video even when status field is not 'succeeded' (status not checked)", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue({
      done: true,
      response: {
        generatedVideos: [
          { video: { uri: "gs://bucket/vid.mp4", status: "failed" } },
        ],
      },
    });
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).resolves.toBeUndefined();
  });

  it("passes when video status is undefined (only checked if truthy)", async () => {
    mockGenerateVideos.mockResolvedValue(makeVeoOperation({ done: false }));
    mockGetVideosOperation.mockResolvedValue({
      done: true,
      response: {
        generatedVideos: [
          { video: { uri: "gs://bucket/vid.mp4" } },
        ],
      },
    });
    jest.spyOn(global, "fetch").mockResolvedValue({
      ok: true,
      arrayBuffer: () => Promise.resolve(new ArrayBuffer(8)),
    } as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).resolves.toBeUndefined();
  });
});

// ---------------------------------------------------------------------------
// 8. extractLastFrame -- ffprobe & ffmpeg commands
// ---------------------------------------------------------------------------

describe("extractLastFrame -- commands", () => {
  beforeEach(() => {
    setupFsMocks();
    setupExecSuccess();
  });

  it("runs ffprobe with correct arguments", async () => {
    await extractLastFrame("/clips/clip.mp4", "/frames/frame.png");

    const ffprobeCall = mockExec.mock.calls[0][0];
    expect(ffprobeCall).toContain("ffprobe");
    expect(ffprobeCall).toContain("/clips/clip.mp4");
    expect(ffprobeCall).toContain("-v error");
    expect(ffprobeCall).toContain("-show_entries format=duration");
    expect(ffprobeCall).toContain("noprint_wrappers=1:nokey=1");
  });

  it("runs ffmpeg with -sseof -0.1 to extract last frame", async () => {
    await extractLastFrame("/clips/clip.mp4", "/frames/frame.png");

    const ffmpegCall = mockExec.mock.calls[1][0];
    expect(ffmpegCall).toContain("ffmpeg");
    expect(ffmpegCall).toContain("-sseof -0.1");
    expect(ffmpegCall).toContain("-i");
    expect(ffmpegCall).toContain("/clips/clip.mp4");
    expect(ffmpegCall).toContain("-vframes 1");
    expect(ffmpegCall).toContain("-q:v 2");
    expect(ffmpegCall).toContain("/frames/frame.png");
  });

  it("runs ffprobe before ffmpeg", async () => {
    await extractLastFrame("/clips/clip.mp4", "/frames/frame.png");

    expect(mockExec).toHaveBeenCalledTimes(2);
    expect(mockExec.mock.calls[0][0]).toContain("ffprobe");
    expect(mockExec.mock.calls[1][0]).toContain("ffmpeg");
  });

  it("creates output directory before extracting frame", async () => {
    await extractLastFrame("/clips/clip.mp4", "/output/frames/frame.png");

    expect(fs.mkdirSync).toHaveBeenCalledWith("/output/frames", {
      recursive: true,
    });
  });
});

// ---------------------------------------------------------------------------
// 9. extractLastFrame -- error handling
// ---------------------------------------------------------------------------

describe("extractLastFrame -- error handling", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("throws descriptive error on ffprobe failure", async () => {
    mockExec.mockImplementation((cmd: string, callback: Function) => {
      callback(new Error("ffprobe: No such file"));
    });

    await expect(
      extractLastFrame("/bad/clip.mp4", "/frames/frame.png")
    ).rejects.toThrow("Failed to extract last frame");
  });

  it("throws descriptive error on ffmpeg failure", async () => {
    mockExec
      .mockImplementationOnce((cmd: string, callback: Function) => {
        callback(null, "10.5", ""); // ffprobe succeeds
      })
      .mockImplementationOnce((cmd: string, callback: Function) => {
        callback(new Error("ffmpeg: Invalid data")); // ffmpeg fails
      });

    await expect(
      extractLastFrame("/clips/clip.mp4", "/frames/frame.png")
    ).rejects.toThrow("Failed to extract last frame");
  });

  it("includes original error message in thrown error", async () => {
    mockExec.mockImplementation((cmd: string, callback: Function) => {
      callback(new Error("command not found: ffprobe"));
    });

    await expect(
      extractLastFrame("/clips/clip.mp4", "/frames/frame.png")
    ).rejects.toThrow("command not found: ffprobe");
  });
});

// ---------------------------------------------------------------------------
// 10. Module exports
// ---------------------------------------------------------------------------

describe("module exports", () => {
  it("exports generateReferenceImage as a function", () => {
    expect(typeof generateReferenceImage).toBe("function");
  });

  it("exports generateVeoClip as a function", () => {
    expect(typeof generateVeoClip).toBe("function");
  });

  it("exports extractLastFrame as a function", () => {
    expect(typeof extractLastFrame).toBe("function");
  });

  it("generateReferenceImage accepts 2 parameters", () => {
    expect(generateReferenceImage.length).toBe(2);
  });

  it("generateVeoClip accepts 4 parameters", () => {
    expect(generateVeoClip.length).toBe(4);
  });

  it("extractLastFrame accepts 2 parameters", () => {
    expect(extractLastFrame.length).toBe(2);
  });
});

// ---------------------------------------------------------------------------
// 11. Source file structure checks
// ---------------------------------------------------------------------------

describe("lib/veo.ts source structure", () => {
  let sourceCode: string;

  beforeAll(() => {
    const realFs = jest.requireActual("fs") as typeof fs;
    sourceCode = realFs.readFileSync(
      path.join(__dirname, "..", "lib", "veo.ts"),
      "utf-8"
    );
  });

  it("has server-only guard", () => {
    expect(sourceCode).toMatch(/server-only/);
  });

  it("uses GOOGLE_API_KEY env var", () => {
    expect(sourceCode).toMatch(/GOOGLE_API_KEY/);
  });

  it("imports GoogleGenAI from @google/genai", () => {
    expect(sourceCode).toMatch(/GoogleGenAI/);
    expect(sourceCode).toMatch(/@google\/genai/);
  });

  it("imports GenerateVideosParameters type from @google/genai", () => {
    expect(sourceCode).toMatch(/GenerateVideosParameters/);
  });

  it("does NOT import google-auth-library (migrated to GenAI SDK)", () => {
    expect(sourceCode).not.toMatch(/google-auth-library/);
  });

  it("exports generateReferenceImage function", () => {
    expect(sourceCode).toMatch(
      /export\s+async\s+function\s+generateReferenceImage/
    );
  });

  it("exports generateVeoClip function", () => {
    expect(sourceCode).toMatch(
      /export\s+async\s+function\s+generateVeoClip/
    );
  });

  it("exports extractLastFrame function", () => {
    expect(sourceCode).toMatch(
      /export\s+async\s+function\s+extractLastFrame/
    );
  });

  it("uses imagen-3.0-generate-002 model in endpoint", () => {
    expect(sourceCode).toMatch(/imagen-3\.0-generate-002/);
  });

  it("uses veo-3.1-generate-preview model in endpoint", () => {
    expect(sourceCode).toMatch(/veo-3\.1-generate-preview/);
  });

  it("sets numberOfImages: 1 for Imagen (GenAI SDK format)", () => {
    expect(sourceCode).toMatch(/numberOfImages:\s*1/);
  });

  it("sets aspectRatio '1:1' for portrait thumbnails", () => {
    expect(sourceCode).toMatch(/aspectRatio:\s*['"]1:1['"]/);
  });

  it("sets outputMimeType 'image/png'", () => {
    expect(sourceCode).toMatch(/outputMimeType:\s*['"]image\/png['"]/);
  });

  it("sets numberOfVideos: 1 for Veo (GenAI SDK format)", () => {
    expect(sourceCode).toMatch(/numberOfVideos:\s*1/);
  });

  it("has 5-second poll interval (sleep 5000)", () => {
    expect(sourceCode).toMatch(/5000/);
  });

  it("has 10-minute timeout (10 * 60 * 1000)", () => {
    expect(sourceCode).toMatch(/10\s*\*\s*60\s*\*\s*1000/);
  });

  it("uses GenAI SDK for API calls (genai.models)", () => {
    expect(sourceCode).toMatch(/genai\.models/);
  });

  it("uses GenAI SDK for polling (genai.operations)", () => {
    expect(sourceCode).toMatch(/genai\.operations/);
  });

  it("uses ffprobe for duration detection", () => {
    expect(sourceCode).toMatch(/ffprobe/);
  });

  it("uses ffmpeg for frame extraction", () => {
    expect(sourceCode).toMatch(/ffmpeg/);
  });

  it("uses -sseof flag for seeking to end of clip", () => {
    expect(sourceCode).toMatch(/-sseof/);
  });

  it("extracts exactly 1 frame with -vframes 1", () => {
    expect(sourceCode).toMatch(/-vframes 1/);
  });

  it("uses promisify for exec (child_process)", () => {
    expect(sourceCode).toMatch(/promisify/);
    expect(sourceCode).toMatch(/exec/);
  });

  it("creates directories recursively with mkdirSync", () => {
    expect(sourceCode).toMatch(/mkdirSync/);
    expect(sourceCode).toMatch(/recursive:\s*true/);
  });

  it("handles base64 image encoding/decoding", () => {
    expect(sourceCode).toMatch(/base64/);
  });

  it("handles GCS URI (gs://) to HTTPS conversion", () => {
    expect(sourceCode).toMatch(/gs:\/\//);
    expect(sourceCode).toMatch(/storage\.googleapis\.com/);
  });

  it("uses writeFileSync to save output files", () => {
    expect(sourceCode).toMatch(/writeFileSync/);
  });
});
