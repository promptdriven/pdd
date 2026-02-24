/**
 * Tests for lib/veo.ts (Vertex AI REST API implementation)
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification.
 *
 * Spec requirements verified:
 *   1. Export generateReferenceImage(prompt, outputPath) -> Promise<void>
 *   2. Export generateVeoClip(prompt, refImagePath | null, aspectRatio, outputPath) -> Promise<void>
 *   3. Export extractLastFrame(clipPath, outputPath) -> Promise<void>
 *   4. Use GOOGLE_CLOUD_PROJECT + GOOGLE_CLOUD_LOCATION + ADC for auth
 *   5. Imagen via Vertex AI REST: sampleCount: 1, aspectRatio: '1:1', outputMimeType: 'image/png'
 *   6. Veo via Vertex AI REST: numberOfVideos: 1, aspectRatio from param, durationSeconds: 8
 *   7. Poll every 5s; timeout after 10 min
 *   8. import 'server-only' guard
 *   9. Uses ffprobe and ffmpeg for frame extraction
 *  10. Ensures output directories exist before writing
 *  11. GCS URI to HTTPS conversion for video download
 *  12. Descriptive errors on all failure paths
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Mock google-auth-library
// ---------------------------------------------------------------------------

const mockGetAccessToken = jest.fn().mockResolvedValue({ token: "test-access-token" });
const mockGetClient = jest.fn().mockResolvedValue({ getAccessToken: mockGetAccessToken });

jest.mock("google-auth-library", () => ({
  GoogleAuth: jest.fn().mockImplementation(() => ({
    getClient: mockGetClient,
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

const ORIGINAL_PROJECT = process.env.GOOGLE_CLOUD_PROJECT;
const ORIGINAL_LOCATION = process.env.GOOGLE_CLOUD_LOCATION;
const ORIGINAL_FETCH = global.fetch;

function setupEnvVars() {
  process.env.GOOGLE_CLOUD_PROJECT = "test-project-123";
  process.env.GOOGLE_CLOUD_LOCATION = "us-central1";
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

function mockFetchSequence(...responses: Array<{ ok: boolean; status?: number; statusText?: string; json?: () => Promise<any>; text?: () => Promise<string>; arrayBuffer?: () => Promise<ArrayBuffer> }>) {
  let callIdx = 0;
  jest.spyOn(global, "fetch").mockImplementation(async () => {
    const resp = responses[callIdx] ?? responses[responses.length - 1];
    callIdx++;
    return resp as any;
  });
}

function makeImagenFetchResponse(base64 = "dGVzdC1pbWFnZQ==") {
  return {
    ok: true,
    statusText: "OK",
    json: () =>
      Promise.resolve({
        predictions: [{ bytesBase64Encoded: base64 }],
      }),
  };
}

function makeVeoStartResponse(name = "projects/test/locations/us-central1/operations/veo-op-123") {
  return {
    ok: true,
    statusText: "OK",
    json: () => Promise.resolve({ name }),
  };
}

function makeVeoPollResponse(
  uri = "gs://bucket/video.mp4",
  done = true,
  videoStatus = "succeeded",
  error?: object
) {
  return {
    ok: true,
    statusText: "OK",
    json: () =>
      Promise.resolve({
        done,
        ...(error ? { error } : {}),
        response: done
          ? {
              generatedVideos: [
                { video: { uri, status: videoStatus } },
              ],
            }
          : undefined,
      }),
  };
}

function makeDownloadResponse(body: ArrayBuffer = new ArrayBuffer(8)) {
  return {
    ok: true,
    statusText: "OK",
    arrayBuffer: () => Promise.resolve(body),
  };
}

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  setupEnvVars();
  jest.clearAllMocks();
  mockGetAccessToken.mockResolvedValue({ token: "test-access-token" });
  mockGetClient.mockResolvedValue({ getAccessToken: mockGetAccessToken });
});

afterEach(() => {
  jest.restoreAllMocks();
  global.fetch = ORIGINAL_FETCH;
  if (ORIGINAL_PROJECT !== undefined) {
    process.env.GOOGLE_CLOUD_PROJECT = ORIGINAL_PROJECT;
  } else {
    delete process.env.GOOGLE_CLOUD_PROJECT;
  }
  if (ORIGINAL_LOCATION !== undefined) {
    process.env.GOOGLE_CLOUD_LOCATION = ORIGINAL_LOCATION;
  } else {
    delete process.env.GOOGLE_CLOUD_LOCATION;
  }
});

// ---------------------------------------------------------------------------
// 1. generateReferenceImage -- Vertex AI Imagen REST call
// ---------------------------------------------------------------------------

describe("generateReferenceImage -- Vertex AI REST call", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls Imagen predict endpoint with correct URL", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("test prompt", "/tmp/out.png");

    expect(global.fetch).toHaveBeenCalledWith(
      expect.stringContaining("imagen-3.0-generate-002:predict"),
      expect.any(Object)
    );
  });

  it("sends prompt in instances array", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("professional headshot portrait", "/tmp/out.png");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.instances).toEqual([{ prompt: "professional headshot portrait" }]);
  });

  it("sets sampleCount: 1 in parameters", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.parameters.sampleCount).toBe(1);
  });

  it("sets aspectRatio '1:1' for portrait thumbnails", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.parameters.aspectRatio).toBe("1:1");
  });

  it("sets outputMimeType 'image/png'", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.parameters.outputMimeType).toBe("image/png");
  });

  it("includes Bearer token in Authorization header", async () => {
    mockFetchSequence(makeImagenFetchResponse());

    await generateReferenceImage("test", "/tmp/out.png");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    expect(callArgs[1].headers.Authorization).toBe("Bearer test-access-token");
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
    mockFetchSequence(makeImagenFetchResponse(base64Data));

    await generateReferenceImage("test", "/output/dir/image.png");

    expect(fs.writeFileSync).toHaveBeenCalledWith(
      "/output/dir/image.png",
      Buffer.from(base64Data, "base64")
    );
  });

  it("creates output directory recursively before writing", async () => {
    mockFetchSequence(makeImagenFetchResponse());

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

  it("throws when GOOGLE_CLOUD_PROJECT is not set", async () => {
    delete process.env.GOOGLE_CLOUD_PROJECT;

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("GOOGLE_CLOUD_PROJECT");
  });

  it("throws when API returns no predictions", async () => {
    mockFetchSequence({
      ok: true,
      statusText: "OK",
      json: () => Promise.resolve({ predictions: [] }),
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws when API returns null predictions", async () => {
    mockFetchSequence({
      ok: true,
      statusText: "OK",
      json: () => Promise.resolve({ predictions: null }),
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws when prediction has no bytesBase64Encoded", async () => {
    mockFetchSequence({
      ok: true,
      statusText: "OK",
      json: () =>
        Promise.resolve({ predictions: [{ bytesBase64Encoded: null }] }),
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Imagen");
  });

  it("throws descriptive error wrapping API failure", async () => {
    mockFetchSequence({
      ok: false,
      status: 429,
      statusText: "Too Many Requests",
      text: () => Promise.resolve("quota exceeded"),
    });

    await expect(
      generateReferenceImage("test", "/tmp/out.png")
    ).rejects.toThrow("Failed to generate reference image via Imagen");
  });
});

// ---------------------------------------------------------------------------
// 4. generateVeoClip -- Vertex AI REST call without reference
// ---------------------------------------------------------------------------

describe("generateVeoClip -- Vertex AI REST call without reference", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("calls Veo generateVideo endpoint with correct URL", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test prompt", null, "16:9", "/tmp/out.mp4");

    expect((global.fetch as jest.Mock).mock.calls[0][0]).toContain(
      "veo-3.1-generate-preview:generateVideo"
    );
  });

  it("sends prompt in request body", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("drone aerial shot", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.prompt).toBe("drone aerial shot");
  });

  it("sets numberOfVideos: 1", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.config.numberOfVideos).toBe(1);
  });

  it("passes aspectRatio 16:9 from parameter", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.config.aspectRatio).toBe("16:9");
  });

  it("passes aspectRatio 9:16 from parameter", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "9:16", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.config.aspectRatio).toBe("9:16");
  });

  it("sets durationSeconds: 8 default", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.config.durationSeconds).toBe(8);
  });

  it("does not include image when referenceImagePath is null", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.image).toBeUndefined();
  });

  it("includes Bearer token in Authorization header", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    expect(callArgs[1].headers.Authorization).toBe("Bearer test-access-token");
  });
});

// ---------------------------------------------------------------------------
// 5. generateVeoClip -- with reference image
// ---------------------------------------------------------------------------

describe("generateVeoClip -- with reference image", () => {
  beforeEach(() => {
    setupFsMocks();
  });

  it("reads reference image, base64-encodes it, and includes in request body", async () => {
    const imgData = Buffer.from("reference-image-png-data");
    jest.spyOn(fs, "readFileSync").mockReturnValue(imgData);
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", "/ref/image.png", "16:9", "/tmp/out.mp4");

    expect(fs.readFileSync).toHaveBeenCalledWith("/ref/image.png");
    const callArgs = (global.fetch as jest.Mock).mock.calls[0];
    const body = JSON.parse(callArgs[1].body);
    expect(body.image).toEqual({
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

  it("polls operation endpoint and downloads video on success", async () => {
    const videoContent = new ArrayBuffer(16);
    mockFetchSequence(
      makeVeoStartResponse("projects/test/locations/us-central1/operations/op-1"),
      makeVeoPollResponse("gs://bucket/vid.mp4"),
      makeDownloadResponse(videoContent)
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    // Second fetch call should be the poll
    expect((global.fetch as jest.Mock).mock.calls[1][0]).toContain("operations/op-1");
    // Third call should be the download
    expect((global.fetch as jest.Mock).mock.calls[2][0]).toBe(
      "https://storage.googleapis.com/bucket/vid.mp4"
    );
    expect(fs.writeFileSync).toHaveBeenCalledWith(
      "/tmp/out.mp4",
      expect.any(Buffer)
    );
  });

  it("converts GCS URI (gs://) to HTTPS storage URL", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse("gs://my-bucket/path/to/video.mp4"),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect((global.fetch as jest.Mock).mock.calls[2][0]).toBe(
      "https://storage.googleapis.com/my-bucket/path/to/video.mp4"
    );
  });

  it("passes through HTTPS URIs directly", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse("https://example.com/video.mp4"),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/tmp/out.mp4");

    expect((global.fetch as jest.Mock).mock.calls[2][0]).toBe(
      "https://example.com/video.mp4"
    );
  });

  it("creates output directory before writing video", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse()
    );

    await generateVeoClip("test", null, "16:9", "/output/clips/video.mp4");

    expect(fs.mkdirSync).toHaveBeenCalledWith("/output/clips", {
      recursive: true,
    });
  });

  it("writes downloaded video content to output file", async () => {
    const videoBytes = new Uint8Array([0x00, 0x00, 0x00, 0x1c]).buffer;
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse(),
      makeDownloadResponse(videoBytes)
    );

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

  it("throws when GOOGLE_CLOUD_PROJECT is not set", async () => {
    delete process.env.GOOGLE_CLOUD_PROJECT;

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("GOOGLE_CLOUD_PROJECT");
  });

  it("throws when operation has no name", async () => {
    mockFetchSequence({
      ok: true,
      statusText: "OK",
      json: () => Promise.resolve({}),
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("valid operation name");
  });

  it("throws when operation completes with error", async () => {
    mockFetchSequence(
      makeVeoStartResponse(),
      makeVeoPollResponse("gs://b/v.mp4", true, "succeeded", { code: 500, message: "Internal error" })
    );

    // The error field triggers the error path
    const pollResp = {
      ok: true,
      statusText: "OK",
      json: () =>
        Promise.resolve({
          done: true,
          error: { code: 500, message: "Internal error" },
        }),
    };
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse() as any)
      .mockResolvedValueOnce(pollResp as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Veo operation failed");
  });

  it("throws when no video URI in completed response", async () => {
    const pollResp = {
      ok: true,
      statusText: "OK",
      json: () =>
        Promise.resolve({
          done: true,
          response: { generatedVideos: [{ video: {} }] },
        }),
    };
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse() as any)
      .mockResolvedValueOnce(pollResp as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("no video URI");
  });

  it("throws when video download returns non-OK response", async () => {
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse() as any)
      .mockResolvedValueOnce(makeVeoPollResponse() as any)
      .mockResolvedValueOnce({
        ok: false,
        statusText: "Forbidden",
      } as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Failed to download");
  });

  it("wraps all errors with descriptive prefix", async () => {
    jest.spyOn(global, "fetch").mockRejectedValue(new Error("network error"));

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("Failed to generate Veo clip");
  });

  it("includes original error message in wrapped error", async () => {
    jest.spyOn(global, "fetch").mockRejectedValue(new Error("connection refused"));

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("connection refused");
  });

  it("times out after 10 minutes with descriptive error", async () => {
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse("projects/test/locations/us-central1/operations/slow") as any);

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

  it("timeout error includes operation name", async () => {
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse("projects/test/locations/us-central1/operations/my-op-456") as any);

    let callCount = 0;
    jest.spyOn(Date, "now").mockImplementation(() => {
      callCount++;
      return callCount === 1 ? 0 : 10 * 60 * 1000 + 1;
    });

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("my-op-456");
  });

  it("throws when video status is not succeeded", async () => {
    const pollResp = {
      ok: true,
      statusText: "OK",
      json: () =>
        Promise.resolve({
          done: true,
          response: {
            generatedVideos: [
              { video: { uri: "gs://bucket/vid.mp4", status: "failed" } },
            ],
          },
        }),
    };
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse() as any)
      .mockResolvedValueOnce(pollResp as any);

    await expect(
      generateVeoClip("test", null, "16:9", "/tmp/out.mp4")
    ).rejects.toThrow("failed");
  });

  it("passes when video status is undefined (only checked if truthy)", async () => {
    const pollResp = {
      ok: true,
      statusText: "OK",
      json: () =>
        Promise.resolve({
          done: true,
          response: {
            generatedVideos: [
              { video: { uri: "gs://bucket/vid.mp4" } },
            ],
          },
        }),
    };
    jest.spyOn(global, "fetch")
      .mockResolvedValueOnce(makeVeoStartResponse() as any)
      .mockResolvedValueOnce(pollResp as any)
      .mockResolvedValueOnce(makeDownloadResponse() as any);

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
    ).rejects.toThrow("Failed to extract last frame from clip");
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
    ).rejects.toThrow("Failed to extract last frame from clip");
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

  it("uses GOOGLE_CLOUD_PROJECT env var", () => {
    expect(sourceCode).toMatch(/GOOGLE_CLOUD_PROJECT/);
  });

  it("uses GOOGLE_CLOUD_LOCATION env var", () => {
    expect(sourceCode).toMatch(/GOOGLE_CLOUD_LOCATION/);
  });

  it("imports GoogleAuth from google-auth-library", () => {
    expect(sourceCode).toMatch(/GoogleAuth/);
    expect(sourceCode).toMatch(/google-auth-library/);
  });

  it("does NOT import @google/genai (migrated away)", () => {
    expect(sourceCode).not.toMatch(/@google\/genai/);
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

  it("sets sampleCount: 1 for Imagen (Vertex AI format)", () => {
    expect(sourceCode).toMatch(/sampleCount:\s*1/);
  });

  it("sets aspectRatio '1:1' for portrait thumbnails", () => {
    expect(sourceCode).toMatch(/aspectRatio:\s*['"]1:1['"]/);
  });

  it("sets outputMimeType 'image/png'", () => {
    expect(sourceCode).toMatch(/outputMimeType:\s*['"]image\/png['"]/);
  });

  it("sets numberOfVideos: 1 for Veo", () => {
    expect(sourceCode).toMatch(/numberOfVideos:\s*1/);
  });

  it("sets durationSeconds: 8 default", () => {
    expect(sourceCode).toMatch(/durationSeconds:\s*8/);
  });

  it("has 5-second poll interval (sleep 5000)", () => {
    expect(sourceCode).toMatch(/5000/);
  });

  it("has 10-minute timeout (10 * 60 * 1000)", () => {
    expect(sourceCode).toMatch(/10\s*\*\s*60\s*\*\s*1000/);
  });

  it("uses Vertex AI REST endpoint pattern", () => {
    expect(sourceCode).toMatch(/aiplatform\.googleapis\.com/);
  });

  it("uses Bearer token authentication", () => {
    expect(sourceCode).toMatch(/Bearer/);
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
