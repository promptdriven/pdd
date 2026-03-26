import path from "path";

const mockWriteFileSync = jest.fn();
const mockMkdirSync = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
    mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
  },
  writeFileSync: (...args: unknown[]) => mockWriteFileSync(...args),
  mkdirSync: (...args: unknown[]) => mockMkdirSync(...args),
}));

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => process.cwd(),
}));

import { POST } from "../app/api/pipeline/tts-render/audio/route";

function makeRequest(body: unknown): Request {
  return new Request("http://localhost/api/pipeline/tts-render/audio", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

beforeEach(() => {
  mockWriteFileSync.mockReset();
  mockMkdirSync.mockReset();
});

describe("POST /api/pipeline/tts-render/audio", () => {
  it("writes restored segment WAV files into outputs/tts", async () => {
    const response = await POST(
      makeRequest({
        segments: [
          {
            segmentId: "part1_economics_005",
            audioBase64: "UklGRg==",
          },
        ],
      }) as any,
    );

    expect(response.status).toBe(200);
    expect(mockMkdirSync).toHaveBeenCalledWith(
      path.join(process.cwd(), "outputs", "tts"),
      { recursive: true },
    );
    expect(mockWriteFileSync).toHaveBeenCalledWith(
      path.join(process.cwd(), "outputs", "tts", "part1_economics_005.wav"),
      expect.any(Buffer),
    );
  });

  it("rejects invalid segment ids", async () => {
    const response = await POST(
      makeRequest({
        segments: [
          {
            segmentId: "../escape",
            audioBase64: "UklGRg==",
          },
        ],
      }) as any,
    );

    expect(response.status).toBe(400);
    await expect(response.json()).resolves.toEqual({
      error: "Invalid segment restore payload",
    });
  });
});
