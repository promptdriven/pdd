/**
 * Tests for app/api/pipeline/compositions/preview/route.ts
 *
 * Verifies the preview endpoint:
 *   1. Returns 400 if component query param is missing
 *   2. Resolves componentName → compositionId via project.json
 *   3. Calls renderStill with compositionId, frame 30, output path
 *   4. Returns JSON { url } pointing to raw image endpoint
 *   5. Serves cached PNG when raw=1
 *   6. Returns 404 when compositionId cannot be resolved
 *   7. Returns 500 when renderStill fails
 */

// ---------------------------------------------------------------------------
// Mocks
// ---------------------------------------------------------------------------

const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

const mockRenderStill = jest.fn();

jest.mock("@/lib/render", () => ({
  renderStill: (...args: unknown[]) => mockRenderStill(...args),
}));

const mockExistsSync = jest.fn();
const mockStatSync = jest.fn();
const mockCreateReadStream = jest.fn();

jest.mock("fs", () => ({
  __esModule: true,
  default: {
    existsSync: (...args: unknown[]) => mockExistsSync(...args),
    statSync: (...args: unknown[]) => mockStatSync(...args),
    createReadStream: (...args: unknown[]) => mockCreateReadStream(...args),
  },
  existsSync: (...args: unknown[]) => mockExistsSync(...args),
  statSync: (...args: unknown[]) => mockStatSync(...args),
  createReadStream: (...args: unknown[]) => mockCreateReadStream(...args),
}));

// Mock stream.Readable.toWeb
jest.mock("stream", () => ({
  __esModule: true,
  Readable: {
    toWeb: () => new ReadableStream(),
  },
}));

// Import after mocks
import { GET } from "../app/api/pipeline/compositions/preview/route";
import { NextRequest } from "next/server";

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeRequest(url: string): NextRequest {
  return new NextRequest(new URL(url, "http://localhost"));
}

const DEFAULT_PROJECT = {
  sections: [
    {
      id: "cold_open",
      label: "Cold Open",
      compositionId: "ColdOpenSection",
      compositions: ["cold_open_title_card"],
      specDir: "cold_open",
    },
    {
      id: "part1_economics",
      label: "Part 1",
      compositionId: "Part1Economics",
      compositions: ["part1_economics_stat_callout_gitclear", "part1_economics_stat_callout_github"],
      specDir: "part1_economics",
    },
    {
      id: "part3_mold",
      label: "Part 3: The Mold",
      compositionId: "Part3MoldThreeParts",
      compositions: ["part3_mold_title_card", "part3_mold_stat_callout_coderabbit"],
      specDir: "03-mold-has-three-parts",
    },
  ],
};

// ---------------------------------------------------------------------------
// Setup
// ---------------------------------------------------------------------------

beforeEach(() => {
  jest.clearAllMocks();
  mockLoadProject.mockReturnValue(DEFAULT_PROJECT);
  mockRenderStill.mockResolvedValue(undefined);
  mockExistsSync.mockReturnValue(false);
});

// ---------------------------------------------------------------------------
// 1. Missing component param
// ---------------------------------------------------------------------------

describe("GET — missing component param", () => {
  it("returns 400 when component is missing", async () => {
    const res = await GET(makeRequest("http://localhost/api/pipeline/compositions/preview"));
    expect(res.status).toBe(400);
    const body = await res.json();
    expect(body.error).toMatch(/missing/i);
  });
});

// ---------------------------------------------------------------------------
// 2. Render still and return URL
// ---------------------------------------------------------------------------

describe("GET — render still", () => {
  it("calls renderStill with hyphenated composition ID (underscores invalid in Remotion)", async () => {
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&section=cold_open")
    );
    expect(res.status).toBe(200);
    expect(mockRenderStill).toHaveBeenCalledTimes(1);
    // Remotion IDs cannot contain underscores — must be hyphenated
    expect(mockRenderStill.mock.calls[0][0]).toBe("cold-open-title-card");
    expect(mockRenderStill.mock.calls[0][1]).toBe(30); // frame = FPS
  });

  it("returns JSON with url field", async () => {
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&section=cold_open")
    );
    const body = await res.json();
    expect(body.url).toContain("component=title_card");
    expect(body.url).toContain("raw=1");
  });

  it("renders different compositions for different components in the same section", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=stat_callout_gitclear&section=part1_economics")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("part1-economics-stat-callout-gitclear");

    mockRenderStill.mockClear();

    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=stat_callout_github&section=part1_economics")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("part1-economics-stat-callout-github");
  });

  it("resolves fallback _main component to section compositionId", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=cold_open_main")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("ColdOpenSection");
  });

  it("resolves wrapper component to section compositionId", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=ColdOpenSectionWrapper")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("ColdOpenSection");
  });
});

// ---------------------------------------------------------------------------
// 2b. Section disambiguation
// ---------------------------------------------------------------------------

describe("GET — section disambiguation", () => {
  it("resolves title_card to cold-open-title-card without section param (first match)", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("cold-open-title-card");
  });

  it("resolves title_card to part3-mold-title-card when section=part3_mold", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&section=part3_mold")
    );
    expect(mockRenderStill.mock.calls[0][0]).toBe("part3-mold-title-card");
  });

  it("includes section param in returned url", async () => {
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&section=part3_mold")
    );
    const body = await res.json();
    expect(body.url).toContain("section=part3_mold");
    expect(body.url).toContain("raw=1");
  });

  it("uses section-scoped filename to avoid cache collisions", async () => {
    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&section=part3_mold")
    );
    const outputPath = mockRenderStill.mock.calls[0][2] as string;
    expect(outputPath).toContain("part3_mold--title_card");
  });
});

// ---------------------------------------------------------------------------
// 3. Serve cached PNG (raw=1)
// ---------------------------------------------------------------------------

describe("GET — serve raw PNG", () => {
  it("returns 404 when PNG does not exist", async () => {
    mockExistsSync.mockReturnValue(false);
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&raw=1")
    );
    expect(res.status).toBe(404);
  });

  it("serves PNG with image/png content type when file exists", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockReturnValue({ size: 1234 });
    mockCreateReadStream.mockReturnValue({});

    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&raw=1")
    );
    expect(res.status).toBe(200);
    expect(res.headers.get("Content-Type")).toBe("image/png");
    expect(res.headers.get("Content-Length")).toBe("1234");
  });

  it("does not call renderStill when serving raw", async () => {
    mockExistsSync.mockReturnValue(true);
    mockStatSync.mockReturnValue({ size: 100 });
    mockCreateReadStream.mockReturnValue({});

    await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card&raw=1")
    );
    expect(mockRenderStill).not.toHaveBeenCalled();
  });
});

// ---------------------------------------------------------------------------
// 4. Error cases
// ---------------------------------------------------------------------------

describe("GET — error cases", () => {
  it("returns 404 when compositionId cannot be resolved", async () => {
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=nonexistent")
    );
    expect(res.status).toBe(404);
    const body = await res.json();
    expect(body.error).toMatch(/cannot resolve/i);
  });

  it("returns 500 when renderStill throws", async () => {
    mockRenderStill.mockRejectedValue(new Error("Bundle not found"));
    const res = await GET(
      makeRequest("http://localhost/api/pipeline/compositions/preview?component=title_card")
    );
    expect(res.status).toBe(500);
    const body = await res.json();
    expect(body.error).toBe("Bundle not found");
  });
});
