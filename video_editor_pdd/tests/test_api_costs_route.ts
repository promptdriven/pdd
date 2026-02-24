/**
 * Tests for app/api/costs/route.ts
 *
 * Spec requirements verified:
 *   1. GET /api/costs — returns cost summary by stage
 *   2. Returns totalCost, byStage array
 *   3. Each stage entry has totalCost, totalInputTokens, totalOutputTokens, callCount
 *   4. Returns 500 on internal error
 *   5. Export dynamic = 'force-dynamic'
 */

// ---------------------------------------------------------------------------
// Mocks — must be declared before importing the module under test
// ---------------------------------------------------------------------------

const mockAll = jest.fn();
const mockGet = jest.fn();
const mockPrepare = jest.fn(() => ({
  all: mockAll,
  get: mockGet,
}));
const mockDb = { prepare: mockPrepare };
const mockGetDb = jest.fn(() => mockDb);

jest.mock("@/lib/db", () => ({
  getDb: () => mockGetDb(),
}));

// Import after mock setup
import { GET, dynamic } from "../app/api/costs/route";

// ---------------------------------------------------------------------------
// Setup / Teardown
// ---------------------------------------------------------------------------

beforeEach(() => {
  mockGetDb.mockReset();
  mockGetDb.mockReturnValue(mockDb);
  mockPrepare.mockReset();
  mockPrepare.mockReturnValue({ all: mockAll, get: mockGet });
  mockAll.mockReset();
  mockGet.mockReset();
  jest.spyOn(console, "error").mockImplementation(() => {});
});

afterEach(() => {
  jest.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. dynamic export
// ---------------------------------------------------------------------------

describe("dynamic export", () => {
  it("exports dynamic as 'force-dynamic'", () => {
    expect(dynamic).toBe("force-dynamic");
  });
});

// ---------------------------------------------------------------------------
// 2. GET /api/costs — successful response
// ---------------------------------------------------------------------------

describe("GET /api/costs — successful response", () => {
  it("returns 200 status", async () => {
    mockAll.mockReturnValue([]);
    mockGet.mockReturnValue({ total: 0 });

    const response = await GET();
    expect(response.status).toBe(200);
  });

  it("returns totalCost from the SUM query", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { all: () => [] };
      return { get: () => ({ total: 42.5 }) };
    });

    const response = await GET();
    const body = await response.json();
    expect(body.totalCost).toBe(42.5);
  });

  it("returns totalCost as 0 when no costs exist", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { all: () => [] };
      return { get: () => ({ total: null }) };
    });

    const response = await GET();
    const body = await response.json();
    expect(body.totalCost).toBe(0);
  });

  it("returns byStage array with stage cost breakdowns", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) {
        return {
          all: () => [
            { stage: "tts-render", totalCost: 10.5, totalInputTokens: 1000, totalOutputTokens: 500, callCount: 3 },
            { stage: "veo", totalCost: 30.0, totalInputTokens: 5000, totalOutputTokens: 2000, callCount: 5 },
          ],
        };
      }
      return { get: () => ({ total: 40.5 }) };
    });

    const response = await GET();
    const body = await response.json();

    expect(body.byStage).toHaveLength(2);
    expect(body.byStage[0].stage).toBe("tts-render");
    expect(body.byStage[0].totalCost).toBe(10.5);
    expect(body.byStage[0].totalInputTokens).toBe(1000);
    expect(body.byStage[0].totalOutputTokens).toBe(500);
    expect(body.byStage[0].callCount).toBe(3);
    expect(body.byStage[1].stage).toBe("veo");
  });

  it("returns empty byStage array when no costs exist", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) return { all: () => [] };
      return { get: () => ({ total: null }) };
    });

    const response = await GET();
    const body = await response.json();
    expect(body.byStage).toEqual([]);
  });

  it("defaults null values to 0 in stage rows", async () => {
    let callCount = 0;
    mockPrepare.mockImplementation(() => {
      callCount++;
      if (callCount === 1) {
        return {
          all: () => [
            { stage: "setup", totalCost: null, totalInputTokens: null, totalOutputTokens: null, callCount: null },
          ],
        };
      }
      return { get: () => ({ total: 0 }) };
    });

    const response = await GET();
    const body = await response.json();

    expect(body.byStage[0].totalCost).toBe(0);
    expect(body.byStage[0].totalInputTokens).toBe(0);
    expect(body.byStage[0].totalOutputTokens).toBe(0);
    expect(body.byStage[0].callCount).toBe(0);
  });
});

// ---------------------------------------------------------------------------
// 3. GET /api/costs — error handling
// ---------------------------------------------------------------------------

describe("GET /api/costs — error handling", () => {
  it("returns 500 when getDb throws", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET();
    expect(response.status).toBe(500);
  });

  it("returns { error: 'Internal Server Error' } body on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("DB connection failed");
    });

    const response = await GET();
    const body = await response.json();
    expect(body).toEqual({ error: "Internal Server Error" });
  });

  it("logs error to console.error on failure", async () => {
    mockGetDb.mockImplementation(() => {
      throw new Error("Unexpected error");
    });

    await GET();
    expect(console.error).toHaveBeenCalled();
  });
});
