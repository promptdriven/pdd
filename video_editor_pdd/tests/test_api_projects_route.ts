const mockListProjectWorkspaces = jest.fn();
const mockGetCurrentProjectWorkspace = jest.fn();
const mockResolveProjectWorkspace = jest.fn();
const mockSetSelectedProjectId = jest.fn();

jest.mock("@/lib/projects", () => ({
  listProjectWorkspaces: (...args: unknown[]) => mockListProjectWorkspaces(...args),
  getCurrentProjectWorkspace: (...args: unknown[]) => mockGetCurrentProjectWorkspace(...args),
  resolveProjectWorkspace: (...args: unknown[]) => mockResolveProjectWorkspace(...args),
  setSelectedProjectId: (...args: unknown[]) => mockSetSelectedProjectId(...args),
}));

import { GET } from "../app/api/projects/route";
import { POST } from "../app/api/projects/select/route";

describe("GET /api/projects", () => {
  beforeEach(() => {
    jest.resetAllMocks();
  });

  it("returns the discovered projects and selected project id", async () => {
    mockListProjectWorkspaces.mockReturnValue([
      { id: "alpha", name: "alpha", dir: "/tmp/alpha", dbPath: "/tmp/alpha/pipeline.db" },
      { id: "beta", name: "beta", dir: "/tmp/beta", dbPath: "/tmp/beta/pipeline.db" },
    ]);
    mockGetCurrentProjectWorkspace.mockReturnValue({
      id: "beta",
      name: "beta",
      dir: "/tmp/beta",
      dbPath: "/tmp/beta/pipeline.db",
    });

    const response = await GET();
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(body.projects).toEqual([
      { id: "alpha", name: "alpha" },
      { id: "beta", name: "beta" },
    ]);
    expect(body.selectedProjectId).toBe("beta");
  });
});

describe("POST /api/projects/select", () => {
  beforeEach(() => {
    jest.resetAllMocks();
  });

  it("persists a valid selected project", async () => {
    mockResolveProjectWorkspace.mockReturnValue({
      id: "beta",
      name: "beta",
      dir: "/tmp/beta",
      dbPath: "/tmp/beta/pipeline.db",
    });

    const response = await POST(
      new Request("http://localhost/api/projects/select", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ projectId: "beta" }),
      }) as any
    );
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(mockSetSelectedProjectId).toHaveBeenCalledWith("beta");
    expect(body.ok).toBe(true);
  });

  it("returns 404 for an unknown project id", async () => {
    mockResolveProjectWorkspace.mockReturnValue(null);

    const response = await POST(
      new Request("http://localhost/api/projects/select", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ projectId: "missing" }),
      }) as any
    );

    expect(response.status).toBe(404);
  });
});
