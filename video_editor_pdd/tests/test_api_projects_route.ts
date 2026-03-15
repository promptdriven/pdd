const mockListProjectWorkspaces = jest.fn();
const mockGetCurrentProjectWorkspace = jest.fn();
const mockResolveProjectWorkspace = jest.fn();
const mockSetSelectedProjectId = jest.fn();
const mockCreateProjectWorkspace = jest.fn();

jest.mock("@/lib/projects", () => ({
  listProjectWorkspaces: (...args: unknown[]) => mockListProjectWorkspaces(...args),
  getCurrentProjectWorkspace: (...args: unknown[]) => mockGetCurrentProjectWorkspace(...args),
  resolveProjectWorkspace: (...args: unknown[]) => mockResolveProjectWorkspace(...args),
  setSelectedProjectId: (...args: unknown[]) => mockSetSelectedProjectId(...args),
  createProjectWorkspace: (...args: unknown[]) => mockCreateProjectWorkspace(...args),
}));

import { GET } from "../app/api/projects/route";
import { POST } from "../app/api/projects/select/route";
import { POST as CREATE } from "../app/api/projects/create/route";

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

describe("POST /api/projects/create", () => {
  beforeEach(() => {
    jest.resetAllMocks();
  });

  it("creates and selects a new project workspace", async () => {
    mockCreateProjectWorkspace.mockReturnValue({
      id: "my-new-video",
      name: "my-new-video",
      dir: "/tmp/projects/my-new-video",
      dbPath: "/tmp/projects/my-new-video/pipeline.db",
    });

    const response = await CREATE(
      new Request("http://localhost/api/projects/create", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "My New Video" }),
      }) as any
    );
    const body = await response.json();

    expect(response.status).toBe(200);
    expect(mockCreateProjectWorkspace).toHaveBeenCalledWith(
      expect.objectContaining({
        projectId: "my-new-video",
        config: expect.objectContaining({ name: "My New Video" }),
      })
    );
    expect(mockSetSelectedProjectId).toHaveBeenCalledWith("my-new-video");
    expect(body).toEqual({
      ok: true,
      project: { id: "my-new-video", name: "My New Video" },
    });
  });

  it("returns 400 when the project name is missing", async () => {
    const response = await CREATE(
      new Request("http://localhost/api/projects/create", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "   " }),
      }) as any
    );

    expect(response.status).toBe(400);
    expect(mockCreateProjectWorkspace).not.toHaveBeenCalled();
  });

  it("returns 409 when the project directory already exists", async () => {
    mockCreateProjectWorkspace.mockImplementation(() => {
      throw new Error("Project already exists: my-new-video");
    });

    const response = await CREATE(
      new Request("http://localhost/api/projects/create", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ name: "My New Video" }),
      }) as any
    );

    expect(response.status).toBe(409);
  });
});
