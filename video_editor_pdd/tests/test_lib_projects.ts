import fs from "fs";
import os from "os";
import path from "path";

describe("lib/projects", () => {
  const originalCwd = process.cwd();
  const originalEnv = process.env.VIDEO_EDITOR_PROJECT_DIRS;

  beforeEach(() => {
    jest.resetModules();
    delete process.env.VIDEO_EDITOR_PROJECT_DIRS;
    delete process.env.VIDEO_EDITOR_PROJECT_ID;
  });

  afterEach(() => {
    process.chdir(originalCwd);
    if (originalEnv === undefined) {
      delete process.env.VIDEO_EDITOR_PROJECT_DIRS;
    } else {
      process.env.VIDEO_EDITOR_PROJECT_DIRS = originalEnv;
    }
  });

  it("discovers the current project and sibling project directories", async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "video-editor-projects-"));
    const current = path.join(root, "current_project");
    const sibling = path.join(root, "other_project");
    fs.mkdirSync(current, { recursive: true });
    fs.mkdirSync(sibling, { recursive: true });
    fs.writeFileSync(path.join(current, "project.json"), "{}");
    fs.writeFileSync(path.join(sibling, "project.json"), "{}");

    process.chdir(current);

    const { listProjectWorkspaces } = await import("../lib/projects");
    const workspaces = listProjectWorkspaces();

    expect(workspaces.map((workspace) => workspace.name)).toEqual(
      expect.arrayContaining(["current_project", "other_project"])
    );
  });

  it("persists the selected project id in the active-project selector file", async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "video-editor-project-select-"));
    const current = path.join(root, "current_project");
    const target = path.join(root, "demo-project");
    fs.mkdirSync(current, { recursive: true });
    fs.mkdirSync(target, { recursive: true });
    fs.writeFileSync(path.join(current, "project.json"), "{}");
    fs.writeFileSync(path.join(target, "project.json"), "{}");
    process.chdir(current);

    const {
      setSelectedProjectId,
      getCurrentProjectWorkspace,
    } = await import("../lib/projects");

    setSelectedProjectId("demo-project");

    expect(fs.readFileSync(path.join(current, ".active-project"), "utf-8")).toBe("demo-project");
    expect(getCurrentProjectWorkspace().name).toBe("demo-project");
  });

  it("defaults to the current working project when sibling projects are also discoverable", async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "video-editor-current-project-"));
    const current = path.join(root, "z_current_project");
    const sibling = path.join(root, "a_other_project");
    fs.mkdirSync(current, { recursive: true });
    fs.mkdirSync(sibling, { recursive: true });
    fs.writeFileSync(path.join(current, "project.json"), "{}");
    fs.writeFileSync(path.join(sibling, "project.json"), "{}");

    process.chdir(current);

    const { getCurrentProjectWorkspace } = await import("../lib/projects");

    expect(fs.realpathSync(getCurrentProjectWorkspace().dir)).toBe(
      fs.realpathSync(path.resolve(current))
    );
    expect(getCurrentProjectWorkspace().name).toBe("z_current_project");
  });

  it("discovers nested project workspaces under parent directories", async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "video-editor-nested-projects-"));
    const current = path.join(root, "video_editor_pdd");
    const demoProject = path.join(root, "demos", "video_editor");
    const nestedPipelineProject = path.join(demoProject, "pipeline");

    fs.mkdirSync(current, { recursive: true });
    fs.mkdirSync(demoProject, { recursive: true });
    fs.mkdirSync(nestedPipelineProject, { recursive: true });

    fs.writeFileSync(path.join(current, "project.json"), "{}");
    fs.writeFileSync(path.join(demoProject, "project.json"), "{}");
    fs.writeFileSync(path.join(nestedPipelineProject, "project.json"), "{}");

    process.chdir(current);

    const { listProjectWorkspaces } = await import("../lib/projects");
    const workspaces = listProjectWorkspaces();

    expect(workspaces.map((workspace) => workspace.name)).toEqual(
      expect.arrayContaining(["video_editor_pdd", "video_editor", "pipeline"])
    );
  });

  it("falls back to the current temp workspace when not running from the app root", async () => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "video-editor-fallback-workspace-"));
    const scratch = path.join(root, "scratch_workspace");
    const sibling = path.join(root, "other_project");

    fs.mkdirSync(scratch, { recursive: true });
    fs.mkdirSync(sibling, { recursive: true });
    fs.writeFileSync(path.join(sibling, "project.json"), "{}");

    process.chdir(scratch);

    const { getCurrentProjectWorkspace } = await import("../lib/projects");

    expect(fs.realpathSync(getCurrentProjectWorkspace().dir)).toBe(
      fs.realpathSync(path.resolve(scratch))
    );
    expect(getCurrentProjectWorkspace().name).toBe("scratch_workspace");
  });
});
