/**
 * Tests for app/api/pipeline/specs/list/route.ts
 *
 * Verifies parent-child spec relationships are surfaced in the list API.
 * Container specs ([split:]) that reference child clipIds should cause
 * those children to be marked with a parentSpec field.
 */

import fs from "fs";
import os from "os";
import path from "path";

const mockLoadProject = jest.fn();

jest.mock("@/lib/project", () => ({
  loadProject: (...args: unknown[]) => mockLoadProject(...args),
}));

let projectDir: string;

jest.mock("@/lib/projects", () => ({
  getProjectDir: () => projectDir,
}));

import { GET } from "../app/api/pipeline/specs/list/route";

function mockProjectConfig(sections: Array<{ id: string; label: string; specDir: string }>) {
  return {
    name: "Test Project",
    sections: sections.map((s) => ({
      ...s,
      videoFile: `output/sections/${s.id}.mp4`,
      remotionDir: `remotion/${s.id}`,
      compositionId: `${s.id}Composition`,
      durationSeconds: 10,
      offsetSeconds: 0,
    })),
  };
}

beforeEach(() => {
  projectDir = fs.mkdtempSync(path.join(os.tmpdir(), "specs-list-"));
  mockLoadProject.mockReset();
});

afterEach(() => {
  fs.rmSync(projectDir, { recursive: true, force: true });
});

describe("GET /api/pipeline/specs/list — parent-child relationships", () => {
  it("marks veo children of a split spec with parentSpec field", async () => {
    mockLoadProject.mockReturnValue(
      mockProjectConfig([{ id: "cold_open", label: "Cold Open", specDir: "cold_open" }])
    );

    const specsDir = path.join(projectDir, "specs", "cold_open");
    fs.mkdirSync(specsDir, { recursive: true });

    fs.writeFileSync(
      path.join(specsDir, "01_split_screen_hook.md"),
      [
        "[split:]",
        "",
        "## Data Points JSON",
        "```json",
        "{",
        '  "type": "split_screen",',
        '  "leftClipId": "developer_ai_edit",',
        '  "rightClipId": "grandmother_darning"',
        "}",
        "```",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(specsDir, "02_developer_ai_edit.md"),
      "[veo:]\n\n# Developer AI Edit"
    );
    fs.writeFileSync(
      path.join(specsDir, "03_grandmother_darning.md"),
      "[veo:]\n\n# Grandmother Darning"
    );
    fs.writeFileSync(
      path.join(specsDir, "04_zoom_out.md"),
      "[Remotion]\n\n# Zoom Out"
    );

    const response = await GET();
    const data = await response.json();
    const files = data.sections[0].files;

    const split = files.find((f: any) => f.path.includes("01_split_screen_hook"));
    const dev = files.find((f: any) => f.path.includes("02_developer_ai_edit"));
    const grandma = files.find((f: any) => f.path.includes("03_grandmother_darning"));
    const zoom = files.find((f: any) => f.path.includes("04_zoom_out"));

    expect(split.parentSpec).toBeUndefined();
    expect(dev.parentSpec).toBe("01_split_screen_hook.md");
    expect(grandma.parentSpec).toBe("01_split_screen_hook.md");
    expect(zoom.parentSpec).toBeUndefined();
  });

  it("matches children by content field in panel objects", async () => {
    mockLoadProject.mockReturnValue(
      mockProjectConfig([{ id: "closing", label: "Closing", specDir: "closing" }])
    );

    const specsDir = path.join(projectDir, "specs", "closing");
    fs.mkdirSync(specsDir, { recursive: true });

    fs.writeFileSync(
      path.join(specsDir, "01_sock_callback_split.md"),
      [
        "[split:]",
        "",
        "## Data Points JSON",
        "```json",
        "{",
        '  "type": "split_screen",',
        '  "leftPanel": { "content": "sock_final_discard" },',
        '  "rightPanel": { "content": "code_regenerate_workflow" }',
        "}",
        "```",
      ].join("\n")
    );
    fs.writeFileSync(
      path.join(specsDir, "02_sock_final_discard.md"),
      "[veo:]\n\n# Sock Discard"
    );
    fs.writeFileSync(
      path.join(specsDir, "03_code_regenerate_workflow.md"),
      "[Remotion]\n\n# Code Regenerate"
    );

    const response = await GET();
    const data = await response.json();
    const files = data.sections[0].files;

    const sock = files.find((f: any) => f.path.includes("02_sock_final_discard"));
    const code = files.find((f: any) => f.path.includes("03_code_regenerate_workflow"));

    expect(sock.parentSpec).toBe("01_sock_callback_split.md");
    expect(code.parentSpec).toBe("01_sock_callback_split.md");
  });

  it("does not assign parentSpec when no split container exists", async () => {
    mockLoadProject.mockReturnValue(
      mockProjectConfig([{ id: "simple", label: "Simple", specDir: "simple" }])
    );

    const specsDir = path.join(projectDir, "specs", "simple");
    fs.mkdirSync(specsDir, { recursive: true });

    fs.writeFileSync(path.join(specsDir, "01_title.md"), "[title:]\n\n# Title");
    fs.writeFileSync(path.join(specsDir, "02_chart.md"), "[Remotion]\n\n# Chart");
    fs.writeFileSync(path.join(specsDir, "03_clip.md"), "[veo:]\n\n# Clip");

    const response = await GET();
    const data = await response.json();
    const files = data.sections[0].files;

    for (const file of files) {
      expect(file.parentSpec).toBeUndefined();
    }
  });

  it("does not assign parentSpec to the container itself", async () => {
    mockLoadProject.mockReturnValue(
      mockProjectConfig([{ id: "sect", label: "Section", specDir: "sect" }])
    );

    const specsDir = path.join(projectDir, "specs", "sect");
    fs.mkdirSync(specsDir, { recursive: true });

    fs.writeFileSync(
      path.join(specsDir, "01_split.md"),
      [
        "[split:]",
        "",
        "## Data Points JSON",
        '```json',
        '{ "leftClipId": "child_a", "rightClipId": "child_b" }',
        "```",
      ].join("\n")
    );
    fs.writeFileSync(path.join(specsDir, "02_child_a.md"), "[veo:]");
    fs.writeFileSync(path.join(specsDir, "03_child_b.md"), "[veo:]");

    const response = await GET();
    const data = await response.json();
    const files = data.sections[0].files;

    const container = files.find((f: any) => f.path.includes("01_split"));
    expect(container.parentSpec).toBeUndefined();
  });
});
