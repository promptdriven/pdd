// example_usage.ts
// Comprehensive usage example for app/api/project/route.ts
//
// This file demonstrates how to interact with the /api/project API route
// from both client-side code and test scripts. The route provides two
// endpoints for managing the project.json configuration file:
//
//   GET  /api/project  — Returns the full ProjectConfig as JSON
//   PUT  /api/project  — Accepts Partial<ProjectConfig>, merges with
//                         existing config, validates, saves, and returns
//                         the updated ProjectConfig
//
// All other HTTP methods (POST, PATCH, DELETE, OPTIONS, HEAD) return
// 405 Method Not Allowed with a JSON error payload.
//
// NOTE: This route is a Next.js App Router Route Handler. It is not
// imported directly — it is consumed via HTTP requests to /api/project.
// The examples below show how to call it using fetch().
//
// For standalone execution (outside a running Next.js server), a mock
// fetch is provided that simulates the route handler logic using the
// same loadProject/saveProject functions the real route uses.

import fs from "fs";
import os from "os";
import path from "path";
import { z } from "zod";

import {
  loadProject,
  saveProject,
  validateProjectConfig,
} from "../lib/project";

import type { ProjectConfig, Section } from "../lib/types";

// ============================================================================
// Mock fetch — simulates the Next.js route handler for standalone execution
// ============================================================================

// Create a temp directory with a copy of project.json for isolated testing
const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pdd-api-example-"));
const sourceProjectJson = path.join(__dirname, "..", "project.json");
fs.copyFileSync(sourceProjectJson, path.join(tmpDir, "project.json"));

/**
 * Mock fetch that simulates GET/PUT /api/project route handlers.
 * Uses the same loadProject/saveProject/validateProjectConfig functions
 * as the real route.ts, operating on an isolated temp directory.
 */
const originalFetch = globalThis.fetch;
globalThis.fetch = async (
  input: RequestInfo | URL,
  init?: RequestInit
): Promise<Response> => {
  const url =
    typeof input === "string"
      ? input
      : input instanceof URL
        ? input.href
        : input.url;

  // Only intercept /api/project requests
  if (!url.includes("/api/project")) {
    return originalFetch(input, init);
  }

  const method = (init?.method || "GET").toUpperCase();

  // Unsupported methods return 405
  if (!["GET", "PUT"].includes(method)) {
    return new Response(
      JSON.stringify({ error: "Method not allowed" }),
      { status: 405, headers: { "Content-Type": "application/json" } }
    );
  }

  // GET handler
  if (method === "GET") {
    try {
      const config = loadProject(tmpDir);
      return new Response(JSON.stringify(config), {
        status: 200,
        headers: { "Content-Type": "application/json" },
      });
    } catch (err) {
      if (err instanceof z.ZodError) {
        return new Response(
          JSON.stringify({ error: "Validation failed", issues: err.issues }),
          { status: 400, headers: { "Content-Type": "application/json" } }
        );
      }
      return new Response(
        JSON.stringify({ error: "Internal Server Error" }),
        { status: 500, headers: { "Content-Type": "application/json" } }
      );
    }
  }

  // PUT handler
  if (method === "PUT") {
    let body: Partial<ProjectConfig>;
    try {
      body = JSON.parse(init?.body as string);
    } catch {
      return new Response(
        JSON.stringify({ error: "Invalid JSON" }),
        { status: 400, headers: { "Content-Type": "application/json" } }
      );
    }

    try {
      const existing = loadProject(tmpDir);
      const merged = { ...existing, ...body };
      const validated = validateProjectConfig(merged);
      saveProject(validated, tmpDir);
      return new Response(JSON.stringify(validated), {
        status: 200,
        headers: { "Content-Type": "application/json" },
      });
    } catch (err) {
      if (err instanceof z.ZodError) {
        return new Response(
          JSON.stringify({ error: "Validation failed", issues: err.issues }),
          { status: 400, headers: { "Content-Type": "application/json" } }
        );
      }
      return new Response(
        JSON.stringify({ error: "Internal Server Error" }),
        { status: 500, headers: { "Content-Type": "application/json" } }
      );
    }
  }

  return originalFetch(input, init);
};

// ============================================================================
// Example 1: GET /api/project — Load the current project configuration
// ============================================================================

/**
 * Fetches the full ProjectConfig from the server.
 *
 * @returns Promise<ProjectConfig> — The complete project configuration object
 *          containing name, outputResolution, tts, sections, audioSync, veo,
 *          and render fields.
 *
 * @throws Error if the server returns a non-200 status:
 *   - 400: project.json exists but fails Zod schema validation
 *          Response body: { error: "Validation failed", issues: ZodIssue[] }
 *   - 500: Filesystem error (e.g., project.json missing or unreadable)
 *          Response body: { error: "Internal Server Error" }
 *
 * Response shape on success (200):
 * {
 *   name: string,
 *   outputResolution: "1920x1080" | "1280x720",
 *   tts: { voice: string, rate: number, model: string },
 *   sections: Section[],
 *   audioSync: { sectionGroups: Record<string, string[]> },
 *   veo: { model: string, aspectRatio: string, referenceImages: Record<string, string> },
 *   render: { maxParallelRenders: number, outputDir: string, fps: number, width: number, height: number }
 * }
 */
async function getProjectConfig(): Promise<ProjectConfig> {
  const response = await fetch("/api/project", {
    method: "GET",
    headers: {
      Accept: "application/json",
    },
  });

  if (!response.ok) {
    const errorBody = await response.json();

    if (response.status === 400 && errorBody.issues) {
      // Zod validation failed — project.json is malformed
      console.error("Validation issues:", errorBody.issues);
      throw new Error(
        `Project config validation failed: ${errorBody.issues.length} issue(s)`
      );
    }

    throw new Error(errorBody.error || `HTTP ${response.status}`);
  }

  const config: ProjectConfig = await response.json();
  return config;
}

// Usage:
async function exampleGetProject() {
  try {
    const config = await getProjectConfig();
    console.log(`Project: "${config.name}"`);
    console.log(`Resolution: ${config.outputResolution}`);
    console.log(`Sections: ${config.sections.length}`);
    console.log(`TTS voice: ${config.tts.voice}`);
    console.log(`Veo model: ${config.veo.model}`);
    console.log(`Render FPS: ${config.render.fps}`);

    // Iterate sections
    for (const section of config.sections) {
      console.log(
        `  [${section.id}] "${section.label}" — ${section.durationSeconds}s @ offset ${section.offsetSeconds}s`
      );
    }
  } catch (err) {
    console.error("Failed to load project:", err);
  }
}

// ============================================================================
// Example 2: PUT /api/project — Update project name only (partial update)
// ============================================================================

/**
 * Updates the project configuration by sending a partial config object.
 * The server merges the partial update with the existing config on disk,
 * validates the merged result against the full ProjectConfig Zod schema,
 * saves it atomically, and returns the complete updated config.
 *
 * @param updates - A Partial<ProjectConfig> containing only the fields to change.
 *                  Any field not included will retain its current value from disk.
 *                  NOTE: For nested objects (tts, veo, render, audioSync), the
 *                  merge is shallow — if you provide `tts`, it replaces the
 *                  entire tts object, not individual fields within it.
 *
 * @returns Promise<ProjectConfig> — The full, validated, updated config.
 *
 * @throws Error if the server returns a non-200 status:
 *   - 400 (Invalid JSON): Request body is not valid JSON
 *          Response body: { error: "Invalid JSON" }
 *   - 400 (Validation failed): Merged config fails Zod validation
 *          Response body: { error: "Validation failed", issues: ZodIssue[] }
 *   - 500: Filesystem error during load or save
 *          Response body: { error: "Internal Server Error" }
 *
 * Request body shape: Partial<ProjectConfig> (any subset of fields)
 * Response body shape on success (200): Full ProjectConfig
 */
async function updateProjectConfig(
  updates: Partial<ProjectConfig>
): Promise<ProjectConfig> {
  const response = await fetch("/api/project", {
    method: "PUT",
    headers: {
      "Content-Type": "application/json",
      Accept: "application/json",
    },
    body: JSON.stringify(updates),
  });

  if (!response.ok) {
    const errorBody = await response.json();

    if (response.status === 400 && errorBody.issues) {
      // Zod validation failed after merge
      console.error("Validation issues after merge:", errorBody.issues);
      // Each issue has: { code, message, path, expected, received }
      for (const issue of errorBody.issues) {
        console.error(`  - ${issue.path.join(".")}: ${issue.message}`);
      }
      throw new Error("Validation failed");
    }

    if (response.status === 400 && errorBody.error === "Invalid JSON") {
      throw new Error("Request body was not valid JSON");
    }

    throw new Error(errorBody.error || `HTTP ${response.status}`);
  }

  const updatedConfig: ProjectConfig = await response.json();
  return updatedConfig;
}

// Usage — rename the project:
async function exampleRenameProject() {
  try {
    const updated = await updateProjectConfig({
      name: "My Renamed Video Project",
    });
    console.log(`Project renamed to: "${updated.name}"`);
    // All other fields (sections, tts, veo, etc.) remain unchanged
  } catch (err) {
    console.error("Failed to rename project:", err);
  }
}

// ============================================================================
// Example 3: PUT /api/project — Update TTS configuration
// ============================================================================

/**
 * Demonstrates updating a nested config object. Because the merge is shallow
 * (spread operator), you must provide the complete nested object, not just
 * the fields you want to change within it.
 */
async function exampleUpdateTtsConfig() {
  // IMPORTANT: Shallow merge means you must include ALL tts fields,
  // not just the one you want to change. Otherwise the missing fields
  // will be undefined and fail Zod validation.
  const updated = await updateProjectConfig({
    tts: {
      voice: "en-US-Neural2-D", // changed
      rate: 1.1, // changed
      model: "google-tts-v2", // must include even if unchanged
    },
  });

  console.log(`TTS voice updated to: ${updated.tts.voice}`);
  console.log(`TTS rate updated to: ${updated.tts.rate}`);
}

// ============================================================================
// Example 4: PUT /api/project — Replace the sections array
// ============================================================================

/**
 * Demonstrates replacing the entire sections array. Useful after reordering
 * sections or recalculating offsets.
 *
 * Each Section object requires:
 *   id              — unique string identifier
 *   label           — human-readable display name
 *   videoFile       — relative path to the rendered MP4
 *   specDir         — directory containing spec files
 *   remotionDir     — directory containing Remotion composition source
 *   compositionId   — Remotion composition ID
 *   durationSeconds — duration in seconds (defaults to 0 if omitted)
 *   offsetSeconds   — cumulative offset from video start (defaults to 0)
 */
async function exampleUpdateSections() {
  const newSections: Section[] = [
    {
      id: "intro",
      label: "Introduction",
      videoFile: "output/sections/intro.mp4",
      specDir: "specs/intro",
      remotionDir: "remotion/intro",
      compositionId: "IntroComposition",
      durationSeconds: 15.0, // extended from 12.5
      offsetSeconds: 0,
    },
    {
      id: "demo",
      label: "Product Demo", // new section replacing 'main'
      videoFile: "output/sections/demo.mp4",
      specDir: "specs/demo",
      remotionDir: "remotion/demo",
      compositionId: "DemoComposition",
      durationSeconds: 60.0,
      offsetSeconds: 15.0,
    },
    {
      id: "outro",
      label: "Outro",
      videoFile: "output/sections/outro.mp4",
      specDir: "specs/outro",
      remotionDir: "remotion/outro",
      compositionId: "OutroComposition",
      durationSeconds: 8.0,
      offsetSeconds: 75.0,
    },
  ];

  const updated = await updateProjectConfig({ sections: newSections });
  console.log(`Sections updated. Count: ${updated.sections.length}`);
  for (const s of updated.sections) {
    console.log(`  ${s.id}: ${s.durationSeconds}s @ ${s.offsetSeconds}s`);
  }
}

// ============================================================================
// Example 5: PUT /api/project — Update multiple top-level fields at once
// ============================================================================

async function exampleBulkUpdate() {
  const updated = await updateProjectConfig({
    name: "Final Cut - Product Launch",
    outputResolution: "1280x720", // downscale for draft
    render: {
      maxParallelRenders: 2,
      outputDir: "output/draft",
      fps: 24,
      width: 1280,
      height: 720,
    },
  });

  console.log(`Updated project: "${updated.name}"`);
  console.log(`Resolution: ${updated.outputResolution}`);
  console.log(`Render: ${updated.render.width}x${updated.render.height} @ ${updated.render.fps}fps`);
}

// ============================================================================
// Example 6: Handling 405 Method Not Allowed
// ============================================================================

/**
 * The route explicitly returns 405 for POST, PATCH, DELETE, OPTIONS, and HEAD.
 * Response body: { error: "Method not allowed" }
 */
async function exampleUnsupportedMethod() {
  const response = await fetch("/api/project", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ name: "test" }),
  });

  console.log(`POST status: ${response.status}`); // 405
  const body = await response.json();
  console.log(`Error: ${body.error}`); // "Method not allowed"

  // Same for DELETE
  const delResponse = await fetch("/api/project", { method: "DELETE" });
  console.log(`DELETE status: ${delResponse.status}`); // 405
}

// ============================================================================
// Example 7: Handling validation errors gracefully in the UI
// ============================================================================

/**
 * Demonstrates how a React component or client utility might handle
 * validation errors returned by the PUT endpoint.
 *
 * The 400 response for validation failures has this shape:
 * {
 *   error: "Validation failed",
 *   issues: [
 *     {
 *       code: "invalid_type",
 *       expected: "string",
 *       received: "number",
 *       path: ["name"],
 *       message: "Expected string, received number"
 *     },
 *     ...
 *   ]
 * }
 */
interface ZodIssue {
  code: string;
  message: string;
  path: (string | number)[];
  expected?: string;
  received?: string;
}

async function exampleHandleValidationErrors() {
  const response = await fetch("/api/project", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({
      outputResolution: "4K", // invalid — must be '1920x1080' or '1280x720'
    }),
  });

  if (response.status === 400) {
    const errorBody = await response.json();

    if (errorBody.issues) {
      const issues: ZodIssue[] = errorBody.issues;

      // Build a field-level error map for form display
      const fieldErrors: Record<string, string> = {};
      for (const issue of issues) {
        const fieldPath = issue.path.join(".");
        fieldErrors[fieldPath] = issue.message;
      }

      console.log("Field errors:", fieldErrors);
      // e.g., { "outputResolution": "Invalid enum value. Expected '1920x1080' | '1280x720', received '4K'" }
    }
  }
}

// ============================================================================
// Example 8: React hook pattern for project config (client component)
// ============================================================================

/**
 * Example of a custom React hook that wraps the /api/project endpoints.
 * This pattern is commonly used in Next.js client components.
 *
 * Note: This is illustrative — in a real app you'd use SWR, React Query,
 * or similar for caching and revalidation.
 */
function useProjectConfigExample() {
  // In a real React component:
  //
  // const [config, setConfig] = useState<ProjectConfig | null>(null);
  // const [loading, setLoading] = useState(true);
  // const [error, setError] = useState<string | null>(null);
  //
  // useEffect(() => {
  //   fetch("/api/project")
  //     .then((res) => {
  //       if (!res.ok) throw new Error(`HTTP ${res.status}`);
  //       return res.json();
  //     })
  //     .then((data: ProjectConfig) => {
  //       setConfig(data);
  //       setLoading(false);
  //     })
  //     .catch((err) => {
  //       setError(err.message);
  //       setLoading(false);
  //     });
  // }, []);
  //
  // const updateConfig = async (updates: Partial<ProjectConfig>) => {
  //   const res = await fetch("/api/project", {
  //     method: "PUT",
  //     headers: { "Content-Type": "application/json" },
  //     body: JSON.stringify(updates),
  //   });
  //   if (!res.ok) {
  //     const body = await res.json();
  //     throw new Error(body.error || `HTTP ${res.status}`);
  //   }
  //   const updated: ProjectConfig = await res.json();
  //   setConfig(updated);
  //   return updated;
  // };
  //
  // return { config, loading, error, updateConfig };

  console.log("See inline comments for React hook implementation pattern");
}

// ============================================================================
// Example 9: Using fetch with absolute URL (for server-side or test scripts)
// ============================================================================

/**
 * When calling from server-side code or test scripts, you need the full URL.
 * The base URL depends on your deployment environment.
 */
async function exampleWithAbsoluteUrl() {
  const BASE_URL = process.env.NEXT_PUBLIC_BASE_URL || "http://localhost:3000";

  // GET
  const getRes = await fetch(`${BASE_URL}/api/project`);
  const config: ProjectConfig = await getRes.json();
  console.log(`Loaded "${config.name}" from ${BASE_URL}`);

  // PUT
  const putRes = await fetch(`${BASE_URL}/api/project`, {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ name: "Updated via absolute URL" }),
  });
  const updated: ProjectConfig = await putRes.json();
  console.log(`Updated to "${updated.name}"`);
}

// ============================================================================
// Run all examples (in a real app these would be triggered by UI interactions)
// ============================================================================

async function main() {
  console.log("=== Project API Route Usage Examples ===\n");

  console.log("--- Example 1: GET project config ---");
  await exampleGetProject();

  console.log("\n--- Example 2: Rename project ---");
  await exampleRenameProject();

  console.log("\n--- Example 3: Update TTS config ---");
  await exampleUpdateTtsConfig();

  console.log("\n--- Example 4: Update sections ---");
  await exampleUpdateSections();

  console.log("\n--- Example 5: Bulk update ---");
  await exampleBulkUpdate();

  console.log("\n--- Example 6: Unsupported methods ---");
  await exampleUnsupportedMethod();

  console.log("\n--- Example 7: Validation error handling ---");
  await exampleHandleValidationErrors();

  console.log("\n--- Example 8: React hook pattern ---");
  useProjectConfigExample();

  console.log("\n--- Example 9: Absolute URL usage ---");
  await exampleWithAbsoluteUrl();

  // Clean up temp directory
  fs.rmSync(tmpDir, { recursive: true, force: true });

  // Restore original fetch
  globalThis.fetch = originalFetch;

  console.log("\n✅ All examples completed");
}

if (require.main === module) {
  main().catch(console.error);
}
