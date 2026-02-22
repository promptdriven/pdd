// example_usage.ts
// Demonstrates and verifies the GET and PUT endpoints of
// the script file API route at /api/project/script.
//
// This file imports the actual route handlers from
// app/api/project/script/route.ts and calls them directly,
// using process.chdir() to redirect file operations to an
// isolated temp directory.

import fs from "fs";
import os from "os";
import path from "path";

// ============================================================================
// Setup: isolated temp directory via process.chdir()
// ============================================================================

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pdd-script-example-"));
const originalCwd = process.cwd();

// Change to temp directory so route handlers use it as their base
process.chdir(tmpDir);

// Import the actual route handlers (they use process.cwd() internally)
import { GET, PUT, dynamic } from "../app/api/project/script/route";

// ============================================================================
// Helper: create a Request object
// ============================================================================

function makeGetRequest(): Request {
  return new Request("http://localhost/api/project/script", { method: "GET" });
}

function makePutRequest(body: unknown): Request {
  return new Request("http://localhost/api/project/script", {
    method: "PUT",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
}

/** Extracts JSON body and status from a Response. */
async function parseResponse(response: Response): Promise<{ status: number; body: any }> {
  const body = await response.json();
  return { status: response.status, body };
}

// ============================================================================
// Example 1: Verify dynamic export
// ============================================================================

function verifyDynamicExport(): void {
  console.log("=== Verify dynamic export ===");
  console.log(`dynamic = '${dynamic}'`);
  if (dynamic !== "force-dynamic") {
    throw new Error(`Expected dynamic to be 'force-dynamic', got '${dynamic}'`);
  }
  console.log("dynamic export is correct.\n");
}

// ============================================================================
// Example 2: Full round-trip — 404, create, read, update, read
// ============================================================================

/**
 * fetchScript()
 *
 * Calls the actual GET handler from route.ts.
 *
 * @returns The markdown content of narrative/main_script.md as a string,
 *          or null if the file does not yet exist (HTTP 404).
 *
 * Response shape on success (HTTP 200):
 *   { content: string }
 *
 * Response shape when file is missing (HTTP 404):
 *   { error: "Script file not found" }
 */
async function fetchScript(): Promise<string | null> {
  const response = await GET(makeGetRequest());
  const { status, body } = await parseResponse(response);

  if (status === 404) {
    console.log("Script file not found (narrative/main_script.md does not exist yet).");
    return null;
  }

  if (status !== 200) {
    throw new Error(`Unexpected status ${status}: ${JSON.stringify(body)}`);
  }

  return body.content;
}

/**
 * saveScript(content: string)
 *
 * Calls the actual PUT handler from route.ts with the given content.
 *
 * @param content - The full markdown string to write to narrative/main_script.md.
 *
 * Request body shape:
 *   { content: string }
 *
 * Response shape on success (HTTP 200):
 *   { ok: true }
 *
 * Response shape on validation error (HTTP 400):
 *   { error: "Missing required field: content must be a string." }
 */
async function saveScript(content: string): Promise<void> {
  const response = await PUT(makePutRequest({ content }));
  const { status, body } = await parseResponse(response);

  if (status !== 200) {
    throw new Error(`Failed to save script: ${status} — ${body.error}`);
  }

  console.log("Script saved successfully:", body.ok);
}

/**
 * Demonstrates a complete workflow using the real route handlers:
 *   1. Attempt to read the script (returns 404 if it doesn't exist).
 *   2. Write an initial script via PUT.
 *   3. Read it back via GET to confirm persistence.
 *   4. Update the script with additional content.
 *   5. Read the updated version.
 */
async function fullRoundTripExample(): Promise<void> {
  console.log("=== Step 1: Attempt to read script (may not exist yet) ===");
  const initial = await fetchScript();
  if (initial === null) {
    console.log("No script found — we will create one.\n");
  } else {
    console.log(`Existing script (${initial.length} chars):\n${initial.substring(0, 200)}...\n`);
  }

  console.log("=== Step 2: Write initial script via PUT ===");
  const initialScript = `# Product Launch Video — Master Script

## Section 1: Introduction
Welcome to the future of productivity. In this video, we'll walk you through
our latest product and show you how it can transform your workflow.

## Section 2: Features
- **Smart Automation**: Let AI handle the repetitive tasks.
- **Real-time Collaboration**: Work with your team seamlessly.
- **Analytics Dashboard**: Understand your data at a glance.

## Section 3: Outro
Thank you for watching. Visit our website to get started today.
`;
  await saveScript(initialScript);
  console.log();

  console.log("=== Step 3: Read script back via GET ===");
  const readBack = await fetchScript();
  if (readBack) {
    console.log(`Script content (${readBack.length} chars):`);
    console.log(readBack);
  }

  // Verify atomic write: the narrative/ directory and file should exist
  const narrativeDir = path.join(tmpDir, "narrative");
  const scriptFile = path.join(narrativeDir, "main_script.md");
  if (!fs.existsSync(scriptFile)) {
    throw new Error("Atomic write failed: main_script.md not found on disk");
  }
  // Verify no leftover .tmp file
  if (fs.existsSync(scriptFile + ".tmp")) {
    throw new Error("Atomic write failed: .tmp file still exists");
  }

  console.log("=== Step 4: Update script with additional section ===");
  const updatedScript =
    readBack +
    `\n## Section 4: Behind the Scenes\nHere's a look at how we built this product, the challenges we faced,\nand the team that made it all possible.\n`;
  await saveScript(updatedScript);
  console.log();

  console.log("=== Step 5: Read updated script ===");
  const final = await fetchScript();
  if (final) {
    console.log(`Updated script (${final.length} chars):`);
    console.log(final);
  }
}

// ============================================================================
// Example 3: Handling validation errors (PUT with invalid body)
// ============================================================================

/**
 * Demonstrates what happens when the PUT endpoint receives invalid data.
 * The server returns HTTP 400 with a descriptive error message.
 */
async function validationErrorExample(): Promise<void> {
  console.log("=== Validation Error Example ===");

  // Case 1: content is missing entirely
  const res1 = await PUT(makePutRequest({}));
  const { status: s1, body: b1 } = await parseResponse(res1);
  console.log(`Missing content — Status: ${s1}, Error: ${b1.error}`);
  if (s1 !== 400) throw new Error(`Expected 400, got ${s1}`);

  // Case 2: content is a number instead of a string
  const res2 = await PUT(makePutRequest({ content: 12345 }));
  const { status: s2, body: b2 } = await parseResponse(res2);
  console.log(`Non-string content — Status: ${s2}, Error: ${b2.error}`);
  if (s2 !== 400) throw new Error(`Expected 400, got ${s2}`);

  // Case 3: content is null
  const res3 = await PUT(makePutRequest({ content: null }));
  const { status: s3, body: b3 } = await parseResponse(res3);
  console.log(`Null content — Status: ${s3}, Error: ${b3.error}`);
  if (s3 !== 400) throw new Error(`Expected 400, got ${s3}`);
}

// ============================================================================
// Example 4: Debounced auto-save pattern (typical client-side usage)
// ============================================================================

/**
 * In a real editor UI, you would debounce calls to saveScript() so that
 * rapid keystrokes don't flood the server. The route is designed to be
 * called once per debounced write (e.g., 1 second after the user stops typing).
 *
 * @param delayMs - Debounce delay in milliseconds (default: 1000).
 * @returns A debounced save function.
 */
function createDebouncedSave(delayMs: number = 1000) {
  let timeoutId: ReturnType<typeof setTimeout> | null = null;

  return function debouncedSave(content: string): void {
    if (timeoutId) {
      clearTimeout(timeoutId);
    }

    timeoutId = setTimeout(async () => {
      try {
        await saveScript(content);
        console.log("Auto-saved script.");
      } catch (err) {
        console.error("Auto-save failed:", err);
      }
    }, delayMs);
  };
}

// ============================================================================
// Run all examples
// ============================================================================

async function main() {
  try {
    verifyDynamicExport();
    await fullRoundTripExample();
    await validationErrorExample();

    // Demonstrate the debounced save factory (just creation, not full run)
    const debouncedSave = createDebouncedSave(1000);
    console.log("\n=== Debounced save function created (1s delay) ===");
    console.log("In a UI, call debouncedSave(editorContent) on every keystroke.\n");

    console.log("✅ All examples completed successfully");
  } catch (err) {
    console.error("Example failed:", err);
    process.exit(1);
  } finally {
    // Restore original working directory
    process.chdir(originalCwd);
    // Clean up temp directory
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
}

main();
