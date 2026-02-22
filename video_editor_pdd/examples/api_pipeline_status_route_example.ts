/**
 * Example: Consuming the GET /api/pipeline/status endpoint
 *
 * This file demonstrates how a client (e.g., a React sidebar component)
 * polls the pipeline status API route to retrieve the current state of
 * all 10 pipeline stages. It also shows the expected response shape and
 * how to work with the returned data.
 *
 * The API route is located at app/api/pipeline/status/route.ts and is
 * a Next.js Route Handler that:
 *   - Queries the `pipeline_status` SQLite table via getDb()
 *   - Returns a map of all 10 stages with their current status
 *   - Fills in "not_started" defaults for stages with no DB row
 *   - Responds with HTTP 500 + { error: string } on DB failures
 *   - Is marked `force-dynamic` so Next.js never caches the response
 *
 * For standalone execution (outside a running Next.js server), a mock
 * fetch is provided that simulates the route handler logic using the
 * same getDb() function the real route uses.
 */

// Use an in-memory database for this example so each run starts fresh
process.env.DB_PATH = ":memory:";

import { getDb } from "../lib/db";
import type { PipelineStage, StageStatus } from "../lib/types";

// ---------------------------------------------------------------------------
// 1. Type definitions matching the API response shape
// ---------------------------------------------------------------------------

/**
 * StageStatusEntry represents the status of a single pipeline stage.
 *
 * @property status    - Current lifecycle state of the stage:
 *                       "not_started" | "running" | "done" | "error"
 * @property lastJobId - UUID of the most recent job associated with this
 *                       stage, or null if no job has been created yet.
 * @property error     - Human-readable error message if status is "error",
 *                       otherwise null.
 */
type StageStatusEntry = {
  status: StageStatus;
  lastJobId: string | null;
  error: string | null;
};

/**
 * PipelineStatusResponse is the JSON body returned by
 * GET /api/pipeline/status on a successful (200) response.
 *
 * @property stages - A record keyed by PipelineStage name, where every
 *                    one of the 10 canonical stages is guaranteed to be
 *                    present. Stages without a database row default to
 *                    { status: "not_started", lastJobId: null, error: null }.
 */
type PipelineStatusResponse = {
  stages: Record<PipelineStage, StageStatusEntry>;
};

/**
 * PipelineErrorResponse is the JSON body returned on a 500 error.
 *
 * @property error - Description of what went wrong (e.g., "Internal Server Error").
 */
type PipelineErrorResponse = {
  error: string;
};

// ---------------------------------------------------------------------------
// 2. Canonical stage ordering (mirrors the server-side constant)
// ---------------------------------------------------------------------------

const PIPELINE_STAGES: PipelineStage[] = [
  "setup",
  "script",
  "tts-script",
  "tts-render",
  "audio-sync",
  "specs",
  "veo",
  "compositions",
  "render",
  "audit",
];

// ---------------------------------------------------------------------------
// 3. Mock fetch — simulates the Next.js route handler for standalone execution
// ---------------------------------------------------------------------------

/**
 * Mock fetch that simulates GET /api/pipeline/status route handler.
 * Uses the same getDb() + pipeline_status query as the real route.ts,
 * operating on an in-memory SQLite database.
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

  // Only intercept /api/pipeline/status requests
  if (!url.includes("/api/pipeline/status")) {
    return originalFetch(input, init);
  }

  try {
    const db = getDb();
    const rows = db.prepare("SELECT * FROM pipeline_status").all() as Array<{
      stage: PipelineStage;
      status: StageStatus;
      lastJobId: string | null;
      error: string | null;
    }>;

    const stagesMap = {} as Record<PipelineStage, StageStatusEntry>;

    // Build map from existing rows
    for (const row of rows) {
      stagesMap[row.stage] = {
        status: row.status,
        lastJobId: row.lastJobId ?? null,
        error: row.error ?? null,
      };
    }

    // Fill missing stages with defaults
    for (const stage of PIPELINE_STAGES) {
      if (!stagesMap[stage]) {
        stagesMap[stage] = {
          status: "not_started",
          lastJobId: null,
          error: null,
        };
      }
    }

    return new Response(JSON.stringify({ stages: stagesMap }), {
      status: 200,
      headers: { "Content-Type": "application/json" },
    });
  } catch (err) {
    return new Response(
      JSON.stringify({ error: "Internal Server Error" }),
      { status: 500, headers: { "Content-Type": "application/json" } }
    );
  }
};

// ---------------------------------------------------------------------------
// 4. Seed test data into the in-memory database
// ---------------------------------------------------------------------------

/**
 * Insert some pipeline_status rows so the example has interesting data.
 */
function seedTestData(): void {
  const db = getDb();
  const now = new Date().toISOString();

  const insert = db.prepare(
    `INSERT INTO pipeline_status (stage, status, lastJobId, error, updatedAt)
     VALUES (?, ?, ?, ?, ?)
     ON CONFLICT(stage) DO UPDATE SET
       status = excluded.status,
       lastJobId = excluded.lastJobId,
       error = excluded.error,
       updatedAt = excluded.updatedAt`
  );

  insert.run("setup", "done", "job-001", null, now);
  insert.run("script", "done", "job-002", null, now);
  insert.run("tts-script", "done", "job-003", null, now);
  insert.run("tts-render", "running", "job-004", null, now);
  insert.run("veo", "error", "job-007", "Veo API rate limit exceeded", now);
}

seedTestData();

// ---------------------------------------------------------------------------
// 5. Fetching pipeline status from the API
// ---------------------------------------------------------------------------

/**
 * Fetches the current status of all pipeline stages from the server.
 *
 * @param baseUrl - The base URL of the Next.js app (e.g., "http://localhost:3000").
 *                  Defaults to an empty string for same-origin browser requests.
 *
 * @returns A PipelineStatusResponse containing a `stages` map with all 10
 *          pipeline stages and their current status.
 *
 * @throws Error if the HTTP response is not OK (status >= 400).
 *
 * @example
 * ```ts
 * const data = await fetchPipelineStatus("http://localhost:3000");
 * console.log(data.stages.setup.status); // "done" | "running" | "not_started" | "error"
 * ```
 */
async function fetchPipelineStatus(
  baseUrl: string = ""
): Promise<PipelineStatusResponse> {
  const response = await fetch(`${baseUrl}/api/pipeline/status`, {
    method: "GET",
    headers: { Accept: "application/json" },
    // Disable Next.js fetch cache to always get fresh data
    cache: "no-store",
  });

  if (!response.ok) {
    const errorBody: PipelineErrorResponse = await response.json();
    throw new Error(
      `Pipeline status request failed (${response.status}): ${errorBody.error}`
    );
  }

  return response.json();
}

// ---------------------------------------------------------------------------
// 6. Polling loop (used by the sidebar to refresh every 5 seconds)
// ---------------------------------------------------------------------------

/**
 * Starts a polling loop that fetches pipeline status at a fixed interval.
 *
 * @param onUpdate  - Callback invoked with the latest stage map on each
 *                    successful poll. Receives Record<PipelineStage, StageStatusEntry>.
 * @param onError   - Callback invoked when a poll fails. Receives the Error object.
 * @param intervalMs - Polling interval in milliseconds. Defaults to 5000 (5s).
 * @param baseUrl   - Base URL of the API server.
 *
 * @returns A cleanup function that stops the polling interval when called.
 *          Typically called in a React useEffect cleanup or on component unmount.
 *
 * @example
 * ```tsx
 * // Inside a React component
 * useEffect(() => {
 *   const stop = startPolling(
 *     (stages) => setStages(stages),
 *     (err) => console.error("Poll failed:", err),
 *     5000
 *   );
 *   return stop; // cleanup on unmount
 * }, []);
 * ```
 */
function startPolling(
  onUpdate: (stages: Record<PipelineStage, StageStatusEntry>) => void,
  onError: (error: Error) => void,
  intervalMs: number = 5000,
  baseUrl: string = ""
): () => void {
  let active = true;

  const poll = async () => {
    if (!active) return;
    try {
      const data = await fetchPipelineStatus(baseUrl);
      if (active) onUpdate(data.stages);
    } catch (err) {
      if (active) onError(err instanceof Error ? err : new Error(String(err)));
    }
  };

  // Fire immediately, then repeat on interval
  poll();
  const handle = setInterval(poll, intervalMs);

  return () => {
    active = false;
    clearInterval(handle);
  };
}

// ---------------------------------------------------------------------------
// 7. Utility: Derive UI state from the stages map
// ---------------------------------------------------------------------------

/**
 * Determines the "active" (currently running or next-to-run) stage index.
 *
 * @param stages - The stages map from the API response.
 * @returns The 0-based index into PIPELINE_STAGES of the first non-"done"
 *          stage, or -1 if all stages are complete.
 */
function getActiveStageIndex(
  stages: Record<PipelineStage, StageStatusEntry>
): number {
  for (let i = 0; i < PIPELINE_STAGES.length; i++) {
    const entry = stages[PIPELINE_STAGES[i]];
    if (entry.status !== "done") return i;
  }
  return -1; // all stages complete
}

/**
 * Checks whether the entire pipeline has completed successfully.
 *
 * @param stages - The stages map from the API response.
 * @returns true if every stage has status "done".
 */
function isPipelineComplete(
  stages: Record<PipelineStage, StageStatusEntry>
): boolean {
  return PIPELINE_STAGES.every((s) => stages[s].status === "done");
}

/**
 * Returns all stages that are currently in an error state.
 *
 * @param stages - The stages map from the API response.
 * @returns Array of objects with the stage name and its error message.
 */
function getErrorStages(
  stages: Record<PipelineStage, StageStatusEntry>
): Array<{ stage: PipelineStage; error: string }> {
  return PIPELINE_STAGES.filter((s) => stages[s].status === "error").map(
    (s) => ({
      stage: s,
      error: stages[s].error ?? "Unknown error",
    })
  );
}

// ---------------------------------------------------------------------------
// 8. End-to-end usage demonstration
// ---------------------------------------------------------------------------

async function main() {
  console.log("=== Single fetch ===");
  try {
    const data = await fetchPipelineStatus();

    // Iterate stages in canonical order
    for (const stage of PIPELINE_STAGES) {
      const entry = data.stages[stage];
      const badge =
        entry.status === "done"
          ? "DONE"
          : entry.status === "running"
            ? "RUNNING"
            : entry.status === "error"
              ? "ERROR"
              : "NOT_STARTED";
      console.log(
        `  [${badge}] ${stage.padEnd(14)} status=${entry.status}` +
          (entry.lastJobId ? ` job=${entry.lastJobId}` : "") +
          (entry.error ? ` error="${entry.error}"` : "")
      );
    }

    // Derived state
    const activeIdx = getActiveStageIndex(data.stages);
    console.log(
      `\n  Active stage: ${activeIdx >= 0 ? PIPELINE_STAGES[activeIdx] : "all complete"}`
    );
    console.log(`  Pipeline complete: ${isPipelineComplete(data.stages)}`);

    const errors = getErrorStages(data.stages);
    if (errors.length > 0) {
      console.log(`  Errors in: ${errors.map((e) => e.stage).join(", ")}`);
    }
  } catch (err) {
    console.error("Failed to fetch pipeline status:", err);
  }

  console.log("\n=== Polling (will run for 3 seconds) ===");
  const stopPolling = startPolling(
    (stages) => {
      const running = PIPELINE_STAGES.filter(
        (s) => stages[s].status === "running"
      );
      console.log(
        `  [poll] Running stages: ${running.length > 0 ? running.join(", ") : "none"}`
      );
    },
    (err) => {
      console.error(`  [poll] Error:`, err.message);
    },
    1000
  );

  // Stop polling after 3 seconds
  await new Promise<void>((resolve) => {
    setTimeout(() => {
      stopPolling();
      console.log("  Polling stopped.");

      // Restore original fetch
      globalThis.fetch = originalFetch;

      resolve();
    }, 3_000);
  });
}

if (require.main === module) {
  main().catch(console.error);
}
