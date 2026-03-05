/**
 * Tests for components/SseLogPanel.tsx
 *
 * PDD Principle: The prompt file is the source of truth.
 * These tests verify that the code conforms to the specification in
 * prompts/sse_log_panel_typescriptreact.prompt.
 *
 * Spec requirements verified:
 *   1. Props: jobId, onDone, onError, className
 *   2. When jobId is null, render nothing (return null)
 *   3. When jobId is set, open EventSource at /api/jobs/${jobId}/stream
 *   4. Append incoming data events as [HH:MM:SS] message lines to log buffer
 *   5. On event: done, show green success banner and call onDone()
 *   6. On event: error, show red error banner and call onError(message)
 *   7. Auto-scroll to bottom on each new log line
 *   8. Fall back to polling GET /api/jobs/${jobId} every 2s if EventSource fails
 *   9. Virtualize log list using CSS contain: content
 *  10. Close EventSource on unmount or jobId change
 *  11. 'use client' directive at the top
 */

import fs from "fs";
import path from "path";

// ---------------------------------------------------------------------------
// Source code (loaded once for structural tests)
// ---------------------------------------------------------------------------

const SOURCE_PATH = path.join(__dirname, "..", "components", "SseLogPanel.tsx");
const sourceCode = fs.readFileSync(SOURCE_PATH, "utf-8");

// ---------------------------------------------------------------------------
// 1. 'use client' directive
// ---------------------------------------------------------------------------

describe("'use client' directive", () => {
  it("has 'use client' as the very first line", () => {
    const firstLine = sourceCode.split("\n")[0].trim();
    expect(firstLine).toBe("'use client';");
  });
});

// ---------------------------------------------------------------------------
// 2. Props interface
// ---------------------------------------------------------------------------

describe("SseLogPanel props", () => {
  it("declares jobId: string | null prop", () => {
    expect(sourceCode).toMatch(/jobId\s*:\s*string\s*\|\s*null/);
  });

  it("declares optional onDone callback", () => {
    expect(sourceCode).toMatch(/onDone\?\s*:\s*\(\)\s*=>\s*void/);
  });

  it("declares optional onError callback with message param", () => {
    expect(sourceCode).toMatch(/onError\?\s*:\s*\(msg\s*:\s*string\)\s*=>\s*void/);
  });

  it("declares optional className prop", () => {
    expect(sourceCode).toMatch(/className\?\s*:\s*string/);
  });
});

// ---------------------------------------------------------------------------
// 3. Null render when jobId is null
// ---------------------------------------------------------------------------

describe("null jobId behavior", () => {
  it("returns null when jobId is falsy", () => {
    expect(sourceCode).toMatch(/if\s*\(\s*!jobId\s*\)\s*return\s+null/);
  });
});

// ---------------------------------------------------------------------------
// 4. EventSource connection
// ---------------------------------------------------------------------------

describe("EventSource connection", () => {
  it("opens EventSource at /api/jobs/${jobId}/stream", () => {
    expect(sourceCode).toMatch(
      /new\s+EventSource\s*\(\s*`\/api\/jobs\/\$\{jobId\}\/stream`\s*\)/
    );
  });

  it("uses useRef<EventSource | null>(null) for EventSource instance", () => {
    expect(sourceCode).toMatch(
      /useRef\s*<\s*EventSource\s*\|\s*null\s*>\s*\(\s*null\s*\)/
    );
  });

  it("has useEffect with [jobId] dependency", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?\}\s*,\s*\[jobId\]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 5. Log formatting — [HH:MM:SS] message
// ---------------------------------------------------------------------------

describe("log formatting", () => {
  it("uses toLocaleTimeString with en-US and hour12: false", () => {
    expect(sourceCode).toMatch(
      /toLocaleTimeString\s*\(\s*['"]en-US['"]\s*,\s*\{\s*hour12\s*:\s*false\s*\}\s*\)/
    );
  });

  it("formats logs as [timestamp] message", () => {
    expect(sourceCode).toMatch(/`\[\$\{ts\}\]\s+\$\{message\}`/);
  });

  it("uses state array for log buffer", () => {
    expect(sourceCode).toMatch(/useState\s*<\s*string\[\]\s*>\s*\(\s*\[\]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 6. Done event handling
// ---------------------------------------------------------------------------

describe("done event handling", () => {
  it("adds event listener for 'done' event", () => {
    expect(sourceCode).toMatch(/addEventListener\s*\(\s*['"]done['"]/);
  });

  it("calls onDone callback", () => {
    expect(sourceCode).toMatch(/onDone\?\.\(\)/);
  });

  it("shows success banner with green text and checkmark", () => {
    expect(sourceCode).toMatch(/text-green-400/);
    expect(sourceCode).toMatch(/✓ Completed/);
  });

  it("success banner uses correct className", () => {
    expect(sourceCode).toMatch(
      /className="mt-2 text-green-400 font-mono text-sm"/
    );
  });
});

// ---------------------------------------------------------------------------
// 7. Error event handling
// ---------------------------------------------------------------------------

describe("error event handling", () => {
  it("adds event listener for 'error' event", () => {
    expect(sourceCode).toMatch(/addEventListener\s*\(\s*['"]error['"]/);
  });

  it("calls onError callback with message", () => {
    expect(sourceCode).toMatch(/onError\?\.\(.*\)/);
  });

  it("shows error banner with red text and cross mark", () => {
    expect(sourceCode).toMatch(/text-red-400/);
    expect(sourceCode).toMatch(/✕ Error:/);
  });

  it("error banner uses correct className", () => {
    expect(sourceCode).toMatch(
      /className="mt-2 text-red-400 font-mono text-sm"/
    );
  });
});

// ---------------------------------------------------------------------------
// 8. Auto-scroll behavior
// ---------------------------------------------------------------------------

describe("auto-scroll behavior", () => {
  it("uses scrollTo with smooth behavior", () => {
    expect(sourceCode).toMatch(
      /scrollTo\s*\(\s*\{[\s\S]*?behavior\s*:\s*['"]smooth['"]/
    );
  });

  it("scrolls to scrollHeight", () => {
    expect(sourceCode).toMatch(/top\s*:\s*logRef\.current\.scrollHeight/);
  });

  it("has useEffect dependent on logs", () => {
    expect(sourceCode).toMatch(/useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?scrollTo[\s\S]*?\}\s*,\s*\[logs\]\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 9. Polling fallback
// ---------------------------------------------------------------------------

describe("polling fallback", () => {
  it("falls back to polling when EventSource is undefined", () => {
    expect(sourceCode).toMatch(
      /typeof\s+EventSource\s*===\s*['"]undefined['"]/
    );
  });

  it("polls /api/jobs/${id} endpoint", () => {
    expect(sourceCode).toMatch(/fetch\s*\(\s*`\/api\/jobs\/\$\{id\}`\s*\)/);
  });

  it("uses 2000ms polling interval", () => {
    expect(sourceCode).toMatch(/setInterval\s*\(\s*async[\s\S]*?2000\s*\)/);
  });

  it("starts polling when EventSource constructor throws", () => {
    // The catch block should start polling
    expect(sourceCode).toMatch(/catch\s*\{[\s\S]*?startPolling/);
  });

  it("checks job.status for done and error", () => {
    expect(sourceCode).toMatch(/job\.status\s*===\s*['"]done['"]/);
    expect(sourceCode).toMatch(/job\.status\s*===\s*['"]error['"]/);
  });

  it("stops polling when job completes", () => {
    expect(sourceCode).toMatch(/stopPolling\s*\(\)/);
  });
});

// ---------------------------------------------------------------------------
// 10. CSS virtualization
// ---------------------------------------------------------------------------

describe("CSS virtualization", () => {
  it("uses contain: content for log container (not strict, which collapses height)", () => {
    expect(sourceCode).toMatch(/contain\s*:\s*['"]content['"]/);
  });

  it("log container has overflow-y: auto via className", () => {
    expect(sourceCode).toMatch(/overflow-y-auto/);
  });
});

// ---------------------------------------------------------------------------
// 11. Log container styling
// ---------------------------------------------------------------------------

describe("log container", () => {
  it("uses logClassName prop to allow overriding default max-h-64", () => {
    expect(sourceCode).toMatch(/logClassName\s*\?\?\s*['"]max-h-64['"]/);
  });

  it("declares optional logClassName prop", () => {
    expect(sourceCode).toMatch(/logClassName\?\s*:\s*string/);
  });

  it("uses a div ref for the log container", () => {
    expect(sourceCode).toMatch(/ref=\{logRef\}/);
  });
});

// ---------------------------------------------------------------------------
// 12. Cleanup on unmount / jobId change
// ---------------------------------------------------------------------------

describe("cleanup behavior", () => {
  it("closes EventSource in useEffect cleanup", () => {
    expect(sourceCode).toMatch(/eventSourceRef\.current\?\.close\(\)/);
  });

  it("stops polling in cleanup", () => {
    // cleanup function should stop polling
    expect(sourceCode).toMatch(
      /return\s*\(\)\s*=>\s*\{[\s\S]*?stopPolling\s*\(\)/
    );
  });

  it("resets state when jobId changes", () => {
    expect(sourceCode).toMatch(/setLogs\s*\(\s*\[\]\s*\)/);
    expect(sourceCode).toMatch(/setCompleted\s*\(\s*false\s*\)/);
    expect(sourceCode).toMatch(/setErrorMsg\s*\(\s*null\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 13. EventSource data parsing
// ---------------------------------------------------------------------------

describe("event data parsing", () => {
  it("parses event data with JSON.parse", () => {
    expect(sourceCode).toMatch(/JSON\.parse\s*\(\s*event\.data\s*\)/);
  });

  it("extracts message field from parsed data", () => {
    expect(sourceCode).toMatch(/data\?\.message/);
  });

  it("handles JSON parse failure gracefully", () => {
    // Should have a catch that appends event.data directly
    expect(sourceCode).toMatch(/catch\s*\{[\s\S]*?appendLog\s*\(\s*event\.data\s*\)/);
  });
});

// ---------------------------------------------------------------------------
// 14. Export shape
// ---------------------------------------------------------------------------

describe("export shape", () => {
  it("exports SseLogPanel as named export", () => {
    expect(sourceCode).toMatch(/export\s+const\s+SseLogPanel/);
  });

  it("exports default SseLogPanel", () => {
    expect(sourceCode).toMatch(/export\s+default\s+SseLogPanel/);
  });

  it("is a React.FC component", () => {
    expect(sourceCode).toMatch(/React\.FC\s*<\s*SseLogPanelProps\s*>/);
  });
});

// ---------------------------------------------------------------------------
// 15. Import structure
// ---------------------------------------------------------------------------

describe("import structure", () => {
  it("imports React hooks: useEffect, useRef, useState", () => {
    expect(sourceCode).toMatch(/import.*useEffect.*from\s+['"]react['"]/);
    expect(sourceCode).toMatch(/import.*useRef.*from\s+['"]react['"]/);
    expect(sourceCode).toMatch(/import.*useState.*from\s+['"]react['"]/);
  });

  it("imports Job type", () => {
    expect(sourceCode).toMatch(/import\s+type\s*\{\s*Job\s*\}/);
  });
});

// ---------------------------------------------------------------------------
// 16. Component is pure display (no job control)
// ---------------------------------------------------------------------------

describe("pure display component", () => {
  it("does not export any job control functions", () => {
    // Should not have functions like startJob, stopJob, etc.
    expect(sourceCode).not.toMatch(/export\s+(const|function)\s+(startJob|stopJob|runJob|executeJob)/);
  });

  it("does not POST or PUT to any endpoint", () => {
    expect(sourceCode).not.toMatch(/method\s*:\s*['"]POST['"]/);
    expect(sourceCode).not.toMatch(/method\s*:\s*['"]PUT['"]/);
  });
});

// ---------------------------------------------------------------------------
// 17. Guard against duplicate callbacks
// ---------------------------------------------------------------------------

describe("callback deduplication", () => {
  it("uses ref to prevent duplicate done calls", () => {
    expect(sourceCode).toMatch(/doneCalledRef/);
  });

  it("uses ref to prevent duplicate error calls", () => {
    expect(sourceCode).toMatch(/errorCalledRef/);
  });
});

// ---------------------------------------------------------------------------
// 18. Connection error → polling fallback
// ---------------------------------------------------------------------------

describe("connection error fallback", () => {
  it("closes EventSource on onerror", () => {
    expect(sourceCode).toMatch(/es\.onerror\s*=\s*\(\)\s*=>\s*\{[\s\S]*?es\.close\(\)/);
  });

  it("starts polling after onerror", () => {
    expect(sourceCode).toMatch(/es\.onerror\s*=\s*\(\)\s*=>\s*\{[\s\S]*?startPolling/);
  });
});

// ---------------------------------------------------------------------------
// 19. Module-level structure checks
// ---------------------------------------------------------------------------

describe("module structure", () => {
  it("file exists at expected path", () => {
    expect(fs.existsSync(SOURCE_PATH)).toBe(true);
  });

  it("is a TypeScript React file", () => {
    expect(SOURCE_PATH).toMatch(/\.tsx$/);
  });

  it("does not import external virtualization libraries", () => {
    expect(sourceCode).not.toMatch(/import.*react-virtualized/);
    expect(sourceCode).not.toMatch(/import.*react-window/);
    expect(sourceCode).not.toMatch(/import.*react-virtuoso/);
  });

  it("uses onmessage handler for incoming data events", () => {
    expect(sourceCode).toMatch(/es\.onmessage\s*=/);
  });
});
