import { NextRequest } from "next/server";
import path from "path";
import fs from "fs";
import { spawn } from "child_process";

import { runPipelineStage, registerExecutor } from "@/lib/jobs";
import { runClaudeFix } from "@/lib/claude";
import type { SseSend } from "@/lib/types";

type RunBody = {
  components?: string[];
  wrappers?: string[];
};

const REMOTION_SCOPE_DIR = path.join(process.cwd(), "remotion/src/remotion");
const SPECS_DIR = path.join(process.cwd(), "specs");

// ---------------------------------------------------------------------------
// SSE helper
// ---------------------------------------------------------------------------
function createSseStream() {
  const stream = new TransformStream();
  const writer = stream.writable.getWriter();
  const encoder = new TextEncoder();

  const send = (data: object) => {
    const payload = `data: ${JSON.stringify(data)}\n\n`;
    writer.write(encoder.encode(payload));
  };

  const done = () => writer.close();
  const error = (message: string) => {
    send({ type: "error", message });
    writer.close();
  };

  return { stream: stream.readable, send, done, error };
}

// ---------------------------------------------------------------------------
// Utility: find spec file content for a component (best effort)
// ---------------------------------------------------------------------------
function findSpecForComponent(componentName: string): string {
  if (!fs.existsSync(SPECS_DIR)) return "";

  const matches: string[] = [];

  const walk = (dir: string) => {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      if (entry.isFile()) {
        const base = path.basename(entry.name, path.extname(entry.name));
        if (base === componentName) matches.push(p);
      }
    }
  };

  walk(SPECS_DIR);

  if (!matches.length) return "";
  try {
    return fs.readFileSync(matches[0], "utf-8");
  } catch {
    return "";
  }
}

// ---------------------------------------------------------------------------
// Claude prompt factory
// ---------------------------------------------------------------------------
function buildComponentPrompt(name: string, spec: string): string {
  return `
You are Claude Code. Generate a Remotion component.

Component name: ${name}
Target directory: remotion/src/remotion/
Output file: remotion/src/remotion/${name}.tsx

Use the spec below to implement the component accurately.

--- SPEC ---
${spec || "(spec not found, infer from naming)"}
--- END SPEC ---

Return valid TypeScript/React code.
`;
}

// ---------------------------------------------------------------------------
// Executor registration for compositions stage
// ---------------------------------------------------------------------------
registerExecutor("compositions", (params, send: SseSend) => {
  return async (onLog) => {
    const components = (params.components as string[]) ?? [];
    const wrappers = (params.wrappers as string[]) ?? [];

    const progressFn = (onLog as unknown as { progress?: (p: number) => void })
      .progress;

    const total = components.length + wrappers.length || 1;
    let completed = 0;

    // Generate components via Claude Code
    for (const name of components) {
      send({ type: "component", name, status: "generating" });
      onLog(`[compositions] Generating component: ${name}`);

      try {
        const spec = findSpecForComponent(name);
        const prompt = buildComponentPrompt(name, spec);

        await runClaudeFix(prompt, REMOTION_SCOPE_DIR, (line) => onLog(line));

        send({ type: "component", name, status: "done" });
      } catch (err) {
        const msg = err instanceof Error ? err.message : "Unknown error";
        send({ type: "component", name, status: "error" });
        onLog(`[compositions] Error generating ${name}: ${msg}`);
        throw err;
      } finally {
        completed++;
        progressFn?.(Math.round((completed / total) * 100));
      }
    }

    // Generate wrappers via python script
    if (wrappers.length > 0) {
      for (const name of wrappers) {
        send({ type: "component", name, status: "generating" });
      }

      await new Promise<void>((resolve, reject) => {
        const proc = spawn("python3", ["generate_section_compositions.py"], {
          cwd: process.cwd(),
          stdio: ["ignore", "pipe", "pipe"],
        });

        proc.stdout.on("data", (d) => onLog(d.toString()));
        proc.stderr.on("data", (d) => onLog(d.toString()));

        proc.on("close", (code) => {
          if (code === 0) resolve();
          else reject(new Error(`Wrapper generation failed (code ${code})`));
        });
      });

      for (const name of wrappers) {
        const filePath = path.join(REMOTION_SCOPE_DIR, `${name}.tsx`);
        if (fs.existsSync(filePath)) {
          send({ type: "component", name, status: "done" });
        } else {
          send({ type: "component", name, status: "error" });
        }
        completed++;
        progressFn?.(Math.round((completed / total) * 100));
      }
    }
  };
});

// ---------------------------------------------------------------------------
// Route handler: POST /api/pipeline/compositions/run
// ---------------------------------------------------------------------------
export async function POST(request: NextRequest): Promise<Response> {
  const body = (await request.json()) as RunBody;
  const { stream, send, done, error } = createSseStream();

  (async () => {
    try {
      const jobId = await runPipelineStage("compositions", body, send);
      send({ type: "job", jobId });
      send({ type: "complete", jobId });
      done();
    } catch (err) {
      const msg = err instanceof Error ? err.message : "Unknown error";
      error(msg);
    }
  })();

  return new Response(stream, {
    headers: {
      "Content-Type": "text/event-stream",
      "Cache-Control": "no-cache",
      Connection: "keep-alive",
    },
  });
}

// --- Asset Staging Handler ---

import { NextResponse } from "next/server";
import crypto from "crypto";

type AssetStagingBody = {
  files?: string[];
};

const VEO_OUTPUT_DIR = path.join(process.cwd(), "outputs/veo");
const REMOTION_PUBLIC_DIR = path.join(process.cwd(), "remotion/public");

function loadManifestFiles(): string[] {
  const candidates = [
    path.join(VEO_OUTPUT_DIR, "staging.json"),
    path.join(VEO_OUTPUT_DIR, "staging-manifest.json"),
    path.join(VEO_OUTPUT_DIR, "manifest.json"),
  ];

  for (const p of candidates) {
    if (fs.existsSync(p)) {
      const raw = fs.readFileSync(p, "utf-8");
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed)) return parsed;
      if (Array.isArray(parsed.files)) return parsed.files;
    }
  }

  return [];
}

export async function POST_AssetStaging(request: NextRequest): Promise<NextResponse> {
  const body = (await request.json()) as AssetStagingBody;
  const files = body.files && body.files.length ? body.files : loadManifestFiles();

  const jobId = crypto.randomUUID();

  for (const file of files) {
    const src = path.join(VEO_OUTPUT_DIR, file);
    const dest = path.join(REMOTION_PUBLIC_DIR, file);

    if (!fs.existsSync(src)) continue;

    if (!fs.existsSync(dest)) {
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.copyFileSync(src, dest);
    }
  }

  return NextResponse.json({ jobId }, { status: 200 });
}

// --- Composition List Handler ---

import { loadProject } from "@/lib/project";
import type {
  CompositionEntry,
  CompositionSection,
  ProjectConfig,
} from "@/lib/types";

const REMOTION_DIR = path.join(process.cwd(), "remotion/src/remotion");

function listSpecComponents(specDir: string): string[] {
  if (!fs.existsSync(specDir)) return [];
  const names: Set<string> = new Set();

  const walk = (dir: string) => {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    for (const entry of entries) {
      const p = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      if (entry.isFile()) {
        const base = path.basename(entry.name, path.extname(entry.name));
        names.add(base);
      }
    }
  };

  walk(specDir);
  return Array.from(names);
}

function getLastErrorForComponent(name: string): string | undefined {
  try {
    const Database = require("better-sqlite3");
    const dbPath = process.env.DB_PATH ?? "data/jobs.sqlite";

    if (!fs.existsSync(dbPath)) return undefined;
    const db = new Database(dbPath);

    const rows = db
      .prepare(
        "SELECT error, params, updatedAt FROM jobs WHERE stage = 'compositions' AND status = 'error' ORDER BY updatedAt DESC"
      )
      .all();

    for (const row of rows) {
      try {
        const params = JSON.parse(row.params ?? "{}");
        const list = [
          ...(params.components ?? []),
          ...(params.wrappers ?? []),
        ];
        if (list.includes(name)) {
          db.close();
          return row.error as string;
        }
      } catch {
        continue;
      }
    }

    db.close();
  } catch {
    return undefined;
  }

  return undefined;
}

function buildEntry(name: string): CompositionEntry {
  const filePath = path.join(REMOTION_DIR, `${name}.tsx`);
  const exists = fs.existsSync(filePath);
  const lastError = getLastErrorForComponent(name);

  if (lastError) {
    return { name, status: "error", lastError };
  }

  return { name, status: exists ? "exists" : "missing" };
}

export async function GET_CompositionList(): Promise<NextResponse> {
  let config: ProjectConfig;

  try {
    config = loadProject();
  } catch (err) {
    return NextResponse.json(
      { error: "Failed to load project config" },
      { status: 500 }
    );
  }

  const sections: CompositionSection[] = config.sections.map((section) => {
    const componentNames = listSpecComponents(
      path.join(process.cwd(), section.specDir)
    );

    const wrapperNames = Array.from(
      new Set([
        `${section.id}Wrapper`,
        `${section.compositionId}Wrapper`,
      ])
    );

    return {
      sectionId: section.id,
      components: componentNames.map(buildEntry),
      wrappers: wrapperNames.map(buildEntry),
    };
  });

  return NextResponse.json({ sections }, { status: 200 });
}