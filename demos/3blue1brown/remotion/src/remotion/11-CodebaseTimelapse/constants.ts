import { z } from "zod";

// Video specs
export const CODEBASE_TIMELAPSE_FPS = 30;
export const CODEBASE_TIMELAPSE_DURATION_SECONDS = 25;
export const CODEBASE_TIMELAPSE_DURATION_FRAMES =
  CODEBASE_TIMELAPSE_FPS * CODEBASE_TIMELAPSE_DURATION_SECONDS;
export const CODEBASE_TIMELAPSE_WIDTH = 1920;
export const CODEBASE_TIMELAPSE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90: Clean codebase establishes (Day 1)
// Frame 90-300: First year of patches (Month 3, 6, 12)
// Frame 300-510: Second year (comments start)
// Frame 510-630: Third year (chaos mode)
// Frame 630-750: Hold on final chaotic state
export const BEATS = {
  CLEAN_START: 0,
  CLEAN_END: 90,              // 0-3s: Clean codebase
  YEAR1_START: 90,
  YEAR1_END: 300,             // 3-10s: First year patches
  YEAR2_START: 300,
  YEAR2_END: 510,             // 10-17s: Second year
  YEAR3_START: 510,
  YEAR3_END: 630,             // 17-21s: Third year (chaos)
  HOLD_START: 630,
  HOLD_END: 750,              // 21-25s: Hold
};

// Color palette - IDE-like dark theme
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NODE_CLEAN: "#4A90D9",
  NODE_YEAR1: "#7A8A9A",
  NODE_YEAR2: "#D9944A",
  NODE_YEAR3: "#D94A4A",
  EDGE_CLEAN: "rgba(74, 144, 217, 0.4)",
  EDGE_TANGLED: "rgba(217, 148, 74, 0.3)",
  PATCH_HIGHLIGHT: "#D9944A",
  COMMENT_TEXT: "#888888",
  COMMENT_BORDER: "#D9944A",
  COMMENT_BG: "rgba(0, 0, 0, 0.7)",
  TIME_LABEL: "#ffffff",
  WARNING_RED: "#D94A4A",
};

// File node initial positions (organized grid)
export interface FileNode {
  id: string;
  label: string;
  x: number;
  y: number;
  size: number;
}

// Initial clean codebase layout (organized grid of 12 modules)
export const INITIAL_NODES: FileNode[] = [
  { id: "auth",     label: "auth.py",       x: 300,  y: 250, size: 40 },
  { id: "users",    label: "users.py",      x: 550,  y: 250, size: 35 },
  { id: "api",      label: "api.py",        x: 800,  y: 250, size: 45 },
  { id: "db",       label: "database.py",   x: 1050, y: 250, size: 50 },
  { id: "models",   label: "models.py",     x: 300,  y: 450, size: 38 },
  { id: "views",    label: "views.py",      x: 550,  y: 450, size: 42 },
  { id: "routes",   label: "routes.py",     x: 800,  y: 450, size: 36 },
  { id: "utils",    label: "utils.py",      x: 1050, y: 450, size: 30 },
  { id: "config",   label: "config.py",     x: 300,  y: 650, size: 28 },
  { id: "tests",    label: "tests.py",      x: 550,  y: 650, size: 34 },
  { id: "deploy",   label: "deploy.py",     x: 800,  y: 650, size: 32 },
  { id: "logging",  label: "logging.py",    x: 1050, y: 650, size: 26 },
];

// Edges (dependencies)
export interface Edge {
  from: string;
  to: string;
}

export const INITIAL_EDGES: Edge[] = [
  { from: "auth", to: "users" },
  { from: "auth", to: "db" },
  { from: "api", to: "auth" },
  { from: "api", to: "routes" },
  { from: "routes", to: "views" },
  { from: "views", to: "models" },
  { from: "models", to: "db" },
  { from: "utils", to: "config" },
  { from: "tests", to: "api" },
  { from: "deploy", to: "config" },
  { from: "logging", to: "utils" },
];

// Additional tangled edges that appear over time
export const TANGLED_EDGES: { edge: Edge; appearAtFrame: number }[] = [
  { edge: { from: "views", to: "db" },       appearAtFrame: 120 },
  { edge: { from: "utils", to: "auth" },     appearAtFrame: 180 },
  { edge: { from: "routes", to: "db" },      appearAtFrame: 240 },
  { edge: { from: "logging", to: "api" },    appearAtFrame: 300 },
  { edge: { from: "deploy", to: "auth" },    appearAtFrame: 350 },
  { edge: { from: "tests", to: "db" },       appearAtFrame: 400 },
  { edge: { from: "config", to: "models" },  appearAtFrame: 450 },
  { edge: { from: "users", to: "logging" },  appearAtFrame: 500 },
  { edge: { from: "views", to: "utils" },    appearAtFrame: 530 },
  { edge: { from: "routes", to: "config" },  appearAtFrame: 560 },
];

// Warning comments
export interface WarningComment {
  text: string;
  appearAtFrame: number;
  x: number;
  y: number;
}

export const WARNING_COMMENTS: WarningComment[] = [
  { text: "// don't touch this",            appearAtFrame: 300, x: 350,  y: 180 },
  { text: "// legacy - do not modify",      appearAtFrame: 360, x: 700,  y: 350 },
  { text: '// temporary fix (2019)',        appearAtFrame: 420, x: 950,  y: 550 },
  { text: "// TODO: refactor",              appearAtFrame: 480, x: 200,  y: 520 },
  { text: "// workaround for bug #1234",    appearAtFrame: 540, x: 600,  y: 720 },
  { text: "// here be dragons",             appearAtFrame: 600, x: 1100, y: 320 },
];

// Patch highlight positions (which nodes get patches, and when)
export interface PatchEvent {
  nodeId: string;
  frame: number;
  type: "HACK" | "TODO" | "FIXME";
}

export const PATCH_EVENTS: PatchEvent[] = [
  { nodeId: "api",     frame: 100,  type: "HACK" },
  { nodeId: "views",   frame: 130,  type: "TODO" },
  { nodeId: "auth",    frame: 160,  type: "FIXME" },
  { nodeId: "db",      frame: 190,  type: "HACK" },
  { nodeId: "routes",  frame: 220,  type: "TODO" },
  { nodeId: "models",  frame: 250,  type: "HACK" },
  { nodeId: "users",   frame: 280,  type: "FIXME" },
  { nodeId: "api",     frame: 310,  type: "FIXME" },
  { nodeId: "utils",   frame: 340,  type: "HACK" },
  { nodeId: "views",   frame: 370,  type: "HACK" },
  { nodeId: "auth",    frame: 400,  type: "TODO" },
  { nodeId: "db",      frame: 420,  type: "FIXME" },
  { nodeId: "routes",  frame: 440,  type: "HACK" },
  { nodeId: "api",     frame: 460,  type: "HACK" },
  { nodeId: "models",  frame: 480,  type: "FIXME" },
  { nodeId: "views",   frame: 500,  type: "TODO" },
  { nodeId: "config",  frame: 520,  type: "HACK" },
  { nodeId: "logging", frame: 540,  type: "FIXME" },
  { nodeId: "deploy",  frame: 560,  type: "HACK" },
  { nodeId: "tests",   frame: 580,  type: "TODO" },
  { nodeId: "db",      frame: 600,  type: "HACK" },
  { nodeId: "auth",    frame: 610,  type: "HACK" },
  { nodeId: "api",     frame: 620,  type: "FIXME" },
];

// Time labels for the counter
export interface TimeLabel {
  label: string;
  frame: number;
}

export const TIME_LABELS: TimeLabel[] = [
  { label: "Day 1",     frame: 0 },
  { label: "Month 3",   frame: 120 },
  { label: "Month 6",   frame: 195 },
  { label: "Month 12",  frame: 270 },
  { label: "Year 2",    frame: 400 },
  { label: "Year 3",    frame: 540 },
];

// Node drift offsets per frame (simulates structure deterioration)
// Uses easeInOutSine for organic movement as specified in the spec
const easeInOutSine = (x: number): number => {
  return -(Math.cos(Math.PI * x) - 1) / 2;
};

export const getNodeDrift = (nodeIndex: number, frame: number): { dx: number; dy: number } => {
  const rawProgress = Math.min(frame / 600, 1);
  const driftIntensity = easeInOutSine(rawProgress);
  const seed = nodeIndex * 137.5; // Golden ratio-ish seed for variety
  return {
    dx: Math.sin(frame * 0.008 + seed) * 30 * driftIntensity +
        Math.sin(frame * 0.003 + seed * 2) * 15 * driftIntensity,
    dy: Math.cos(frame * 0.006 + seed * 0.7) * 20 * driftIntensity +
        Math.cos(frame * 0.004 + seed * 1.3) * 10 * driftIntensity,
  };
};

// Props schema
export const CodebaseTimelapseProps = z.object({
  showTimeCounter: z.boolean().default(true),
});

export const defaultCodebaseTimelapseProps: z.infer<typeof CodebaseTimelapseProps> = {
  showTimeCounter: true,
};

export type CodebaseTimelapsePropsType = z.infer<typeof CodebaseTimelapseProps>;
