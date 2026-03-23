// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";
export const EDITOR_BG = "#161B22";
export const TAB_BAR_BG = "#1C2128";
export const TAB_ACTIVE_BG = "#0D1117";
export const TAB_INACTIVE_BG = "#1C2128";
export const TAB_BORDER = "#30363D";
export const SIDEBAR_BG = "#0D1117";
export const SIDEBAR_BORDER = "#21262D";

export const HIGHLIGHT_GREEN = "#5AAA6E";
export const HIGHLIGHT_GREEN_BG = "rgba(90, 170, 110, 0.15)";
export const DIFF_ADD = "#5AAA6E";
export const DIFF_REMOVE = "#E74C3C";
export const DIFF_MODIFY = "#D9944A";

export const TEXT_PRIMARY = "#E2E8F0";
export const TEXT_SECONDARY = "#94A3B8";
export const TEXT_DIM = "#6B7280";
export const TODO_LABEL_COLOR = "#E74C3C";

// Syntax colors
export const SYNTAX_KEYWORD = "#FF7B72";
export const SYNTAX_STRING = "#A5D6FF";
export const SYNTAX_TYPE = "#79C0FF";
export const SYNTAX_FUNCTION = "#D2A8FF";
export const SYNTAX_COMMENT = "#8B949E";
export const SYNTAX_VARIABLE = "#FFA657";
export const SYNTAX_PLAIN = "#C9D1D9";
export const SYNTAX_NUMBER = "#79C0FF";

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 164;

export const TAB_HEIGHT = 35;
export const LINE_HEIGHT = 20;
export const CODE_FONT_SIZE = 13;
export const CODE_LEFT_PADDING = 60;
export const LINE_NUMBER_WIDTH = 45;

// ── Zoom Levels ─────────────────────────────────────────────────────
export const ZOOM_LEVELS = [
  { scale: 1.0, frame: 0 },
  { scale: 0.6, frame: 15 },
  { scale: 0.3, frame: 50 },
  { scale: 0.15, frame: 90 },
  { scale: 0.10, frame: 120 },
] as const;

export const DRIFT_START_FRAME = 140;
export const DRIFT_PX_PER_FRAME = -0.5;

// ── Animation Timing ────────────────────────────────────────────────
export const LAYER1_START = 15;
export const LAYER2_START = 50;
export const LAYER3_START = 90;
export const FINAL_HOLD_START = 140;

// ── Code Content ────────────────────────────────────────────────────
export interface CodeLine {
  lineNum: number;
  tokens: Array<{ text: string; color: string }>;
  isHighlighted?: boolean;
}

export const USER_SERVICE_CODE: CodeLine[] = [
  {
    lineNum: 1,
    tokens: [
      { text: "import", color: SYNTAX_KEYWORD },
      { text: " { Injectable } ", color: SYNTAX_PLAIN },
      { text: "from", color: SYNTAX_KEYWORD },
      { text: " '@nestjs/common'", color: SYNTAX_STRING },
    ],
  },
  {
    lineNum: 2,
    tokens: [
      { text: "import", color: SYNTAX_KEYWORD },
      { text: " { Repository } ", color: SYNTAX_PLAIN },
      { text: "from", color: SYNTAX_KEYWORD },
      { text: " 'typeorm'", color: SYNTAX_STRING },
    ],
  },
  { lineNum: 3, tokens: [] },
  {
    lineNum: 4,
    tokens: [
      { text: "@Injectable", color: SYNTAX_FUNCTION },
      { text: "()", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 5,
    tokens: [
      { text: "export", color: SYNTAX_KEYWORD },
      { text: " class", color: SYNTAX_KEYWORD },
      { text: " UserService", color: SYNTAX_TYPE },
      { text: " {", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 6,
    tokens: [
      { text: "  constructor", color: SYNTAX_FUNCTION },
      { text: "(", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 7,
    tokens: [
      { text: "    private", color: SYNTAX_KEYWORD },
      { text: " readonly", color: SYNTAX_KEYWORD },
      { text: " userRepo", color: SYNTAX_VARIABLE },
      { text: ": ", color: SYNTAX_PLAIN },
      { text: "Repository", color: SYNTAX_TYPE },
      { text: "<", color: SYNTAX_PLAIN },
      { text: "User", color: SYNTAX_TYPE },
      { text: ">", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 8,
    tokens: [
      { text: "  ) {}", color: SYNTAX_PLAIN },
    ],
  },
  { lineNum: 9, tokens: [] },
  {
    lineNum: 10,
    tokens: [
      { text: "  ", color: SYNTAX_PLAIN },
      { text: "async", color: SYNTAX_KEYWORD },
      { text: " findByEmail", color: SYNTAX_FUNCTION },
      { text: "(", color: SYNTAX_PLAIN },
      { text: "email", color: SYNTAX_VARIABLE },
      { text: ": ", color: SYNTAX_PLAIN },
      { text: "string", color: SYNTAX_TYPE },
      { text: ") {", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 11,
    tokens: [
      { text: "    ", color: SYNTAX_PLAIN },
      { text: "const", color: SYNTAX_KEYWORD },
      { text: " user = ", color: SYNTAX_PLAIN },
      { text: "await", color: SYNTAX_KEYWORD },
      { text: " this", color: SYNTAX_KEYWORD },
      { text: ".userRepo.findOne({", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 12,
    tokens: [
      { text: "      where", color: SYNTAX_PLAIN },
      { text: ": { ", color: SYNTAX_PLAIN },
      { text: "email", color: SYNTAX_VARIABLE },
      { text: " }", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 13,
    tokens: [
      { text: "    });", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 14,
    tokens: [
      { text: "    ", color: SYNTAX_PLAIN },
      { text: "return", color: SYNTAX_KEYWORD },
      { text: " user", color: SYNTAX_PLAIN },
      { text: "?.", color: SYNTAX_PLAIN },
      { text: "sanitize", color: SYNTAX_FUNCTION },
      { text: "() ?? ", color: SYNTAX_PLAIN },
      { text: "null", color: SYNTAX_KEYWORD },
      { text: ";", color: SYNTAX_PLAIN },
    ],
    isHighlighted: true,
  },
  {
    lineNum: 15,
    tokens: [
      { text: "  }", color: SYNTAX_PLAIN },
    ],
  },
  { lineNum: 16, tokens: [] },
  {
    lineNum: 17,
    tokens: [
      { text: "  ", color: SYNTAX_PLAIN },
      { text: "// TODO: add pagination", color: SYNTAX_COMMENT },
    ],
  },
  {
    lineNum: 18,
    tokens: [
      { text: "  ", color: SYNTAX_PLAIN },
      { text: "async", color: SYNTAX_KEYWORD },
      { text: " listAll", color: SYNTAX_FUNCTION },
      { text: "() {", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 19,
    tokens: [
      { text: "    ", color: SYNTAX_PLAIN },
      { text: "return", color: SYNTAX_KEYWORD },
      { text: " this", color: SYNTAX_KEYWORD },
      { text: ".userRepo.find();", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 20,
    tokens: [
      { text: "  }", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 21,
    tokens: [
      { text: "}", color: SYNTAX_PLAIN },
    ],
  },
];

// ── File Tree Data ──────────────────────────────────────────────────
export interface FileTreeNode {
  name: string;
  indent: number;
  isDir: boolean;
  isExpanded?: boolean;
}

export const FILE_TREE: FileTreeNode[] = [
  { name: "src", indent: 0, isDir: true, isExpanded: true },
  { name: "auth", indent: 1, isDir: true, isExpanded: true },
  { name: "AuthController.ts", indent: 2, isDir: false },
  { name: "AuthService.ts", indent: 2, isDir: false },
  { name: "auth.guard.ts", indent: 2, isDir: false },
  { name: "jwt.strategy.ts", indent: 2, isDir: false },
  { name: "database", indent: 1, isDir: true, isExpanded: true },
  { name: "DatabaseHelper.ts", indent: 2, isDir: false },
  { name: "migrations", indent: 2, isDir: true, isExpanded: true },
  { name: "001_init.ts", indent: 3, isDir: false },
  { name: "002_add_users.ts", indent: 3, isDir: false },
  { name: "003_fix_index.ts", indent: 3, isDir: false },
  { name: "004_add_roles.ts", indent: 3, isDir: false },
  { name: "005_temp_patch.ts", indent: 3, isDir: false },
  { name: "entities", indent: 2, isDir: true, isExpanded: true },
  { name: "User.ts", indent: 3, isDir: false },
  { name: "Role.ts", indent: 3, isDir: false },
  { name: "Session.ts", indent: 3, isDir: false },
  { name: "legacy", indent: 1, isDir: true, isExpanded: true },
  { name: "legacy_utils.py", indent: 2, isDir: false },
  { name: "old_auth.js", indent: 2, isDir: false },
  { name: "convert.sh", indent: 2, isDir: false },
  { name: "users", indent: 1, isDir: true, isExpanded: true },
  { name: "UserService.ts", indent: 2, isDir: false },
  { name: "UserController.ts", indent: 2, isDir: false },
  { name: "user.dto.ts", indent: 2, isDir: false },
  { name: "utils", indent: 1, isDir: true, isExpanded: true },
  { name: "helpers.ts", indent: 2, isDir: false },
  { name: "logger.ts", indent: 2, isDir: false },
  { name: "cache.ts", indent: 2, isDir: false },
  { name: "constants.ts", indent: 2, isDir: false },
  { name: "config", indent: 1, isDir: true, isExpanded: true },
  { name: "app.config.ts", indent: 2, isDir: false },
  { name: "db.config.ts", indent: 2, isDir: false },
  { name: "redis.config.ts", indent: 2, isDir: false },
  { name: "middleware", indent: 1, isDir: true },
  { name: "tests", indent: 1, isDir: true },
  { name: "scripts", indent: 1, isDir: true, isExpanded: true },
  { name: "deploy.sh", indent: 2, isDir: false },
  { name: "seed.ts", indent: 2, isDir: false },
  { name: "cleanup.ts", indent: 2, isDir: false },
  { name: "node_modules", indent: 0, isDir: true },
  { name: "package.json", indent: 0, isDir: false },
  { name: "tsconfig.json", indent: 0, isDir: false },
  { name: ".env", indent: 0, isDir: false },
  { name: "docker-compose.yml", indent: 0, isDir: false },
];

// ── TODO/HACK Labels ────────────────────────────────────────────────
export interface TodoLabelData {
  text: string;
  x: number;
  y: number;
  rotation: number;
}

export const TODO_LABELS: TodoLabelData[] = [
  { text: "// HACK", x: 1200, y: 280, rotation: -1.5 },
  { text: "// temporary fix (2019)", x: 600, y: 720, rotation: 1.2 },
  { text: "// don't touch this", x: 1400, y: 550, rotation: -0.8 },
  { text: "// TODO: refactor someday", x: 300, y: 850, rotation: 2.0 },
  { text: "// FIXME", x: 1100, y: 150, rotation: -1.0 },
  { text: "// legacy — do not delete", x: 850, y: 950, rotation: 1.5 },
  { text: "// workaround for #4281", x: 1500, y: 400, rotation: -2.0 },
  { text: "// ??? why does this work", x: 200, y: 450, rotation: 0.5 },
];

// ── Diff Marker positions ───────────────────────────────────────────
export interface DiffMarkerData {
  symbol: "+" | "-" | "~";
  x: number;
  y: number;
  color: string;
}

function generateDiffMarkers(): DiffMarkerData[] {
  const markers: DiffMarkerData[] = [];
  const symbols: Array<"+" | "-" | "~"> = ["+", "-", "~"];
  const colors = [DIFF_ADD, DIFF_REMOVE, DIFF_MODIFY];

  // Deterministic pseudo-random positions
  const positions = [
    [480, 120], [720, 200], [550, 340], [900, 160], [380, 500],
    [1100, 280], [650, 420], [820, 580], [1300, 340], [450, 660],
    [1050, 460], [750, 750], [300, 380], [1200, 520], [580, 850],
    [950, 700], [1400, 180], [680, 600], [1150, 780], [400, 250],
    [1000, 900], [530, 180], [870, 450], [1350, 640], [250, 700],
  ];

  for (let i = 0; i < 25; i++) {
    const idx = i % 3;
    markers.push({
      symbol: symbols[idx],
      x: positions[i][0],
      y: positions[i][1],
      color: colors[idx],
    });
  }
  return markers;
}

export const DIFF_MARKERS = generateDiffMarkers();

// ── Tab Data ────────────────────────────────────────────────────────
export interface TabData {
  name: string;
  isActive: boolean;
  isModified: boolean;
}

export const INITIAL_TABS: TabData[] = [
  { name: "UserService.ts", isActive: true, isModified: true },
];

export const EXPANDED_TABS: TabData[] = [
  { name: "UserService.ts", isActive: true, isModified: true },
  { name: "AuthController.ts", isActive: false, isModified: false },
  { name: "DatabaseHelper.ts", isActive: false, isModified: true },
  { name: "legacy_utils.py", isActive: false, isModified: false },
];

// ── Secondary Code Snippets (for adjacent files) ────────────────────
export const AUTH_CONTROLLER_CODE: CodeLine[] = [
  {
    lineNum: 1,
    tokens: [
      { text: "import", color: SYNTAX_KEYWORD },
      { text: " { Controller, Post } ", color: SYNTAX_PLAIN },
      { text: "from", color: SYNTAX_KEYWORD },
      { text: " '@nestjs/common'", color: SYNTAX_STRING },
    ],
  },
  { lineNum: 2, tokens: [] },
  {
    lineNum: 3,
    tokens: [
      { text: "@Controller", color: SYNTAX_FUNCTION },
      { text: "('auth')", color: SYNTAX_STRING },
    ],
  },
  {
    lineNum: 4,
    tokens: [
      { text: "export", color: SYNTAX_KEYWORD },
      { text: " class", color: SYNTAX_KEYWORD },
      { text: " AuthController", color: SYNTAX_TYPE },
      { text: " {", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 5,
    tokens: [
      { text: "  ", color: SYNTAX_PLAIN },
      { text: "// HACK: bypass rate limit for now", color: SYNTAX_COMMENT },
    ],
  },
  {
    lineNum: 6,
    tokens: [
      { text: "  @Post", color: SYNTAX_FUNCTION },
      { text: "('login')", color: SYNTAX_STRING },
    ],
  },
  {
    lineNum: 7,
    tokens: [
      { text: "  ", color: SYNTAX_PLAIN },
      { text: "async", color: SYNTAX_KEYWORD },
      { text: " login", color: SYNTAX_FUNCTION },
      { text: "(", color: SYNTAX_PLAIN },
      { text: "@Body", color: SYNTAX_FUNCTION },
      { text: "() dto) {", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 8,
    tokens: [
      { text: "    ", color: SYNTAX_PLAIN },
      { text: "// temporary fix", color: SYNTAX_COMMENT },
    ],
  },
  {
    lineNum: 9,
    tokens: [
      { text: "    ", color: SYNTAX_PLAIN },
      { text: "return", color: SYNTAX_KEYWORD },
      { text: " this", color: SYNTAX_KEYWORD },
      { text: ".authService.login(dto);", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 10,
    tokens: [
      { text: "  }", color: SYNTAX_PLAIN },
    ],
  },
  {
    lineNum: 11,
    tokens: [
      { text: "}", color: SYNTAX_PLAIN },
    ],
  },
];

// ── Mini editor pane code snippets ──────────────────────────────────
export const MINI_PANE_SNIPPETS: CodeLine[][] = [
  // Pane 1: config-like
  [
    { lineNum: 1, tokens: [{ text: "export default {", color: SYNTAX_PLAIN }] },
    { lineNum: 2, tokens: [{ text: "  port: 3000,", color: SYNTAX_PLAIN }] },
    { lineNum: 3, tokens: [{ text: "  // don't change", color: SYNTAX_COMMENT }] },
    { lineNum: 4, tokens: [{ text: "  db: 'postgres',", color: SYNTAX_STRING }] },
    { lineNum: 5, tokens: [{ text: "}", color: SYNTAX_PLAIN }] },
  ],
  // Pane 2: test file
  [
    { lineNum: 1, tokens: [{ text: "describe('User',", color: SYNTAX_FUNCTION }] },
    { lineNum: 2, tokens: [{ text: "  () => {", color: SYNTAX_PLAIN }] },
    { lineNum: 3, tokens: [{ text: "  it('works',", color: SYNTAX_FUNCTION }] },
    { lineNum: 4, tokens: [{ text: "    async () =>", color: SYNTAX_KEYWORD }] },
    { lineNum: 5, tokens: [{ text: "  // TODO", color: SYNTAX_COMMENT }] },
  ],
  // Pane 3: utility
  [
    { lineNum: 1, tokens: [{ text: "export function", color: SYNTAX_KEYWORD }] },
    { lineNum: 2, tokens: [{ text: "  hash(input) {", color: SYNTAX_FUNCTION }] },
    { lineNum: 3, tokens: [{ text: "  // FIXME: weak", color: SYNTAX_COMMENT }] },
    { lineNum: 4, tokens: [{ text: "  return md5(i)", color: SYNTAX_PLAIN }] },
    { lineNum: 5, tokens: [{ text: "}", color: SYNTAX_PLAIN }] },
  ],
];
