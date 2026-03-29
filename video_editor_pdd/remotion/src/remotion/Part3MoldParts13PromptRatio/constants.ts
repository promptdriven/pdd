// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const DURATION_FRAMES = 540;
export const FPS = 30;

// ── Colors ──
export const BLOCK_BG = "#1E1E2E";
export const PROMPT_ACCENT = "#D9944A";
export const CODE_BORDER = "#334155";
export const CODE_LABEL_COLOR = "#64748B";
export const RATIO_COLOR = "#E2E8F0";
export const SUBLABEL_COLOR = "#94A3B8";
export const RED_TINT = "#EF4444";
export const RED_LABEL = "#F87171";
export const GREEN_TINT = "#4ADE80";

// ── Phase 1: Prompt block ──
export const PROMPT_X = 200;
export const PROMPT_Y = 300;
export const PROMPT_WIDTH = 300;
export const PROMPT_HEIGHT = 200;

// ── Phase 1: Code block ──
export const CODE_X = 600;
export const CODE_Y = 180;
export const CODE_WIDTH = 1150;
export const CODE_HEIGHT = 600;

// ── Phase 2: Context windows ──
export const CTX_WINDOW_WIDTH = 400;
export const CTX_WINDOW_HEIGHT = 500;
export const CTX_LEFT_X = 300;
export const CTX_RIGHT_X = 1220;
export const CTX_Y = 260;

// ── Animation frame boundaries ──
export const PROMPT_FADE_START = 0;
export const PROMPT_FADE_DUR = 20;
export const CODE_FADE_START = 30;
export const CODE_FADE_DUR = 20;
export const RATIO_ANIM_START = 90;
export const RATIO_ANIM_DUR = 20;
export const PHASE1_HOLD_END = 210;
export const CROSSFADE_START = 210;
export const CROSSFADE_DUR = 60;
export const LEFT_FILL_START = 270;
export const LEFT_FILL_DUR = 30;
export const RIGHT_FILL_START = 330;
export const RIGHT_FILL_DUR = 30;
export const EMPHASIS_START = 390;
export const EMPHASIS_DUR = 15;

// ── Prompt text content (12 lines) ──
export const PROMPT_LINES: string[] = [
  "Generate an injection mold module for",
  "ABS plastic with 2mm wall thickness.",
  "",
  "Requirements:",
  "- Two-plate mold, single cavity",
  "- Side gate at parting line",
  "- Ejector pins at 4 corners",
  "- Cooling channels: 10mm diameter",
  "- Draft angle: 1.5 degrees",
  "",
  "Output: OpenSCAD with parametric",
  "dimensions and assembly comments.",
];

// ── Generated code lines (40 visible, representing ~200) ──
export const CODE_LINES: string[] = [
  "// Auto-generated: injection_mold_abs.scad",
  "// Module: single-cavity two-plate mold",
  "",
  "include <MCAD/units.scad>;",
  "",
  "// ── Parameters ──",
  "wall_thickness   = 2.0;    // mm",
  "draft_angle      = 1.5;    // degrees",
  "gate_type        = \"side\"; // at parting line",
  "cooling_diameter = 10.0;   // mm",
  "ejector_count    = 4;",
  "",
  "module mold_cavity(w, h, d) {",
  "  difference() {",
  "    cube([w + wall_thickness*2,",
  "          h + wall_thickness*2,",
  "          d + wall_thickness], center=true);",
  "    translate([0, 0, wall_thickness/2])",
  "      cube([w, h, d], center=true);",
  "  }",
  "}",
  "",
  "module cooling_channel(len) {",
  "  rotate([90, 0, 0])",
  "    cylinder(h=len, d=cooling_diameter,",
  "             center=true, $fn=32);",
  "}",
  "",
  "module ejector_pin(pos) {",
  "  translate(pos)",
  "    cylinder(h=20, d=3, $fn=16);",
  "}",
  "",
  "module side_gate(w, h) {",
  "  translate([w/2, 0, 0])",
  "    cube([5, 2, h/3], center=true);",
  "}",
  "",
  "// ── Assembly ──",
  "module mold_assembly() {",
  "  // A-plate (cavity side)",
  "  mold_cavity(80, 60, 30);",
  "",
  "  // Cooling system",
  "  for (y = [-20, 20])",
  "    translate([0, y, -10])",
  "      cooling_channel(120);",
  "",
  "  // Ejector pins",
  "  pin_positions = [",
  "    [-30, -20, 0], [30, -20, 0],",
  "    [-30,  20, 0], [30,  20, 0]",
  "  ];",
  "  for (p = pin_positions)",
  "    ejector_pin(p);",
  "}",
  "",
  "// Render",
  "mold_assembly();",
];

// ── Syntax highlight color map ──
export const SYNTAX_COMMENT = "#6A9955";
export const SYNTAX_KEYWORD = "#569CD6";
export const SYNTAX_STRING = "#CE9178";
export const SYNTAX_NUMBER = "#B5CEA8";
export const SYNTAX_FUNCTION = "#DCDCAA";
export const SYNTAX_DEFAULT = "#D4D4D4";

// ── Dense code filler for context window (raw code) ──
export const DENSE_CODE_FILLER = Array.from({ length: 60 }, (_, i) => {
  const templates = [
    "fn process_chunk(&mut self, buf: &[u8]) -> Result<()> {",
    "  let hash = self.hasher.update(buf);",
    "  self.state.push(hash.finalize());",
    "  if self.state.len() > MAX_CHUNKS { self.flush()?; }",
    "  Ok(())",
    "}",
    "impl Iterator for TokenStream {",
    "  type Item = Token;",
    "  fn next(&mut self) -> Option<Self::Item> {",
    "    self.buffer.pop_front()",
    "  }",
    "}",
  ];
  return templates[i % templates.length];
});

// ── Clean prompt filler for context window (prompts) ──
export const CLEAN_PROMPT_FILLER: string[] = [
  "Module 1: Core geometry engine",
  "  - Generate parametric body",
  "  - Apply draft angles to all faces",
  "",
  "Module 2: Gating system",
  "  - Side gate at parting line",
  "  - Runner layout for balanced flow",
  "",
  "Module 3: Cooling system",
  "  - Conformal cooling channels",
  "  - Baffle placement strategy",
  "",
  "Module 4: Ejection system",
  "  - Pin placement and sizing",
  "  - Sleeve ejector for deep cores",
  "",
  "Module 5: Mold base selection",
  "  - Standard base dimensions",
  "  - Plate thickness calculation",
  "",
  "Module 6: Venting design",
  "  - Vent depth and width",
  "  - Parting line vent placement",
  "",
  "Module 7: Surface finish spec",
  "  - SPI classification mapping",
  "  - Texture region definition",
  "",
  "Module 8: Tolerance analysis",
  "  - Shrinkage compensation",
  "  - Dimensional tolerance stack",
  "",
  "Module 9: Assembly sequence",
  "  - Component mating order",
  "  - Fastener specification",
  "",
  "Module 10: Quality validation",
  "  - Fill simulation check",
  "  - Warp and sink analysis",
];
