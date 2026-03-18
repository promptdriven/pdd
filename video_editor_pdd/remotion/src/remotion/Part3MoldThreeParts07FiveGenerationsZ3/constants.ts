// constants.ts — Part3MoldThreeParts07FiveGenerationsZ3

export const DURATION_FRAMES = 540;
export const FPS = 30;

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';
export const BG_DARK = '#080C16';
export const DOT_GRID_SPACING = 30;
export const DOT_GRID_COLOR = '#1E293B';
export const DOT_GRID_OPACITY = 0.03;

// Panel layout
export const PANEL_COUNT = 5;
export const PANEL_WIDTH = 300;
export const PANEL_HEIGHT = 500;
export const PANEL_GAP = 20;
export const PANEL_Y = 180;
export const PANEL_X_STARTS = [110, 430, 750, 1070, 1390];
export const PANEL_BG = '#1E293B';
export const PANEL_BORDER = '#334155';
export const PANEL_TITLE_BG = '#0F172A';
export const PANEL_TITLE_HEIGHT = 30;

// Syntax highlighting colors
export const SYN_KEYWORD = '#C792EA';
export const SYN_STRING = '#C3E88D';
export const SYN_FUNCTION = '#82AAFF';
export const SYN_COMMENT = '#546E7A';
export const SYN_DEFAULT = '#D4D4D4';

// Test result colors
export const COLOR_FAIL = '#EF4444';
export const COLOR_WARN = '#D9944A';
export const COLOR_PASS = '#5AAA6E';

// Typography
export const FONT_MONO = 'JetBrains Mono, Fira Code, monospace';
export const FONT_SANS = 'Inter, system-ui, sans-serif';

// Text colors
export const TEXT_PRIMARY = '#E2E8F0';
export const TEXT_SECONDARY = '#64748B';
export const TEXT_MUTED = '#94A3B8';
export const COLOR_PURPLE = '#C792EA';
export const COLOR_BLUE = '#82AAFF';
export const COLOR_AMBER = '#D9944A';

// Animation keyframes
export const BEAT1_START = 0;
export const BEAT1_END = 300;
export const PANELS_APPEAR_START = 0;
export const PANELS_APPEAR_END = 30;
export const CODE_TYPE_START = 30;
export const CODE_TYPE_END = 120;
export const TEST_RESULTS_START = 120;
export const TEST_RESULTS_END = 180;
export const WINNER_HIGHLIGHT_START = 180;
export const WINNER_HIGHLIGHT_END = 240;
export const CAPTION_START = 240;
export const CAPTION_END = 300;

export const BEAT2_START = 300;
export const BEAT2_END = 540;
export const DISSOLVE_START = 300;
export const DISSOLVE_END = 330;
export const LOGOS_START = 330;
export const LOGOS_END = 390;
export const PROOF_START = 390;
export const PROOF_END = 450;
export const STAMP_START = 450;
export const STAMP_END = 480;
export const ANNOTATION_START = 480;
export const ANNOTATION_END = 540;

// Code variants for the five panels
export const CODE_VARIANTS: string[][] = [
  // Panel 1 — v1
  [
    '# user_parser_v1.py',
    'def parse_user(raw: str):',
    '    parts = raw.split(",")',
    '    uid = int(parts[0])',
    '    name = parts[1].strip()',
    '    email = parts[2].strip()',
    '    return {"id": uid,',
    '            "name": name,',
    '            "email": email}',
  ],
  // Panel 2 — v2
  [
    '# user_parser_v2.py',
    'import re',
    'def parse_user(text: str):',
    '    m = re.match(',
    '        r"(\\d+),(.+),(.+)"',
    '        , text)',
    '    if m:',
    '        return {"id": int(m[1]),',
    '          "name": m[2], "email": m[3]}',
  ],
  // Panel 3 — v3 (winner)
  [
    '# user_parser_v3.py',
    'from typing import Optional',
    'def parse_user(raw: str)',
    '    -> Optional[dict]:',
    '    parts = raw.split(",", 2)',
    '    if len(parts) != 3:',
    '        return None',
    '    uid, name, email = parts',
    '    if not uid.isdigit():',
    '        return None',
    '    return {"id": int(uid),',
    '     "name": name.strip(),',
    '     "email": email.strip()}',
  ],
  // Panel 4 — v4
  [
    '# user_parser_v4.py',
    'def parse_user(data: str):',
    '    tokens = data.split(",")',
    '    user = {}',
    '    user["id"] = int(tokens[0])',
    '    user["name"] = tokens[1]',
    '    user["email"] = tokens[2]',
    '    return user',
  ],
  // Panel 5 — v5
  [
    '# user_parser_v5.py',
    'class UserParser:',
    '  def parse(self, s: str):',
    '    fields = s.split(",")',
    '    return {',
    '      "id": int(fields[0]),',
    '      "name": fields[1].strip(),',
    '      "email": fields[2].strip(),',
    '    }',
  ],
];

export type TestResultType = 'fail' | 'warning' | 'pass';

export interface TestResult {
  type: TestResultType;
  label: string;
  symbol: string;
}

export const TEST_RESULTS: TestResult[] = [
  { type: 'fail', label: '2 tests failed', symbol: '✗' },
  { type: 'warning', label: 'Performance warning', symbol: '△' },
  { type: 'pass', label: 'All 12 tests pass ✓', symbol: '✓' },
  { type: 'fail', label: 'Null handling error', symbol: '✗' },
  { type: 'warning', label: 'Style violations', symbol: '△' },
];

export const WINNER_INDEX = 2;

// Proof section data
export const PROOF_LINES = [
  { text: '∀ input ∈ String:', color: COLOR_PURPLE, size: 24 },
  { text: 'parse(input) ∈ {Valid(id), None}', color: COLOR_BLUE, size: 20 },
];

export const PROOF_STEPS = [
  'Exhaustive enumeration over input alphabet',
  'Branch coverage: 100% path exploration',
  'Satisfiability: UNSAT (no counterexample)',
];
