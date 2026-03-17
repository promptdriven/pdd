// constants.ts — Colors, dimensions, code variants, and test results

export const COLORS = {
  bg: '#0A0F1A',
  bgDarker: '#080C16',
  gridDot: '#1E293B',
  panelBg: '#1E293B',
  panelBorder: '#334155',
  panelTitleBar: '#0F172A',
  // Syntax highlighting
  keyword: '#C792EA',
  string: '#C3E88D',
  func: '#82AAFF',
  comment: '#546E7A',
  // Test results
  fail: '#EF4444',
  warning: '#D9944A',
  pass: '#5AAA6E',
  // Text
  textPrimary: '#E2E8F0',
  textSecondary: '#94A3B8',
  textMuted: '#64748B',
  textAccent: '#D9944A',
  // Proof
  proofPurple: '#C792EA',
  proofBlue: '#82AAFF',
} as const;

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const PANEL = {
  width: 300,
  height: 500,
  gap: 20,
  startX: 110,
  startY: 180,
  titleBarHeight: 30,
  borderRadius: 6,
} as const;

export const PANEL_POSITIONS = [0, 1, 2, 3, 4].map((i) => ({
  x: PANEL.startX + i * (PANEL.width + PANEL.gap),
  y: PANEL.startY,
}));

export interface TestResult {
  type: 'fail' | 'warning' | 'pass';
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

// Simplified code variants for each panel
export const CODE_VARIANTS: string[] = [
  `def parse_user(input):
    # Version 1: basic split
    parts = input.split(",")
    if len(parts) < 2:
        return None
    uid = parts[0].strip()
    name = parts[1].strip()
    if not uid.isdigit():
        return None
    return Valid(
        id=int(uid),
        name=name
    )`,

  `def parse_user(raw):
    # Version 2: regex approach
    import re
    match = re.match(
        r"(\\d+),\\s*(.+)", raw
    )
    if not match:
        return None
    return Valid(
        id=int(match.group(1)),
        name=match.group(2)
    )`,

  `def parse_user(data):
    # Version 3: robust parser
    if not data or "," not in data:
        return None
    idx = data.index(",")
    raw_id = data[:idx].strip()
    name = data[idx+1:].strip()
    try:
        uid = int(raw_id)
    except ValueError:
        return None
    if not name:
        return None
    return Valid(id=uid, name=name)`,

  `def parse_user(text):
    # Version 4: json-style
    try:
        parts = text.split(",")
        uid = int(parts[0])
        name = parts[1]
        return Valid(
            id=uid,
            name=name.strip()
        )
    except:
        return None`,

  `def parse_user(s):
    # Version 5: functional
    tokens = [
        t.strip() for t in
        s.split(",", 1)
    ]
    if len(tokens) != 2:
        return None
    id_str, name = tokens
    return (
        Valid(id=int(id_str),
              name=name)
        if id_str.isdigit()
        else None
    )`,
];

// Frame timing constants
export const TIMING = {
  // Beat 1
  panelStagger: 5,
  panelAppearDuration: 12,
  codeTypeStart: 30,
  codeTypeEnd: 120,
  testResultStart: 120,
  testResultEnd: 180,
  winnerHighlightStart: 180,
  winnerHighlightEnd: 240,
  captionStart: 240,
  beat1End: 300,
  // Beat 2
  beat2Start: 300,
  crossDissolveDuration: 30,
  logoStart: 330,
  proofLine1Start: 360,
  proofLine2Start: 390,
  proofStepsStart: 410,
  stampStart: 450,
  annotationStart: 480,
  totalFrames: 540,
} as const;
