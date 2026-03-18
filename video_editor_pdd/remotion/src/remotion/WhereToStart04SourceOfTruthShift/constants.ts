// constants.ts — Colors, dimensions, timing, and content data

export const CANVAS = {
  width: 1920,
  height: 1080,
  backgroundColor: '#0A0F1A',
} as const;

export const COLORS = {
  // Background & neutral
  deepNavy: '#0A0F1A',
  titleBar: '#1E293B',
  editorBg: '#0F172A',

  // Code block colors
  codeText: '#94A3B8',
  codeFaded: '#64748B',
  codeBorder: '#334155',

  // Prompt / accent blue
  promptBlue: '#4A90D9',
  promptText: '#CBD5E1',

  // Test wall amber
  amber: '#D9944A',

  // Terminal / success
  success: '#5AAA6E',

  // Callout text
  calloutText: '#E2E8F0',
} as const;

// Code block (left panel)
export const CODE_BLOCK = {
  x: 330,
  y: 300,
  width: 300,
  height: 200,
  filename: 'auth_handler.py',
} as const;

// Prompt document (right panel)
export const PROMPT_BLOCK = {
  x: 970,
  y: 270,
  width: 300,
  height: 220,
  filename: 'auth_handler.prompt',
} as const;

// Arrow between panels
export const ARROW = {
  startX: 650,
  endX: 950,
  y: 400,
} as const;

// Terminal
export const TERMINAL = {
  x: 1400,
  y: 900,
  width: 360,
  height: 80,
} as const;

// Test walls
export const TEST_WALLS = [
  { label: 'JWT verify', x: 1040 },
  { label: 'expiry check', x: 1110 },
  { label: 'null safety', x: 1180 },
] as const;

export const TEST_WALL_Y = 540;

// Timing (frames)
export const TIMING = {
  // Phase 1: Both panels visible (0-30)
  initialHold: 30,

  // Phase 2: Code desaturates, prompt glows (30-70)
  desatStart: 30,
  desatDuration: 40,

  // Phase 3: Arrow reverses (70-100)
  arrowReverseStart: 70,
  arrowReverseDuration: 30,

  // Phase 4: Labels + test walls appear (100-120)
  labelsStart: 100,
  labelDuration: 15,
  wallStagger: 5,
  wallDuration: 12,

  // Phase 5: Terminal appears (120-140)
  terminalStart: 120,
  terminalDuration: 10,

  // Phase 6: Callout text (140-180)
  calloutStart: 140,
  calloutDuration: 20,

  totalFrames: 180,
} as const;

// Fake code content for auth_handler.py
export const AUTH_HANDLER_CODE = [
  'import jwt',
  'from datetime import datetime',
  '',
  'class AuthHandler:',
  '    def __init__(self, secret):',
  '        self.secret = secret',
  '        self.algo = "HS256"',
  '',
  '    def verify(self, token):',
  '        try:',
  '            payload = jwt.decode(',
  '                token, self.secret,',
  '                algorithms=[self.algo]',
  '            )',
  '            if payload is None:',
  '                raise ValueError',
  '            exp = payload.get("exp")',
  '            if exp < datetime.now():',
  '                return False',
  '            return payload',
  '        except jwt.InvalidToken:',
  '            return None',
];

// Fake prompt content for auth_handler.prompt
export const PROMPT_CONTENT = [
  'Module: auth_handler',
  '',
  'Purpose: JWT authentication',
  'handler with verification,',
  'expiry checking, and null',
  'safety guarantees.',
  '',
  'Constraints:',
  '- Verify JWT signature',
  '- Check token expiry',
  '- Handle null payloads',
  '- Return structured errors',
];
