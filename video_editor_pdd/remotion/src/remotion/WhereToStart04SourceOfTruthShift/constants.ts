// constants.ts — Colors, dimensions, timing, and inline content data

export const CANVAS = {
  width: 1920,
  height: 1080,
  backgroundColor: '#0A0F1A',
} as const;

export const COLORS = {
  // Code block
  codeTextInitial: '#94A3B8',
  codeTextFinal: '#64748B',
  codeBorder: '#334155',
  artifactLabel: '#64748B',

  // Prompt document
  promptText: '#CBD5E1',
  promptGlow: '#4A90D9',
  promptBorder: '#4A90D9',
  sourceLabel: '#4A90D9',

  // Arrow
  arrow: '#4A90D9',

  // Test walls
  wallColor: '#D9944A',

  // Terminal
  terminalSuccess: '#5AAA6E',
  terminalText: '#94A3B8',

  // Callout
  calloutText: '#E2E8F0',
  calloutHighlight: '#4A90D9',

  // Editor chrome
  titleBar: '#1E293B',
  editorBg: '#0F172A',
  titleBarText: '#94A3B8',
  titleBarDots: ['#EF4444', '#F59E0B', '#22C55E'],
} as const;

export const TIMING = {
  // Phase 1: Both panels visible (0-30)
  phaseOneEnd: 30,

  // Phase 2: Code desaturates, prompt glows (30-70)
  desaturationStart: 30,
  desaturationDuration: 40,

  // Phase 3: Arrow reverses (70-100)
  arrowReverseStart: 70,
  arrowReverseDuration: 30,

  // Phase 4: Labels and test walls (100-120)
  labelsStart: 100,
  labelFadeDuration: 15,
  wallStagger: 5,
  wallScaleDuration: 12,

  // Phase 5: Terminal (120-140)
  terminalStart: 120,
  terminalFadeDuration: 10,

  // Phase 6: Callout (140-180)
  calloutStart: 140,
  calloutFadeDuration: 20,

  totalFrames: 180,
} as const;

export const LAYOUT = {
  codeBlock: { x: 330, y: 300, width: 300, height: 200 },
  promptDoc: { x: 970, y: 270, width: 300, height: 220 },
  arrowFrom: { x: 640, y: 400 },
  arrowTo: { x: 960, y: 400 },
  artifactLabel: { x: 480, y: 520 },
  sourceLabel: { x: 1120, y: 510 },
  walls: [
    { x: 1040, y: 540 },
    { x: 1100, y: 540 },
    { x: 1160, y: 540 },
  ],
  wallLabels: ['JWT verify', 'expiry check', 'null safety'],
  terminal: { x: 1400, y: 900, width: 360, height: 80 },
  callout: { x: 960, y: 880 },
} as const;

// Inline code content for auth_handler.py
export const AUTH_HANDLER_CODE = [
  'import jwt',
  'from datetime import datetime',
  '',
  'def verify_token(token: str):',
  '    try:',
  '        payload = jwt.decode(',
  '            token, SECRET_KEY,',
  '            algorithms=["HS256"]',
  '        )',
  '        if payload["exp"] < now():',
  '            raise ExpiredToken()',
  '        return payload["sub"]',
  '    except jwt.InvalidToken:',
  '        raise AuthError("invalid")',
  '    return None',
];

// Inline prompt content for auth_handler.prompt
export const AUTH_PROMPT_CONTENT = [
  '# Auth Handler Specification',
  '',
  'Verify JWT tokens using HS256.',
  'Check expiration timestamp.',
  'Return subject claim on success.',
  '',
  '## Constraints',
  '- Reject expired tokens',
  '- Reject malformed tokens',
  '- Handle null token input',
  '- Return clear error types',
  '- Use constant-time compare',
];
