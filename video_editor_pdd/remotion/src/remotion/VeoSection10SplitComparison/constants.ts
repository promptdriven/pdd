// Component-level constants for VeoSection10SplitComparison
// Split-screen: Prompt (left) vs. Veo output (right)

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#000000',
  leftPanelBg: '#1E1E2E',
  promptText: '#E2E8F0',
  lineNumber: '#4A5568',
  accent: '#F59E0B',
  cursorColor: '#E2E8F0',
  dividerGradientStart: '#1E1E2E',
  headerText: '#F59E0B',
};

export const TYPOGRAPHY = {
  prompt: {
    fontFamily: 'JetBrains Mono, monospace',
    fontSize: 20,
    lineHeight: 1.6,
  },
  lineNumber: {
    fontFamily: 'JetBrains Mono, monospace',
    fontSize: 14,
  },
  header: {
    fontFamily: 'Inter, sans-serif',
    fontSize: 12,
    fontWeight: 600 as const,
    letterSpacing: '3px',
  },
  arrow: {
    fontFamily: 'Inter, sans-serif',
    fontSize: 32,
    fontWeight: 700 as const,
  },
};

export const DIMENSIONS = {
  panelWidth: 948,
  panelHeight: 1080,
  dividerWidth: 24,
  dividerX: 948,
  rightPanelX: 972,
  promptPadding: 60,
  lineNumberGutterWidth: 50,
};

export const POSITIONS = {
  leftHeaderX: 60,
  leftHeaderY: 40,
  rightHeaderX: 1860,
  rightHeaderY: 40,
  promptBlockY: 400,
  arrowY: 540,
};

export const ANIMATION = {
  // Slide in: frames 0-15
  slideInStart: 0,
  slideInEnd: 15,

  // Typewriter: frames 15-45
  typeStart: 15,
  typeEnd: 45,

  // Arrow fade + pulse: frames 30-40
  arrowFadeStart: 30,
  arrowFadeEnd: 35,
  arrowPulseStart: 30,
  arrowPulseEnd: 40,

  // Hold: frames 40-75

  // Slide out: frames 75-90
  slideOutStart: 75,
  slideOutEnd: 90,

  // Cursor blink
  cursorBlinkRate: 15, // frames per blink cycle

  totalDuration: 90,
};

export const PROMPT_TEXT =
  'A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion';
