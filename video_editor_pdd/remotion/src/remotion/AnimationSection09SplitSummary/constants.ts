// AnimationSection09SplitSummary – visual constants

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: '#020617',
} as const;

export const DIVIDER = {
  startX: 640,
  endX: 720,
  width: 6,
  color: '#38BDF8',
} as const;

export const PANELS = {
  left: { background: '#0F172A', label: 'Before' },
  right: { background: '#111827', label: 'After' },
} as const;

export const COLORS = {
  text: '#E2E8F0',
} as const;

export const TYPOGRAPHY = {
  panelLabel: { fontSize: 46, fontWeight: 700 as const },
  title: { fontSize: 54, fontWeight: 700 as const },
} as const;

export const INTRINSIC_FRAMES = 90;
