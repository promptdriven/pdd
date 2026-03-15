export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0A1628',
  panelBg: 'rgba(11, 17, 32, 0.75)',
  gold: '#C9A84C',
  captionText: '#FFFFFF',
  wordHighlight: '#C9A84C',
} as const;

export const TYPOGRAPHY = {
  caption: {
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
    fontSize: 32,
    lineHeight: 1.5,
  },
} as const;

export const PANEL = {
  height: 200,
  borderTopWidth: 2,
  padding: 40,
} as const;

export const WAVEFORM = {
  barCount: 5,
  barWidth: 4,
  barGap: 6,
  minHeight: 12,
  maxHeight: 36,
  left: 40,
  bottom: 24,
} as const;

// Animation frame ranges (30fps, 51 frames total ≈ 1.7s)
export const ANIMATION = {
  // Frame 0–8: Panel slides up from y=1080 to y=880
  panelSlideStart: 0,
  panelSlideEnd: 8,

  // Frame 8–10: Gold accent line fades in; waveform begins
  accentFadeStart: 8,
  accentFadeEnd: 10,
  waveformStart: 8,

  // Frame 10–40: Caption words type in (word_timing_frames from spec)
  captionStart: 10,

  // Frame 40–51: Hold — all visible
  totalDuration: 51,
} as const;

export const DATA = {
  caption: 'It uses Veo-generated clips with narration overlay.',
  words: ['It', 'uses', 'Veo-generated', 'clips', 'with', 'narration', 'overlay.'] as const,
  // Frame at which each word begins to appear (relative to composition start)
  wordTimingFrames: [10, 17, 24, 31, 38, 45, 52] as const,
  wordFadeDuration: 3,
} as const;
