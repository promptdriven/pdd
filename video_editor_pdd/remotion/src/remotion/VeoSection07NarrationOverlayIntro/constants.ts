// Component-level constants for VeoSection07NarrationOverlayIntro
// Duration: ~0.8s (24 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0B1120',
  overlay: 'rgba(11, 17, 32, 0.5)',
  narrationText: '#FFFFFF',
  waveformBar: 'rgba(79, 195, 247, 0.8)',
  accentUnderline: '#C9A84C',
} as const;

export const TYPOGRAPHY = {
  narration: {
    fontSize: 40,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
    lineHeight: 1.4,
  },
} as const;

// Animation frame ranges (30fps, 24 frames total = ~0.8s)
export const ANIMATION = {
  // Frame 0–4: Background blur + overlay fade in (opacity 0→1)
  bgFadeStart: 0,
  bgFadeEnd: 4,

  // Frame 4–18: Words appear one at a time (~2.8 frames per word, 5 words)
  wordStart: 4,
  framesPerWord: 2.8,
  wordShiftPx: 8,

  // Frame 10–20: Waveform bars begin pulsing (traveling wave)
  waveformStart: 10,
  waveformEnd: 20,

  // Frame 18–22: Accent underline grows from center outward
  underlineStart: 18,
  underlineEnd: 22,

  // Frame 22–24: Hold — all visible, waveform continues subtle pulse
  totalDuration: 24,
} as const;

export const DIMENSIONS = {
  // Narration text block (center, y: 440)
  textY: 440,
  textMaxWidth: 900,

  // Waveform visualizer (center, y: 560)
  waveformY: 560,
  waveformBarCount: 40,
  waveformBarWidth: 4,
  waveformBarGap: 6,
  waveformMinHeight: 10,
  waveformMaxHeight: 40,

  // Accent underline (y: 530)
  underlineY: 530,
  underlineHeight: 2,
  underlineMaxWidth: 580,

  // Background blur radius
  backgroundBlur: 20,
} as const;

export const NARRATION_WORDS = [
  'Veo-generated',
  'clips',
  'with',
  'narration',
  'overlay',
] as const;
