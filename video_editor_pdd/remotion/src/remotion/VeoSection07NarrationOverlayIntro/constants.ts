// Component-level constants for VeoSection07NarrationOverlayIntro
// Duration: ~1.3s (38 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0A1628',
  gradientMesh: ['#0A1628', '#1B3A5C', '#0D4D4D'] as readonly string[],
  waveformBottom: '#4DA8DA',
  waveformTop: '#8EC8E8',
  waveformOpacity: 0.7,
  waveformReflectionOpacity: 0.15,
  activeWord: '#FFFFFF',
  inactiveWord: 'rgba(255,255,255,0.4)',
  badgeBackground: 'rgba(77,168,218,0.2)',
  badgeBorder: '#4DA8DA',
  badgeText: '#8EC8E8',
} as const;

export const TYPOGRAPHY = {
  narration: {
    fontSize: 36,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
    lineHeight: 1.4,
  },
  badge: {
    fontSize: 14,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
  },
} as const;

export const WAVEFORM = {
  barCount: 64,
  xStart: 100,
  xEnd: 1820,
  baselineY: 700,
  bottomY: 980,
  barWidth: 20,
  barGap: 6,
  minHeight: 20,
  maxHeight: 280,
} as const;

export const NARRATION = {
  centerX: 960,
  centerY: 400,
  maxWidth: 1200,
  words: ['It', 'uses', 'Veo-generated', 'clips', 'with', 'narration', 'overlay.'] as readonly string[],
  framesPerWord: 5,
  wordFadeDuration: 3,
} as const;

export const BADGE = {
  x: 1680,
  y: 40,
  paddingX: 16,
  paddingY: 8,
  borderRadius: 20,
  text: 'TTS: Qwen3 — Aiden',
  slideDistance: 40,
} as const;

export const ANIMATION = {
  // Frame 0-6: Gradient mesh fades in, badge slides in
  meshFadeStart: 0,
  meshFadeEnd: 6,
  badgeSlideStart: 0,
  badgeSlideEnd: 6,

  // Frame 6-10: Waveform bars begin animating
  waveformStart: 6,
  waveformRampEnd: 10,

  // Frame 6-34: Words reveal one by one (~1 word per 5 frames)
  wordRevealStart: 6,

  // Frame 34-38: Waveform tails off
  waveformTailStart: 34,
  waveformTailEnd: 38,

  totalDuration: 38,
} as const;
