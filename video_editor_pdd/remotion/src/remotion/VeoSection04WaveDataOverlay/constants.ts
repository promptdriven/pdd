// Component-level constants for VeoSection04WaveDataOverlay
// Duration: ~1.0s (30 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  /** Semi-transparent dark overlay composited over footage */
  overlay: 'rgba(11, 17, 32, 0.6)',
  /** Fallback solid background */
  fallbackBg: '#0B1120',
  /** Waveform stroke */
  waveStroke: '#4FC3F7',
  /** Waveform glow (30% opacity, blur 8px) */
  waveGlow: 'rgba(79, 195, 247, 0.3)',
  /** Waveform fill gradient top */
  waveFillTop: 'rgba(79, 195, 247, 0.2)',
  /** Grid line color (5% white) */
  gridLine: 'rgba(255, 255, 255, 0.05)',
  /** Badge background */
  badgeBg: 'rgba(26, 39, 68, 0.8)',
  /** Badge border */
  badgeBorder: 'rgba(79, 195, 247, 0.4)',
  /** Badge label text (muted silver) */
  badgeLabel: '#A0AEC0',
  /** Badge value text */
  badgeValue: '#FFFFFF',
} as const;

export const TYPOGRAPHY = {
  badgeLabel: {
    fontSize: 14,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
  },
  badgeValue: {
    fontSize: 22,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
  },
} as const;

export const ANIMATION = {
  // Frame 0–8: Dark overlay + grid lines fade in
  overlayFadeStart: 0,
  overlayFadeEnd: 8,
  // Frame 8–22: Waveform draws left-to-right (linear)
  waveDrawStart: 8,
  waveDrawEnd: 22,
  // Frame 8–12: Badge 1 slides in
  badge1Start: 8,
  badge1End: 12,
  // Frame 12–16: Badge 2 slides in
  badge2Start: 12,
  badge2End: 16,
  // Frame 16–20: Badge 3 slides in
  badge3Start: 16,
  badge3End: 20,
  // Frame 22–30: Hold
  totalDuration: 30,
} as const;

/** Waveform chart area in the lower third */
export const WAVEFORM = {
  left: 100,
  right: 1820,
  top: 680,
  bottom: 980,
  strokeWidth: 3,
  glowBlur: 8,
  /** Sine wave parameters from spec */
  amplitude: 0.8,
  frequency: 1.2,
  samples: 120,
} as const;

/** Stat badge definitions — upper-right quadrant */
export const STAT_BADGES = [
  { label: 'Wave Height', value: '0.8m', icon: 'wave' as const },
  { label: 'Period', value: '6.2s', icon: 'clock' as const },
  { label: 'Temperature', value: '22°C', icon: 'thermometer' as const },
] as const;

/** Badge layout — upper-right area y:80–300, x:1400–1840 */
export const BADGE_LAYOUT = {
  x: 1440,
  startY: 80,
  gapY: 76,
  width: 380,
  height: 60,
  borderRadius: 12,
  borderWidth: 1,
  /** Slide-in translateX offset */
  slideOffset: 40,
} as const;

/** Grid lines at 25% vertical intervals across the full canvas */
export const GRID = {
  intervals: [0.25, 0.50, 0.75],
} as const;

export type WaveOverlayLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  waveform: {
    left: number;
    right: number;
    top: number;
    bottom: number;
  };
  badge: {
    x: number;
    width: number;
    height: number;
  };
  typography: {
    badgeLabel: typeof TYPOGRAPHY.badgeLabel & { fontSize: number };
    badgeValue: typeof TYPOGRAPHY.badgeValue & { fontSize: number };
  };
};

export const resolveWaveOverlayLayout = (
  width: number,
  height: number,
): WaveOverlayLayout => {
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  return {
    width,
    height,
    scaleX,
    scaleY,
    uniformScale,
    waveform: {
      left: WAVEFORM.left * scaleX,
      right: WAVEFORM.right * scaleX,
      top: WAVEFORM.top * scaleY,
      bottom: WAVEFORM.bottom * scaleY,
    },
    badge: {
      x: BADGE_LAYOUT.x * scaleX,
      width: BADGE_LAYOUT.width * scaleX,
      height: BADGE_LAYOUT.height * scaleY,
    },
    typography: {
      badgeLabel: {
        ...TYPOGRAPHY.badgeLabel,
        fontSize: Math.max(10, TYPOGRAPHY.badgeLabel.fontSize * uniformScale),
      },
      badgeValue: {
        ...TYPOGRAPHY.badgeValue,
        fontSize: Math.max(14, TYPOGRAPHY.badgeValue.fontSize * uniformScale),
      },
    },
  };
};
