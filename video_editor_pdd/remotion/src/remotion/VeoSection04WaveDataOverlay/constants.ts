// Component-level constants for VeoSection04WaveDataOverlay
// Duration: ~1.3s (38 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'rgba(10, 22, 40, 0.7)',
  chartLine: '#4DA8DA',
  chartFill: 'rgba(77, 168, 218, 0.3)',
  gridLine: 'rgba(255, 255, 255, 0.08)',
  badgeBg: 'rgba(77, 168, 218, 0.2)',
  badgeBorder: '#4DA8DA',
  titleText: '#FFFFFF',
  axisLabel: 'rgba(255, 255, 255, 0.5)',
  badgeValue: '#FFFFFF',
  badgeLabel: '#8EC8E8',
} as const;

export const TYPOGRAPHY = {
  chartTitle: {
    fontSize: 28,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
    letterSpacing: 6,
  },
  axisLabel: {
    fontSize: 14,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
  },
  badgeValue: {
    fontSize: 18,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 600 as const,
  },
  badgeLabel: {
    fontSize: 14,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
  },
} as const;

export const ANIMATION = {
  // Frame 0-8: Background, grid lines draw, axes appear
  gridDrawStart: 0,
  gridDrawEnd: 8,
  // Frame 8-28: Sine wave draws from left to right
  waveDrawStart: 8,
  waveDrawEnd: 28,
  // Frame 20-34: Stat callout badges pop in (staggered by 4 frames)
  badgeStartFrame: 20,
  badgeStagger: 4,
  badgeFadeDuration: 6,
  // Total
  totalDuration: 38,
} as const;

export const CHART = {
  // Chart area bounds
  left: 160,
  right: 1860,
  top: 200,
  bottom: 700,
  // Axis ranges
  xMin: 0,
  xMax: 10,
  yMin: -1.5,
  yMax: 1.5,
  // Grid rows (y positions in data space)
  gridYValues: [-1.0, -0.5, 0.0, 0.5, 1.0],
  // X-axis label interval
  xLabelStep: 2,
  // Y-axis label interval
  yLabelStep: 0.5,
  // Line style
  strokeWidth: 3,
} as const;

export const WAVE_DATA = [
  { time: 0, height: 0.0 },
  { time: 1, height: 0.9 },
  { time: 2, height: 1.2 },
  { time: 3, height: 0.8 },
  { time: 4, height: -0.3 },
  { time: 5, height: -1.0 },
  { time: 6, height: -1.2 },
  { time: 7, height: -0.6 },
  { time: 8, height: 0.4 },
  { time: 9, height: 1.1 },
  { time: 10, height: 1.2 },
] as const;

export const STAT_BADGES = [
  { label: 'Wave Height', value: '1.2m', x: 1400, y: 200 },
  { label: 'Period', value: '8.4s', x: 1500, y: 320 },
  { label: 'Water Temp', value: '22°C', x: 1450, y: 440 },
] as const;

export const DIMENSIONS = {
  titleX: 80,
  titleY: 80,
  badgePaddingX: 20,
  badgePaddingY: 12,
  badgeBorderRadius: 8,
  badgeBorderWidth: 1,
} as const;

export type WaveOverlayLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  chart: {
    left: number;
    right: number;
    top: number;
    bottom: number;
  };
  typography: {
    chartTitle: typeof TYPOGRAPHY.chartTitle;
    axisLabel: typeof TYPOGRAPHY.axisLabel;
    badgeValue: typeof TYPOGRAPHY.badgeValue;
    badgeLabel: typeof TYPOGRAPHY.badgeLabel;
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
    chart: {
      left: CHART.left * scaleX,
      right: CHART.right * scaleX,
      top: CHART.top * scaleY,
      bottom: CHART.bottom * scaleY,
    },
    typography: {
      chartTitle: {
        ...TYPOGRAPHY.chartTitle,
        fontSize: Math.max(16, TYPOGRAPHY.chartTitle.fontSize * uniformScale),
        letterSpacing: TYPOGRAPHY.chartTitle.letterSpacing * uniformScale,
      },
      axisLabel: {
        ...TYPOGRAPHY.axisLabel,
        fontSize: Math.max(10, TYPOGRAPHY.axisLabel.fontSize * uniformScale),
      },
      badgeValue: {
        ...TYPOGRAPHY.badgeValue,
        fontSize: Math.max(12, TYPOGRAPHY.badgeValue.fontSize * uniformScale),
      },
      badgeLabel: {
        ...TYPOGRAPHY.badgeLabel,
        fontSize: Math.max(10, TYPOGRAPHY.badgeLabel.fontSize * uniformScale),
      },
    },
  };
};
