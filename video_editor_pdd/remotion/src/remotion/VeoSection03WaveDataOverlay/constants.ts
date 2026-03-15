// VeoSection03WaveDataOverlay constants

export const BASE_CANVAS = {
	width: 1920,
	height: 1080,
};

export const COLORS = {
	background: '#0A1628',
	goldAccent: '#C9A84C',
	waveStroke: '#C9A84C',
	waveFill: 'rgba(201, 168, 76, 0.15)',
	gridLine: 'rgba(255, 255, 255, 0.08)',
	badgeBackground: 'rgba(11, 17, 32, 0.85)',
	badgeBorder: 'rgba(201, 168, 76, 0.4)',
	labelText: 'rgba(255, 255, 255, 0.6)',
	valueText: '#FFFFFF',
};

export const WAVEFORM = {
	amplitude: 0.8,
	frequency: 1.2,
	samples: 120,
	strokeWidth: 2,
	yStart: 720,
	yEnd: 980,
};

export const BADGE = {
	width: 200,
	height: 60,
	borderRadius: 8,
	rightOffset: 60,
	topStart: 120,
	gap: 16,
};

export const TYPOGRAPHY = {
	labelFontSize: 12,
	labelFontFamily: "'Inter', sans-serif",
	labelFontWeight: 500 as const,
	valueFontSize: 22,
	valueFontWeight: 700 as const,
};

export const ANIMATION = {
	// Phase 1: Dark overlay fade (frames 0-8)
	overlayFadeStart: 0,
	overlayFadeEnd: 8,

	// Phase 2: Waveform draws left-to-right (frames 4-30)
	waveDrawStart: 4,
	waveDrawEnd: 30,

	// Phase 3-5: Stat badges stagger in (6 frames each)
	badge1Start: 8,
	badge1End: 14,
	badge2Start: 12,
	badge2End: 18,
	badge3Start: 16,
	badge3End: 22,

	// Phase 6: Waveform oscillation (frames 22+)
	oscillationStart: 22,

	totalDuration: 52,
};

export const GRID_ROWS = 4;

export const DATA = {
	waveHeight: { label: 'Wave Height', value: '0.8 m' },
	wavePeriod: { label: 'Wave Period', value: '6.2 s' },
	waterTemp: { label: 'Water Temp', value: '22\u00B0C' },
};
