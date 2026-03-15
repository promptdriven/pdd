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
	slideOffsetY: 24,
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
	waveHeight: { label: 'Wave Height', value: '0.8m' },
	wavePeriod: { label: 'Wave Period', value: '6.2s' },
	waterTemp: { label: 'Water Temp', value: '22\u00B0C' },
};

export const DEFAULT_BADGE_SLOTS = [
	{ x: 120, y: 680 },
	{ x: 860, y: 680 },
	{ x: 1600, y: 680 },
] as const;

export type WaveBadgeIcon = 'wave' | 'clock' | 'thermometer';

export type ResolvedWaveOverlayBadge = {
	label: string;
	value: string;
	icon: WaveBadgeIcon;
	x: number;
	y: number;
};

const isRecord = (value: unknown): value is Record<string, unknown> =>
	Boolean(value) && typeof value === 'object' && !Array.isArray(value);

const DEFAULT_BADGES: readonly ResolvedWaveOverlayBadge[] = [
	{ ...DEFAULT_BADGE_SLOTS[0], ...DATA.waveHeight, icon: 'wave' },
	{ ...DEFAULT_BADGE_SLOTS[1], ...DATA.wavePeriod, icon: 'clock' },
	{ ...DEFAULT_BADGE_SLOTS[2], ...DATA.waterTemp, icon: 'thermometer' },
] as const;

export const resolveWaveOverlayBadges = (
	dataPoints: Record<string, unknown> | null,
): ResolvedWaveOverlayBadge[] => {
	const stats = Array.isArray(dataPoints?.stats) ? dataPoints.stats : [];

	return DEFAULT_BADGES.map((fallbackBadge, index) => {
		const candidate = stats[index];
		if (!isRecord(candidate)) {
			return { ...fallbackBadge };
		}

		return {
			label:
				typeof candidate.label === 'string' ? candidate.label : fallbackBadge.label,
			value:
				typeof candidate.value === 'string' ? candidate.value : fallbackBadge.value,
			icon:
				candidate.icon === 'wave' || candidate.icon === 'clock' || candidate.icon === 'thermometer'
					? candidate.icon
					: fallbackBadge.icon,
			x: typeof candidate.x === 'number' ? candidate.x : fallbackBadge.x,
			y: typeof candidate.y === 'number' ? candidate.y : fallbackBadge.y,
		};
	});
};
