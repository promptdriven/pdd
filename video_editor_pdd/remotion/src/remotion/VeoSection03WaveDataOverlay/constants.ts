// VeoSection03WaveDataOverlay constants

export const BASE_CANVAS = {
	width: 1920,
	height: 1080,
};

export const COLORS = {
	background: '#0B1D3A',
	backgroundOpacity: 0.85,
	waveStroke: '#5B9BD5',
	accentDot: '#5B9BD5',
	filmReelIcon: '#E8967A',
	sparkleIcon: '#D4A843',
	labelText: '#FFFFFF',
};

export const WAVE = {
	amplitude: 40,
	wavelength: 200,
	strokeWidth: 3,
	centerY: 540,
};

export const DOTS = {
	radius: 6,
	positions: [480, 960, 1440],
};

export const TYPOGRAPHY = {
	labelFontSize: 28,
	labelFontFamily: 'Inter, sans-serif',
	labelFontWeight: 500 as const,
	iconSize: 24,
};

export const STAT_CALLOUTS = [
	{ icon: 'film-reel' as const, label: 'Cinematic Footage', color: '#E8967A', y: 700 },
	{ icon: 'sparkle' as const, label: 'AI-Generated', color: '#D4A843', y: 760 },
];

export const STAT_X = 300;

export const ANIMATION_TIMING = {
	// Phase 1: Sine wave draws left-to-right (frames 0-45)
	waveDrawStart: 0,
	waveDrawEnd: 45,

	// Phase 2: Accent dots scale in (frames 30-45)
	dotsScaleStart: 30,
	dotsScaleEnd: 45,

	// Phase 3: Stat callout 1 fades in (frames 45-75)
	stat1FadeStart: 45,
	stat1FadeEnd: 75,

	// Phase 4: Stat callout 2 fades in (frames 60-90)
	stat2FadeStart: 60,
	stat2FadeEnd: 90,

	// Phase 5: Hold then fade out (frames 90-120)
	fadeOutStart: 105,
	fadeOutEnd: 120,

	totalDuration: 120,
};

export interface WaveDataOverlayLayout {
	width: number;
	height: number;
	wave: {
		amplitude: number;
		wavelength: number;
		strokeWidth: number;
		centerY: number;
	};
	dots: {
		radius: number;
		positions: number[];
	};
	typography: {
		labelFontSize: number;
		labelFontFamily: string;
		labelFontWeight: typeof TYPOGRAPHY.labelFontWeight;
		iconSize: number;
	};
	statCallouts: Array<(typeof STAT_CALLOUTS)[number] & { y: number }>;
	statX: number;
}

export const resolveWaveDataOverlayLayout = (
	width: number,
	height: number
): WaveDataOverlayLayout => {
	const scaleX = width / BASE_CANVAS.width;
	const scaleY = height / BASE_CANVAS.height;
	const uniformScale = Math.min(scaleX, scaleY);

	return {
		width,
		height,
		wave: {
			amplitude: WAVE.amplitude * scaleY,
			wavelength: WAVE.wavelength * scaleX,
			strokeWidth: Math.max(2, WAVE.strokeWidth * uniformScale),
			centerY: WAVE.centerY * scaleY,
		},
		dots: {
			radius: Math.max(4, DOTS.radius * uniformScale),
			positions: DOTS.positions.map((position) => position * scaleX),
		},
		typography: {
			labelFontSize: Math.max(18, TYPOGRAPHY.labelFontSize * uniformScale),
			labelFontFamily: TYPOGRAPHY.labelFontFamily,
			labelFontWeight: TYPOGRAPHY.labelFontWeight,
			iconSize: Math.max(16, TYPOGRAPHY.iconSize * uniformScale),
		},
		statCallouts: STAT_CALLOUTS.map((callout) => ({
			...callout,
			y: callout.y * scaleY,
		})),
		statX: STAT_X * scaleX,
	};
};
