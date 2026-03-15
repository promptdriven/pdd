export const FPS = 30;

export const CANVAS = {
	width: 1920,
	height: 1080,
	centerX: 960,
	centerY: 540,
} as const;

export const COLORS = {
	backgroundCenter: '#0F172A',
	backgroundEdge: '#020617',
	squareFill: '#6366F1',
	streakColor: '#6366F1',
	streakOpacity: 0.4,
} as const;

export const SHAPE = {
	size: 130,
	borderRadius: 12,
} as const;

export const SLIDE = {
	fromX: 960,
	toX: 1440,
	y: 540,
	anticipationOffset: 20,
	overshoot: 30,
	streakMaxWidth: 280,
	streakHeight: 6,
} as const;

export const TIMING = {
	totalFrames: 30,
	// Phase 1: Anticipation (frames 0-6)
	anticipationEnd: 6,
	// Phase 2: Main slide (frames 6-20)
	slideStart: 6,
	slideEnd: 20,
	// Phase 3: Bounce back (frames 20-26)
	bounceStart: 20,
	bounceEnd: 26,
	// Phase 4: Hold (frames 26-30)
	holdStart: 26,
	holdEnd: 30,
	// Motion streak visible range
	streakAppear: 10,
	streakFade: 18,
} as const;

export const SCALE = {
	anticipationX: 0.97,
	slideStretchX: 1.03,
	normal: 1.0,
} as const;
