export const FPS = 30;

export const CANVAS = {
	width: 1920,
	height: 1080,
	centerX: 960,
	centerY: 540,
} as const;

export const COLORS = {
	backgroundCenter: '#1E293B',
	backgroundEdge: '#0F172A',
	squareFill: '#6366F1',
	streakColor: 'rgba(99, 102, 241, 0.3)',
} as const;

export const SHAPE = {
	size: 120,
	borderRadius: 12,
} as const;

export const SLIDE = {
	fromX: 960,
	toX: 1440,
	y: 540,
	anticipationOffset: 10,  // shift left 10px during anticipation
	overshoot: 20,           // overshoot past toX by 20px
	streakMaxLength: 200,
} as const;

export const TIMING = {
	totalFrames: 30,
	// Phase 1: Anticipation (frames 0-3)
	anticipationEnd: 3,
	// Phase 2: Main slide (frames 3-21)
	slideStart: 3,
	slideEnd: 21,
	// Phase 3: Bounce back (frames 21-27)
	bounceStart: 21,
	bounceEnd: 27,
	// Phase 4: Settle (frames 27-30)
	settleStart: 27,
	settleEnd: 30,
} as const;
