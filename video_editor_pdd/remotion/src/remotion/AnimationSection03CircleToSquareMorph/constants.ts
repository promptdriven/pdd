export const CANVAS = {
	width: 1920,
	height: 1080,
	centerX: 960,
	centerY: 540,
} as const;

export const COLORS = {
	backgroundCenter: '#1E293B',
	backgroundEdge: '#0F172A',
	shapeStart: '#3B82F6',
	shapeEnd: '#6366F1',
} as const;

export const SHAPE = {
	size: 120,
	borderRadiusStart: 60, // 50% of 120 = circle
	borderRadiusEnd: 12,
} as const;

export const TIMING = {
	totalFrames: 36,
	// Phase 1: Hold as circle (frames 0-5)
	holdEnd: 6,
	// Phase 2: Morph (frames 6-29)
	morphStart: 6,
	morphEnd: 30,
	// Phase 3: Settle (frames 30-35)
	settleStart: 30,
	settleEnd: 36,
} as const;

export const GHOST = {
	count: 3,
	opacities: [0.15, 0.1, 0.05] as readonly number[],
	frameOffsets: [0, 4, 8] as readonly number[],
} as const;

export const FPS = 30;
