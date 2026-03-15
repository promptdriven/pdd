// Component-level constants for AnimationSection03CircleToSquareMorph

export const CANVAS = {
	width: 1920,
	height: 1080,
	centerX: 960,
	centerY: 540,
} as const;

export const COLORS = {
	backgroundCenter: '#0F172A',
	backgroundEdge: '#020617',
	shapeStart: '#3B82F6',
	shapeEnd: '#6366F1',
} as const;

export const SHAPE = {
	startSize: 120,
	endSize: 130,
	borderRadiusStart: 60,
	borderRadiusEnd: 12,
} as const;

export const TIMING = {
	totalFrames: 36,
	// Phase 1: Hold as circle (frames 0-5)
	holdEnd: 6,
	// Phase 2: Morph (frames 6-29)
	morphStart: 6,
	morphEnd: 30,
	// Phase 3: Settle / ghost fade-out (frames 30-35)
	settleStart: 30,
	settleEnd: 36,
} as const;

export const GHOST = {
	opacities: [0.6, 0.35, 0.15] as readonly number[],
	lagFrames: 3,
} as const;
