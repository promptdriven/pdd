// Component-level constants for AnimationSection05SplitComparison
// Duration: 30 frames @ 30fps (~1.0s)

export const CANVAS = {
	width: 1920,
	height: 1080,
} as const;

export const COLORS = {
	outerBackground: '#0A1628',
	leftBackground: '#1E3A5F',
	rightBackground: '#312E81',
	circleFill: '#3B82F6',
	squareFill: '#6366F1',
	divider: '#FFFFFF',
	label: '#FFFFFF',
} as const;

export const LAYOUT = {
	panelWidth: 960,
	dividerWidth: 2,
	dividerMaxOpacity: 0.6,
} as const;

export const SHAPES = {
	circleCenterX: 480,
	circleCenterY: 540,
	circleRadius: 50,
	squareCenterX: 480, // relative to right panel
	squareCenterY: 540,
	squareSize: 100,
	squareBorderRadius: 12,
	floatAmplitude: 5,
	floatPeriod: 20,
} as const;

export const TYPOGRAPHY = {
	fontFamily: "'Inter', sans-serif",
	fontSize: 24,
	fontWeight: 600 as const,
	labelOpacity: 0.9,
	labelY: 420,
} as const;

export const TIMING = {
	// Frame 0-12: Slide up from y=1080 to y=0
	slideUpStart: 0,
	slideUpEnd: 12,
	// Frame 8-18: "Before" label fades in
	beforeLabelStart: 8,
	beforeLabelEnd: 18,
	// Frame 12-22: "After" label fades in
	afterLabelStart: 12,
	afterLabelEnd: 22,
	// Frame 15-30: Floating bob begins
	floatStart: 15,
	totalFrames: 30,
} as const;
