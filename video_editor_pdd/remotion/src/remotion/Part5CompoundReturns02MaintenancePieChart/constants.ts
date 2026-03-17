// Colors
export const COLORS = {
	background: '#0F172A',
	initialDev: '#4A90D9',
	maintenance: '#D9944A',
	segmentBorder: '#1E293B',
	centerText: '#64748B',
	calloutBg: '#1E293B',
	calloutBorder: '#334155',
	calloutMain: '#E2E8F0',
	calloutSub: '#94A3B8',
	calloutSource: '#64748B',
} as const;

// Chart dimensions
export const CHART = {
	centerX: 960,
	centerY: 500,
	outerRadius: 220,
	innerRadius: 120,
} as const;

// Segment angles (degrees, starting from 12 o'clock / -90deg offset)
// Using midpoint: Initial Dev = 15% (54deg), Maintenance = 85% (306deg)
export const SEGMENTS = {
	initialDev: {
		startAngle: 0,
		endAngle: 54,
		label: 'Initial Development',
		value: '10-20%',
		color: COLORS.initialDev,
		valueSize: 20,
	},
	maintenance: {
		startAngle: 54,
		endAngle: 360,
		label: 'Maintenance',
		value: '80-90%',
		color: COLORS.maintenance,
		valueSize: 28,
	},
} as const;

// Callout card positions and data
export const CALLOUTS = {
	mckinsey: {
		x: 1400,
		y: 380,
		width: 320,
		height: 100,
		mainText: '+40% maintenance cost',
		subText: 'with high technical debt',
		source: 'McKinsey Digital, 2024',
		iconType: 'bar_chart' as const,
	},
	stripe: {
		x: 1400,
		y: 520,
		width: 320,
		height: 100,
		mainText: '33% of work week',
		subText: 'spent on technical debt',
		source: 'Stripe Developer Coefficient, 2018',
		iconType: 'clock' as const,
	},
} as const;

// Animation frame timings
export const TIMING = {
	// Phase 1: Ring outline + center text fade in
	ringFadeStart: 0,
	ringFadeDuration: 20,

	// Phase 2: Blue segment draws
	blueSegmentStart: 30,
	blueSegmentDuration: 30,

	// Phase 3: Amber segment draws
	amberSegmentStart: 60,
	amberSegmentDuration: 90,

	// Phase 4: Value emphasis
	valueEmphasisDelay: 15, // after segment finishes
	valueEmphasisDuration: 15,

	// Phase 5: McKinsey callout
	mckinseyStart: 210,
	calloutSlideDuration: 25,
	calloutPulseDelay: 25,
	calloutPulseDuration: 20,

	// Phase 6: Stripe callout
	stripeStart: 270,

	// Total
	totalFrames: 420,
} as const;
