import React from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	CANVAS_WIDTH,
	CANVAS_HEIGHT,
	RULE_COLOR,
	RULE_MAX_OPACITY,
	RULE_WIDTH,
	RULE_HEIGHT,
	RULE_FADE_IN_START,
	RULE_FADE_IN_END,
	RULE_FADE_OUT_START,
	RULE_FADE_OUT_END,
} from './constants';

/**
 * A thin horizontal rule that fades in and out at center screen.
 * Appears at frame 15, fully visible at frame 30, fades out by frame 45.
 */
export const HorizontalRule: React.FC = () => {
	const frame = useCurrentFrame();

	// Fade in: frames 15-30, easeOut(quad)
	const fadeIn = interpolate(frame, [RULE_FADE_IN_START, RULE_FADE_IN_END], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// Fade out: frames 30-45, easeIn(quad)
	const fadeOut = interpolate(frame, [RULE_FADE_OUT_START, RULE_FADE_OUT_END], [1, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.in(Easing.quad),
	});

	// Combined opacity: multiply fade-in × fade-out × max opacity
	const opacity = fadeIn * fadeOut * RULE_MAX_OPACITY;

	return (
		<div
			style={{
				position: 'absolute',
				top: CANVAS_HEIGHT / 2,
				left: (CANVAS_WIDTH - RULE_WIDTH) / 2,
				width: RULE_WIDTH,
				height: RULE_HEIGHT,
				backgroundColor: RULE_COLOR,
				opacity,
			}}
		/>
	);
};

export default HorizontalRule;
