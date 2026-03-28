import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
	RULE_COLOR,
	RULE_MAX_OPACITY,
	RULE_WIDTH,
	RULE_HEIGHT,
	RULE_FADE_IN_START,
	RULE_FADE_IN_DURATION,
	RULE_FADE_OUT_START,
	RULE_FADE_OUT_DURATION,
} from './constants';

/**
 * A thin horizontal rule that fades in and out at center screen.
 * Appears at frame 15, fully visible by frame 30, fades out from frame 45-60.
 */
export const HorizontalRule: React.FC = () => {
	const frame = useCurrentFrame();

	// Fade in: frames 15-30, easeOut(quad)
	const fadeIn = interpolate(
		frame,
		[RULE_FADE_IN_START, RULE_FADE_IN_START + RULE_FADE_IN_DURATION],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		}
	);

	// Fade out: frames 45-60, easeIn(quad)
	const fadeOut = interpolate(
		frame,
		[RULE_FADE_OUT_START, RULE_FADE_OUT_START + RULE_FADE_OUT_DURATION],
		[1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.in(Easing.quad),
		}
	);

	// Combined opacity: multiply base max opacity by fade-in and fade-out
	const opacity = RULE_MAX_OPACITY * fadeIn * fadeOut;

	return (
		<div
			style={{
				position: 'absolute',
				top: '50%',
				left: '50%',
				transform: 'translate(-50%, -50%)',
				width: RULE_WIDTH,
				height: RULE_HEIGHT,
				backgroundColor: RULE_COLOR,
				opacity,
			}}
		/>
	);
};

export default HorizontalRule;
