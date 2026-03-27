import React from 'react';
import {useCurrentFrame, interpolate, Easing} from 'remotion';
import {
	PART_DISSOLVE_START,
	PART_DISSOLVE_END,
	PART_REAPPEAR_START,
	PART_REAPPEAR_END,
} from './constants';

/**
 * Overlay that simulates the plastic part dissolving then reappearing.
 * It works by showing a semi-transparent mask over the lower-right area
 * of the right panel (where the ejected part is), fading it to white/transparent
 * to "dissolve" the part, then bringing it back.
 */
const PartDissolveReappear: React.FC = () => {
	const frame = useCurrentFrame();

	// Dissolve: part fades out (mask opacity goes up) — easeInCubic 30 frames
	const dissolveOpacity = interpolate(
		frame,
		[PART_DISSOLVE_START, PART_DISSOLVE_END],
		[0, 0.92],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.in(Easing.bezier(0.32, 0, 0.67, 0)),
		},
	);

	// Hold dissolved state
	const holdOpacity =
		frame >= PART_DISSOLVE_END && frame < PART_REAPPEAR_START ? 0.92 : 0;

	// Reappear: mask fades back out — easeOutCubic 20 frames
	const reappearOpacity = interpolate(
		frame,
		[PART_REAPPEAR_START, PART_REAPPEAR_END],
		[0.92, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.bezier(0.33, 1, 0.68, 1)),
		},
	);

	let maskOpacity: number;
	if (frame < PART_DISSOLVE_START) {
		maskOpacity = 0;
	} else if (frame < PART_DISSOLVE_END) {
		maskOpacity = dissolveOpacity;
	} else if (frame < PART_REAPPEAR_START) {
		maskOpacity = holdOpacity || 0.92;
	} else if (frame < PART_REAPPEAR_END) {
		maskOpacity = reappearOpacity;
	} else {
		maskOpacity = 0;
	}

	if (maskOpacity <= 0) return null;

	return (
		<div
			style={{
				position: 'absolute',
				bottom: 0,
				left: '15%',
				width: '70%',
				height: '45%',
				background:
					'radial-gradient(ellipse 60% 50% at 50% 60%, rgba(0,0,0,0.95) 0%, transparent 100%)',
				opacity: maskOpacity,
				pointerEvents: 'none',
			}}
		/>
	);
};

export default PartDissolveReappear;
