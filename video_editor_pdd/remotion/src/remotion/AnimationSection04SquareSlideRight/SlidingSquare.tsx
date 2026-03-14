import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, SHAPE, SLIDE, TIMING } from './constants';

/**
 * Computes the square's X position at any given frame, including
 * anticipation, main slide with overshoot, and bounce settle.
 */
export const getSquareX = (frame: number): number => {
	// Phase 1: Anticipation (frames 0-3) — shift left 10px
	if (frame <= TIMING.anticipationEnd) {
		return interpolate(
			frame,
			[0, TIMING.anticipationEnd],
			[SLIDE.fromX, SLIDE.fromX - SLIDE.anticipationOffset],
			{
				extrapolateLeft: 'clamp',
				extrapolateRight: 'clamp',
				easing: Easing.in(Easing.quad),
			},
		);
	}

	// Phase 2: Main slide (frames 3-21) — from 950 to 1460 (overshoot)
	if (frame <= TIMING.slideEnd) {
		return interpolate(
			frame,
			[TIMING.slideStart, TIMING.slideEnd],
			[SLIDE.fromX - SLIDE.anticipationOffset, SLIDE.toX + SLIDE.overshoot],
			{
				extrapolateLeft: 'clamp',
				extrapolateRight: 'clamp',
				easing: Easing.out(Easing.cubic),
			},
		);
	}

	// Phase 3: Bounce back (frames 21-27) — from 1460 to 1440
	if (frame <= TIMING.bounceEnd) {
		return interpolate(
			frame,
			[TIMING.bounceStart, TIMING.bounceEnd],
			[SLIDE.toX + SLIDE.overshoot, SLIDE.toX],
			{
				extrapolateLeft: 'clamp',
				extrapolateRight: 'clamp',
				easing: Easing.inOut(Easing.sin),
			},
		);
	}

	// Phase 4: Settled at destination
	return SLIDE.toX;
};

export const SlidingSquare: React.FC = () => {
	const frame = useCurrentFrame();
	const x = getSquareX(frame);

	return (
		<div
			style={{
				position: 'absolute',
				left: x - SHAPE.size / 2,
				top: SLIDE.y - SHAPE.size / 2,
				width: SHAPE.size,
				height: SHAPE.size,
				backgroundColor: COLORS.squareFill,
				borderRadius: SHAPE.borderRadius,
			}}
		/>
	);
};
