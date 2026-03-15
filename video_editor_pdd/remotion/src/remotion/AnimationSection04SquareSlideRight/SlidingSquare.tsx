import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, SHAPE, SLIDE, TIMING, SCALE } from './constants';

/**
 * Computes the square's X position at any given frame, including
 * anticipation pullback, main slide with overshoot, and elastic bounce settle.
 */
export const getSquareX = (frame: number): number => {
	// Phase 1: Anticipation (frames 0-6) — shift left by 20px
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

	// Phase 2: Main slide (frames 6-20) — from 940 to 1470 (overshoot)
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

	// Phase 3: Bounce back (frames 20-26) — from 1470 to 1440
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

	// Phase 4: Hold at destination
	return SLIDE.toX;
};

/**
 * Computes the horizontal scale factor for the square at any given frame.
 * Compresses during anticipation, stretches during slide, returns to normal.
 */
const getSquareScaleX = (frame: number): number => {
	// Phase 1: Anticipation — compress to 0.97x
	if (frame <= TIMING.anticipationEnd) {
		return interpolate(
			frame,
			[0, TIMING.anticipationEnd],
			[SCALE.normal, SCALE.anticipationX],
			{
				extrapolateLeft: 'clamp',
				extrapolateRight: 'clamp',
				easing: Easing.in(Easing.quad),
			},
		);
	}

	// Phase 2: Main slide — stretch to 1.03x then return
	if (frame <= TIMING.slideEnd) {
		const midSlide = TIMING.slideStart + (TIMING.slideEnd - TIMING.slideStart) * 0.4;
		if (frame <= midSlide) {
			return interpolate(
				frame,
				[TIMING.slideStart, midSlide],
				[SCALE.anticipationX, SCALE.slideStretchX],
				{
					extrapolateLeft: 'clamp',
					extrapolateRight: 'clamp',
					easing: Easing.out(Easing.quad),
				},
			);
		}
		return interpolate(
			frame,
			[midSlide, TIMING.slideEnd],
			[SCALE.slideStretchX, SCALE.normal],
			{
				extrapolateLeft: 'clamp',
				extrapolateRight: 'clamp',
				easing: Easing.out(Easing.cubic),
			},
		);
	}

	// Phase 3-4: Return to normal
	if (frame <= TIMING.bounceEnd) {
		return interpolate(
			frame,
			[TIMING.bounceStart, TIMING.bounceEnd],
			[SCALE.normal, SCALE.normal],
			{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
		);
	}

	return SCALE.normal;
};

export const SlidingSquare: React.FC = () => {
	const frame = useCurrentFrame();
	const x = getSquareX(frame);
	const scaleX = getSquareScaleX(frame);

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
				transform: `scaleX(${scaleX})`,
			}}
		/>
	);
};
