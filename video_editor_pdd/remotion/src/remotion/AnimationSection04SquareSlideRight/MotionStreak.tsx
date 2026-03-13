import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, SHAPE, SLIDE, TIMING } from './constants';
import { getSquareX } from './SlidingSquare';

/**
 * Horizontal gradient streak trailing the square during the slide.
 * The streak is a bar from the square's trailing edge back up to 200px,
 * fading from the square's color at 30% opacity to transparent.
 * It fades out during the bounce/settle phases.
 */
export const MotionStreak: React.FC = () => {
	const frame = useCurrentFrame();

	// Only show streak during and shortly after the slide
	if (frame < TIMING.slideStart) return null;

	const squareX = getSquareX(frame);
	const squareLeftEdge = squareX - SHAPE.size / 2;

	// How far the square has traveled from its start position
	const traveled = squareX - (SLIDE.fromX - SLIDE.anticipationOffset);
	const streakLength = Math.min(Math.max(traveled, 0), SLIDE.streakMaxLength);

	if (streakLength <= 0) return null;

	// Streak starts at the left edge of the square and extends left
	const streakLeft = squareLeftEdge - streakLength;

	// Streak opacity fades out during bounce and settle (frames 21-30)
	const streakOpacity = interpolate(
		frame,
		[TIMING.bounceStart, TIMING.settleEnd],
		[1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	if (streakOpacity <= 0) return null;

	return (
		<div
			style={{
				position: 'absolute',
				left: streakLeft,
				top: SLIDE.y - SHAPE.size / 2,
				width: streakLength,
				height: SHAPE.size,
				background: `linear-gradient(to right, transparent, ${COLORS.streakColor})`,
				opacity: streakOpacity,
				pointerEvents: 'none' as const,
			}}
		/>
	);
};
