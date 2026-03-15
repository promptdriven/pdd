import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, SHAPE, SLIDE, TIMING } from './constants';
import { getSquareX } from './SlidingSquare';

/**
 * Horizontal motion streak trailing behind the square during peak velocity.
 * 6px tall bar centered on the square's vertical position, with an indigo
 * gradient at 40% opacity fading to transparent on the left.
 * Visible during frames 10-18, fades out with easeOutExpo.
 */
export const MotionStreak: React.FC = () => {
	const frame = useCurrentFrame();

	// Only render during slide and bounce phases
	if (frame < TIMING.streakAppear) return null;
	if (frame > TIMING.bounceEnd) return null;

	const squareX = getSquareX(frame);
	const squareLeftEdge = squareX - SHAPE.size / 2;

	// Velocity-proportional width: peak during mid-slide, taper at edges
	const velocityFactor = interpolate(
		frame,
		[TIMING.streakAppear, 14, TIMING.streakFade],
		[0.3, 1.0, 0.5],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);
	const streakWidth = SLIDE.streakMaxWidth * velocityFactor;

	// Opacity: appears during streak range, fades out after
	const streakOpacity = interpolate(
		frame,
		[TIMING.streakAppear, TIMING.streakAppear + 2, TIMING.streakFade, TIMING.bounceEnd],
		[0, COLORS.streakOpacity, COLORS.streakOpacity, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.poly(4)),
		},
	);

	if (streakOpacity <= 0.01) return null;

	return (
		<div
			style={{
				position: 'absolute',
				left: squareLeftEdge - streakWidth,
				top: SLIDE.y - SLIDE.streakHeight / 2,
				width: streakWidth,
				height: SLIDE.streakHeight,
				background: `linear-gradient(to right, transparent, ${COLORS.streakColor})`,
				opacity: streakOpacity,
				borderRadius: SLIDE.streakHeight / 2,
				pointerEvents: 'none' as const,
			}}
		/>
	);
};
