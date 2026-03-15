import React from 'react';
import {
	useCurrentFrame,
	interpolate,
	interpolateColors,
	Easing,
} from 'remotion';
import { CANVAS, COLORS, SHAPE, TIMING } from './constants';

/**
 * Primary morphing shape: centered element that transitions from a blue circle
 * (border-radius 60px) to an indigo rounded square (border-radius 12px),
 * with size growth from 120→130px.
 */
export const MorphShape: React.FC = () => {
	const frame = useCurrentFrame();

	// Border radius: 60px (circle) → 12px (rounded square), easeInOutCubic
	const borderRadius = interpolate(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[SHAPE.borderRadiusStart, SHAPE.borderRadiusEnd],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);

	// Fill color: #3B82F6 → #6366F1, linear
	const fillColor = interpolateColors(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[COLORS.shapeStart, COLORS.shapeEnd],
	);

	// Size: 120 → 130px, easeOutQuad
	const size = interpolate(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[SHAPE.startSize, SHAPE.endSize],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	return (
		<div
			style={{
				position: 'absolute',
				width: size,
				height: size,
				borderRadius,
				backgroundColor: fillColor,
				boxShadow: `0 0 30px ${fillColor}`,
				top: CANVAS.centerY - size / 2,
				left: CANVAS.centerX - size / 2,
			}}
		/>
	);
};
