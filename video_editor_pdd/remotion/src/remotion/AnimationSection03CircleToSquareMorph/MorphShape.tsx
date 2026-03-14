import React from 'react';
import {
	useCurrentFrame,
	interpolate,
	interpolateColors,
	Easing,
} from 'remotion';
import { CANVAS, COLORS, SHAPE, TIMING } from './constants';

/**
 * The primary morphing shape: a centered 120x120 element that transitions
 * from a circle (borderRadius 50%) to a rounded square (borderRadius 12px),
 * with a color shift from blue to indigo and subtle scale animation.
 */
export const MorphShape: React.FC = () => {
	const frame = useCurrentFrame();

	// --- Border Radius: 60px (circle) → 12px (rounded square) ---
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

	// --- Fill color: #3B82F6 → #6366F1 (linear) ---
	const fillColor = interpolateColors(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[COLORS.shapeStart, COLORS.shapeEnd],
	);

	// --- Scale animation ---
	// Phase 1 (frames 0-5): Scale up 1.0 → 1.05
	const scaleUp = interpolate(
		frame,
		[0, TIMING.holdEnd],
		[1.0, 1.05],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	// Phase 3 (frames 30-35): Scale settle 1.05 → 1.0
	const scaleSettle = interpolate(
		frame,
		[TIMING.settleStart, TIMING.settleEnd],
		[1.05, 1.0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	let scale: number;
	if (frame < TIMING.holdEnd) {
		scale = scaleUp;
	} else if (frame < TIMING.settleStart) {
		scale = 1.05;
	} else {
		scale = scaleSettle;
	}

	return (
		<div
			style={{
				position: 'absolute',
				width: SHAPE.size,
				height: SHAPE.size,
				borderRadius,
				backgroundColor: fillColor,
				boxShadow: `0 0 30px ${fillColor}`,
				top: CANVAS.centerY - SHAPE.size / 2,
				left: CANVAS.centerX - SHAPE.size / 2,
				transform: `scale(${scale})`,
			}}
		/>
	);
};
