import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, SHAPES, TIMING } from './constants';

export const AnimatedSquare: React.FC = () => {
	const frame = useCurrentFrame();

	// Floating bob: sin-based y oscillation starting at frame 15
	const floatProgress = interpolate(
		frame,
		[TIMING.floatStart, TIMING.totalFrames],
		[0, 1],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);
	const floatY =
		frame >= TIMING.floatStart
			? Math.sin(floatProgress * Math.PI * 2 * ((TIMING.totalFrames - TIMING.floatStart) / SHAPES.floatPeriod)) * SHAPES.floatAmplitude
			: 0;

	return (
		<div
			style={{
				position: 'absolute',
				left: SHAPES.squareCenterX - SHAPES.squareSize / 2,
				top: SHAPES.squareCenterY - SHAPES.squareSize / 2 + floatY,
				width: SHAPES.squareSize,
				height: SHAPES.squareSize,
				borderRadius: SHAPES.squareBorderRadius,
				backgroundColor: COLORS.squareFill,
			}}
		/>
	);
};
