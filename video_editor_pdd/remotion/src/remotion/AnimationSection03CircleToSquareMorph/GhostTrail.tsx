import React from 'react';
import { useCurrentFrame, interpolate, interpolateColors, Easing } from 'remotion';
import { CANVAS, COLORS, SHAPE, TIMING, GHOST } from './constants';

/**
 * Computes the border radius for a given effective frame.
 */
function getBorderRadius(frame: number): number {
	return interpolate(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[SHAPE.borderRadiusStart, SHAPE.borderRadiusEnd],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);
}

/**
 * Computes the fill color for a given effective frame.
 */
function getFillColor(frame: number): string {
	return interpolateColors(
		frame,
		[TIMING.morphStart, TIMING.morphEnd],
		[COLORS.shapeStart, COLORS.shapeEnd],
	);
}

/**
 * Renders 3 ghost copies of the morphing shape at decreasing opacity,
 * each offset by a number of frames behind the current frame.
 * Ghost trails are visible during the morph phase and fade out during settle.
 */
export const GhostTrail: React.FC = () => {
	const frame = useCurrentFrame();

	// Ghost trails only visible during morph and fade out during settle
	const ghostVisibility = interpolate(
		frame,
		[TIMING.morphStart, TIMING.morphStart + 2, TIMING.settleStart, TIMING.settleEnd],
		[0, 1, 1, 0],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);

	if (ghostVisibility <= 0) {
		return null;
	}

	return (
		<>
			{GHOST.frameOffsets.map((offset, i) => {
				const ghostFrame = Math.max(0, frame - offset);
				const radius = getBorderRadius(ghostFrame);
				const color = getFillColor(ghostFrame);
				const baseOpacity = GHOST.opacities[i];

				return (
					<div
						key={i}
						style={{
							position: 'absolute',
							width: SHAPE.size,
							height: SHAPE.size,
							borderRadius: radius,
							backgroundColor: color,
							opacity: baseOpacity * ghostVisibility,
							top: CANVAS.centerY - SHAPE.size / 2,
							left: CANVAS.centerX - SHAPE.size / 2,
						}}
					/>
				);
			})}
		</>
	);
};
