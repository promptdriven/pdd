import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, GRID_ROWS, ANIMATION } from './constants';

export const GridOverlay: React.FC = () => {
	const frame = useCurrentFrame();

	const gridOpacity = interpolate(
		frame,
		[ANIMATION.overlayFadeStart, ANIMATION.overlayFadeEnd],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	const lines = [];
	for (let i = 1; i <= GRID_ROWS; i++) {
		const yPercent = (i / (GRID_ROWS + 1)) * 100;
		lines.push(
			<div
				key={i}
				style={{
					position: 'absolute',
					top: `${yPercent}%`,
					left: 0,
					width: '100%',
					height: 1,
					backgroundColor: COLORS.gridLine,
					opacity: gridOpacity,
				}}
			/>,
		);
	}

	return <>{lines}</>;
};
