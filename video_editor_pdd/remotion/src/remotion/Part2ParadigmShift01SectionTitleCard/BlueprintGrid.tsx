import React, { useMemo } from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame } from 'remotion';
import {
	WIDTH,
	HEIGHT,
	GRID_COLOR,
	GRID_SPACING,
	GRID_ACCENT_EVERY,
	GRID_BASE_OPACITY,
	GRID_ACCENT_OPACITY,
	BG_FADE_END,
} from './constants';

export const BlueprintGrid: React.FC = () => {
	const frame = useCurrentFrame();

	const opacity = interpolate(frame, [0, BG_FADE_END], [0, 1], {
		extrapolateRight: 'clamp',
	});

	const lines = useMemo(() => {
		const result: React.ReactNode[] = [];

		// Vertical lines
		for (let x = 0; x <= WIDTH; x += GRID_SPACING) {
			const isAccent = x % GRID_ACCENT_EVERY === 0;
			result.push(
				<line
					key={`v-${x}`}
					x1={x}
					y1={0}
					x2={x}
					y2={HEIGHT}
					stroke={GRID_COLOR}
					strokeWidth={1}
					opacity={isAccent ? GRID_ACCENT_OPACITY : GRID_BASE_OPACITY}
				/>,
			);
		}

		// Horizontal lines
		for (let y = 0; y <= HEIGHT; y += GRID_SPACING) {
			const isAccent = y % GRID_ACCENT_EVERY === 0;
			result.push(
				<line
					key={`h-${y}`}
					x1={0}
					y1={y}
					x2={WIDTH}
					y2={y}
					stroke={GRID_COLOR}
					strokeWidth={1}
					opacity={isAccent ? GRID_ACCENT_OPACITY : GRID_BASE_OPACITY}
				/>,
			);
		}

		return result;
	}, []);

	return (
		<AbsoluteFill style={{ opacity }}>
			<svg
				width={WIDTH}
				height={HEIGHT}
				viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
				style={{ position: 'absolute', top: 0, left: 0 }}
			>
				{lines}
			</svg>
		</AbsoluteFill>
	);
};
