import React from 'react';
import {useCurrentFrame, interpolate, interpolateColors, Easing} from 'remotion';
import {
	TRIANGLE_VERTICES,
	EDGE_WIDTH_START,
	EDGE_WIDTH_END,
	EDGE_COLOR_START,
	EDGE_COLOR_END,
	EDGE_OPACITY_START,
	EDGE_OPACITY_END,
	GLOW_LAYERS,
} from './constants';

const pathFromVertices = (vertices: [number, number][]): string => {
	return `M ${vertices[0][0]} ${vertices[0][1]} L ${vertices[1][0]} ${vertices[1][1]} L ${vertices[2][0]} ${vertices[2][1]} Z`;
};

export const TriangleGlow: React.FC = () => {
	const frame = useCurrentFrame();
	const path = pathFromVertices(TRIANGLE_VERTICES);

	// Edge brightening over frames 0-90
	const edgeProgress = interpolate(frame, [0, 90], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	const edgeWidth =
		EDGE_WIDTH_START + (EDGE_WIDTH_END - EDGE_WIDTH_START) * edgeProgress;
	const edgeColor = interpolateColors(
		edgeProgress,
		[0, 1],
		[EDGE_COLOR_START, EDGE_COLOR_END]
	);
	const edgeOpacity =
		EDGE_OPACITY_START +
		(EDGE_OPACITY_END - EDGE_OPACITY_START) * edgeProgress;

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{position: 'absolute', top: 0, left: 0}}
		>
			<defs>
				{GLOW_LAYERS.map((layer, i) => (
					<filter
						key={`glow-${i}`}
						id={`triangle-glow-${i}`}
						x="-50%"
						y="-50%"
						width="200%"
						height="200%"
					>
						<feGaussianBlur stdDeviation={layer.blur / 2} result="blur" />
					</filter>
				))}
			</defs>

			{/* Glow layers — rendered behind the main edge */}
			{GLOW_LAYERS.map((layer, i) => {
				const layerProgress = interpolate(
					frame,
					[30 + layer.delay, 90 + layer.delay],
					[0, 1],
					{
						extrapolateLeft: 'clamp',
						extrapolateRight: 'clamp',
						easing: Easing.out(Easing.quad),
					}
				);

				return (
					<path
						key={`glow-layer-${i}`}
						d={path}
						fill="none"
						stroke={layer.color}
						strokeWidth={edgeWidth + layer.blur * 0.5}
						opacity={layer.opacity * layerProgress}
						filter={`url(#triangle-glow-${i})`}
					/>
				);
			})}

			{/* Main edge stroke */}
			<path
				d={path}
				fill="none"
				stroke={edgeColor}
				strokeWidth={edgeWidth}
				opacity={edgeOpacity}
				strokeLinejoin="round"
			/>
		</svg>
	);
};
