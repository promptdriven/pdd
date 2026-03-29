import React from 'react';
import {interpolate, Easing} from 'remotion';
import {
	CANVAS_WIDTH,
	CANVAS_HEIGHT,
	MOLD_OUTLINE_COLOR,
	MOLD_OUTLINE_OPACITY,
	MOLD_FILL_COLOR,
	MOLD_FILL_OPACITY,
	MOLD_STROKE_WIDTH,
	MOLD_DRAW_DURATION,
	MOLD_PULSE_CYCLE,
} from './constants';

/**
 * A ghost mold cross-section silhouette drawn at very low opacity.
 * Renders an injection mold cavity outline with a faint liquid fill.
 */
export const MoldSilhouette: React.FC<{localFrame: number}> = ({localFrame}) => {
	// Stroke-dashoffset animation for drawing the outline
	const totalPathLength = 1200;
	const drawProgress = interpolate(
		localFrame,
		[0, MOLD_DRAW_DURATION],
		[totalPathLength, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);

	// Subtle pulse on the outline after drawn
	const pulseOpacity =
		localFrame > MOLD_DRAW_DURATION
			? MOLD_OUTLINE_OPACITY +
				interpolate(
					Math.sin(
						((localFrame - MOLD_DRAW_DURATION) / MOLD_PULSE_CYCLE) *
							Math.PI *
							2,
					),
					[-1, 1],
					[-0.01, 0.01],
					{extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
				)
			: MOLD_OUTLINE_OPACITY;

	const fillOpacity =
		localFrame > MOLD_DRAW_DURATION
			? interpolate(localFrame, [MOLD_DRAW_DURATION, MOLD_DRAW_DURATION + 20], [0, MOLD_FILL_OPACITY], {
					extrapolateLeft: 'clamp',
					extrapolateRight: 'clamp',
				})
			: 0;

	// Center of the canvas
	const cx = CANVAS_WIDTH / 2;
	const cy = CANVAS_HEIGHT / 2;

	// Mold cross-section: two halves of a mold with a cavity in the center
	// Top mold half
	const topMold = `
		M ${cx - 200} ${cy - 120}
		L ${cx + 200} ${cy - 120}
		L ${cx + 200} ${cy - 20}
		C ${cx + 160} ${cy - 20}, ${cx + 120} ${cy - 60}, ${cx + 80} ${cy - 60}
		L ${cx - 80} ${cy - 60}
		C ${cx - 120} ${cy - 60}, ${cx - 160} ${cy - 20}, ${cx - 200} ${cy - 20}
		Z
	`;

	// Bottom mold half
	const bottomMold = `
		M ${cx - 200} ${cy + 120}
		L ${cx + 200} ${cy + 120}
		L ${cx + 200} ${cy + 20}
		C ${cx + 160} ${cy + 20}, ${cx + 120} ${cy + 60}, ${cx + 80} ${cy + 60}
		L ${cx - 80} ${cy + 60}
		C ${cx - 120} ${cy + 60}, ${cx - 160} ${cy + 20}, ${cx - 200} ${cy + 20}
		Z
	`;

	// Injection nozzle on left side
	const nozzle = `
		M ${cx - 260} ${cy - 15}
		L ${cx - 200} ${cy - 15}
		L ${cx - 200} ${cy + 15}
		L ${cx - 260} ${cy + 15}
		L ${cx - 270} ${cy - 5}
		L ${cx - 270} ${cy + 5}
		Z
	`;

	// Cavity shape (the interior void)
	const cavity = `
		M ${cx - 80} ${cy - 55}
		C ${cx - 110} ${cy - 55}, ${cx - 150} ${cy - 15}, ${cx - 195} ${cy - 15}
		L ${cx - 195} ${cy + 15}
		C ${cx - 150} ${cy + 15}, ${cx - 110} ${cy + 55}, ${cx - 80} ${cy + 55}
		L ${cx + 80} ${cy + 55}
		C ${cx + 110} ${cy + 55}, ${cx + 150} ${cy + 15}, ${cx + 195} ${cy + 15}
		L ${cx + 195} ${cy - 15}
		C ${cx + 150} ${cy - 15}, ${cx + 110} ${cy - 55}, ${cx + 80} ${cy - 55}
		Z
	`;

	return (
		<svg
			width={CANVAS_WIDTH}
			height={CANVAS_HEIGHT}
			style={{position: 'absolute', top: 0, left: 0}}
		>
			<defs>
				<radialGradient id="moldFillGradient" cx="50%" cy="50%" r="50%">
					<stop offset="0%" stopColor={MOLD_FILL_COLOR} stopOpacity={fillOpacity * 1.5} />
					<stop offset="100%" stopColor={MOLD_FILL_COLOR} stopOpacity={0} />
				</radialGradient>
			</defs>

			{/* Fill hint in cavity */}
			<path
				d={cavity}
				fill="url(#moldFillGradient)"
			/>

			{/* Mold outlines */}
			<path
				d={topMold}
				fill="none"
				stroke={MOLD_OUTLINE_COLOR}
				strokeWidth={MOLD_STROKE_WIDTH}
				opacity={pulseOpacity}
				strokeDasharray={totalPathLength}
				strokeDashoffset={drawProgress}
			/>
			<path
				d={bottomMold}
				fill="none"
				stroke={MOLD_OUTLINE_COLOR}
				strokeWidth={MOLD_STROKE_WIDTH}
				opacity={pulseOpacity}
				strokeDasharray={totalPathLength}
				strokeDashoffset={drawProgress}
			/>
			<path
				d={nozzle}
				fill="none"
				stroke={MOLD_OUTLINE_COLOR}
				strokeWidth={MOLD_STROKE_WIDTH}
				opacity={pulseOpacity}
				strokeDasharray={totalPathLength}
				strokeDashoffset={drawProgress}
			/>

			{/* Cavity outline */}
			<path
				d={cavity}
				fill="none"
				stroke={MOLD_OUTLINE_COLOR}
				strokeWidth={MOLD_STROKE_WIDTH * 0.75}
				opacity={pulseOpacity * 0.7}
				strokeDasharray={totalPathLength}
				strokeDashoffset={drawProgress}
				strokeLinecap="round"
			/>
		</svg>
	);
};
