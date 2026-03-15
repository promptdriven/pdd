import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, WAVEFORM, ANIMATION, BASE_CANVAS } from './constants';

export const WaveformGraph: React.FC = () => {
	const frame = useCurrentFrame();
	const { width, height } = BASE_CANVAS;
	const { yStart, yEnd, amplitude, frequency, samples } = WAVEFORM;

	const centerY = (yStart + yEnd) / 2;
	const waveAmplitude = ((yEnd - yStart) / 2) * amplitude;

	// Phase shift for subtle oscillation after draw completes
	const phaseShift =
		frame >= ANIMATION.oscillationStart
			? interpolate(
					frame,
					[ANIMATION.oscillationStart, ANIMATION.totalDuration],
					[0, Math.PI * 2],
					{
						extrapolateLeft: 'clamp',
						extrapolateRight: 'clamp',
						easing: Easing.inOut(Easing.sin),
					},
				)
			: 0;

	// Build SVG path from sample points
	const points: Array<{ x: number; y: number }> = [];
	for (let i = 0; i <= samples; i++) {
		const x = (i / samples) * width;
		const y =
			centerY +
			waveAmplitude *
				Math.sin(
					(2 * Math.PI * frequency * i) / samples + phaseShift,
				);
		points.push({ x, y });
	}

	// Stroke path
	const pathD = points
		.map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x.toFixed(2)} ${p.y.toFixed(2)}`)
		.join(' ');

	// Fill path (close along the bottom)
	const fillD =
		pathD +
		` L ${width} ${yEnd} L 0 ${yEnd} Z`;

	// Approximate path length for dash animation
	const pathLength = width * 1.1;

	// Draw progress (linear, frames 4-30)
	const drawProgress = interpolate(
		frame,
		[ANIMATION.waveDrawStart, ANIMATION.waveDrawEnd],
		[0, 1],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);

	const dashOffset = pathLength * (1 - drawProgress);

	// Fill opacity follows draw progress
	const fillOpacity = interpolate(
		frame,
		[ANIMATION.waveDrawStart, ANIMATION.waveDrawEnd],
		[0, 1],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);

	return (
		<svg
			width={width}
			height={height}
			viewBox={`0 0 ${width} ${height}`}
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
				width: '100%',
				height: '100%',
			}}
		>
			{/* Filled area beneath the waveform */}
			<path
				d={fillD}
				fill={COLORS.waveFill}
				opacity={fillOpacity}
			/>
			{/* Animated stroke */}
			<path
				d={pathD}
				fill="none"
				stroke={COLORS.waveStroke}
				strokeWidth={WAVEFORM.strokeWidth}
				strokeDasharray={pathLength}
				strokeDashoffset={dashOffset}
				strokeLinecap="round"
			/>
		</svg>
	);
};
