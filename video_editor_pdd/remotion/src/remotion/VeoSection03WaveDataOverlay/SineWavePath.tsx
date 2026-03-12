import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING, type WaveDataOverlayLayout } from './constants';

interface SineWavePathProps {
	layout: WaveDataOverlayLayout;
}

export const SineWavePath: React.FC<SineWavePathProps> = ({ layout }) => {
	const frame = useCurrentFrame();
	const { width, height, wave } = layout;

	// Build the sine wave SVG path
	const points: string[] = [];

	for (let x = 0; x <= width; x++) {
		const y =
			wave.centerY +
			wave.amplitude * Math.sin((2 * Math.PI * x) / wave.wavelength);
		if (x === 0) {
			points.push(`M ${x} ${y}`);
		} else {
			points.push(`L ${x} ${y}`);
		}
	}

	const pathD = points.join(' ');

	// Approximate path length for dash animation
	const pathLength = width * 1.05;

	// Animate the wave drawing left-to-right (linear)
	const drawProgress = interpolate(
		frame,
		[ANIMATION_TIMING.waveDrawStart, ANIMATION_TIMING.waveDrawEnd],
		[0, 1],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);

	const dashOffset = pathLength * (1 - drawProgress);

	return (
		<svg
			width={width}
			height={height}
			style={{
				position: 'absolute',
				top: 0,
				left: 0,
			}}
		>
			<path
				d={pathD}
				fill="none"
				stroke={COLORS.waveStroke}
				strokeWidth={wave.strokeWidth}
				strokeDasharray={pathLength}
				strokeDashoffset={dashOffset}
				strokeLinecap="round"
			/>
		</svg>
	);
};
