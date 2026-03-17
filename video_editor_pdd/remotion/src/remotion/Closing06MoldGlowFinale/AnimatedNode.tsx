import React from 'react';
import {useCurrentFrame, interpolate, interpolateColors, Easing} from 'remotion';
import {
	NODE_RADIUS_START,
	NODE_RADIUS_END,
	NODE_GROW_DURATION,
	NODE_PULSE_PERIOD,
	NODE_GLOW_RADIUS,
	NODE_GLOW_OPACITY,
} from './constants';

interface AnimatedNodeProps {
	center: [number, number];
	fillFrom: string;
	fillTo: string;
	glowColor: string;
	/** Frame offset within the Sequence (node animation starts at parent Sequence from=30) */
}

export const AnimatedNode: React.FC<AnimatedNodeProps> = ({
	center,
	fillFrom,
	fillTo,
	glowColor,
}) => {
	const frame = useCurrentFrame();

	// Growth animation (frames 0-50 within this sequence, which is globally 30-80)
	const growProgress = interpolate(frame, [0, NODE_GROW_DURATION], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	const radius =
		NODE_RADIUS_START +
		(NODE_RADIUS_END - NODE_RADIUS_START) * growProgress;

	// Color brightening
	const fillColor = interpolateColors(
		growProgress,
		[0, 1],
		[fillFrom, fillTo]
	);

	// Slow radial pulse — sinusoidal, every NODE_PULSE_PERIOD frames
	const pulsePhase = (frame % NODE_PULSE_PERIOD) / NODE_PULSE_PERIOD;
	const pulseFactor = 1 + 0.08 * Math.sin(pulsePhase * Math.PI * 2);
	const pulseRadius = radius * pulseFactor;

	// Glow opacity fade-in
	const glowOpacity = interpolate(frame, [0, 60], [0, NODE_GLOW_OPACITY], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// Glow pulse
	const glowPulseRadius = NODE_GLOW_RADIUS * pulseFactor;

	const filterId = `node-glow-${center[0]}-${center[1]}`;

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{position: 'absolute', top: 0, left: 0}}
		>
			<defs>
				<filter
					id={filterId}
					x="-100%"
					y="-100%"
					width="300%"
					height="300%"
				>
					<feGaussianBlur stdDeviation={glowPulseRadius / 2} result="blur" />
				</filter>
			</defs>

			{/* Outer glow */}
			<circle
				cx={center[0]}
				cy={center[1]}
				r={pulseRadius + glowPulseRadius * 0.5}
				fill={glowColor}
				opacity={glowOpacity}
				filter={`url(#${filterId})`}
			/>

			{/* Main node */}
			<circle
				cx={center[0]}
				cy={center[1]}
				r={pulseRadius}
				fill={fillColor}
			/>
		</svg>
	);
};
