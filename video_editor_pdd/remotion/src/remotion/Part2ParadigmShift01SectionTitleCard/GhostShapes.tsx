import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import {
	MOLD_POS,
	CIRCUIT_POS,
	MOLD_COLOR,
	CIRCUIT_COLOR,
	GHOST_OPACITY,
	GHOST_STROKE_WIDTH,
	GHOST_GLOW_BLUR,
	GHOST_GLOW_OPACITY,
	GHOST_DRAW_DURATION,
	MOLD_PULSE_CYCLE,
} from './constants';

/**
 * Simplified injection mold cavity cross-section.
 * Rectangular cavity with a tapered nozzle at top.
 */
const MoldCavityPath = (): string => {
	// Nozzle (tapered triangle at top)
	const nozzle = 'M -8,-60 L 0,-40 L 8,-60';
	// Cavity body (rectangular with slight chamfers)
	const cavity = [
		'M -40,-40',
		'L -40,40',
		'L -30,50',
		'L 30,50',
		'L 40,40',
		'L 40,-40',
		'L 30,-40',
		'L 30,30',
		'L -30,30',
		'L -30,-40',
		'Z',
	].join(' ');
	return `${nozzle} ${cavity}`;
};

/**
 * Simplified circuit schematic fragment with gate symbols and traces.
 */
const CircuitSchematicPath = (): string => {
	// AND gate (curved front)
	const andGate = [
		'M -50,-20 L -50,20 L -20,20',
		'Q 10,20 10,0',
		'Q 10,-20 -20,-20',
		'L -50,-20',
	].join(' ');
	// OR gate (curved body)
	const orGate = [
		'M 20,-20 Q 30,-20 40,-10',
		'Q 50,0 40,10',
		'Q 30,20 20,20',
		'Q 30,10 30,0',
		'Q 30,-10 20,-20',
	].join(' ');
	// Connecting wires / traces
	const traces = [
		'M -70,-10 L -50,-10',
		'M -70,10 L -50,10',
		'M 10,0 L 20,0',
		'M 50,0 L 70,0',
		// Extra horizontal traces
		'M -70,35 L 70,35',
		'M -70,-35 L 70,-35',
		// Small vias/dots simulated as tiny cross marks
		'M -60,35 L -60,30',
		'M 60,35 L 60,30',
		'M -60,-35 L -60,-30',
		'M 60,-35 L 60,-30',
	].join(' ');
	return `${andGate} ${orGate} ${traces}`;
};

const moldPath = MoldCavityPath();
const circuitPath = CircuitSchematicPath();

// Approximate total path lengths for dashoffset animation
const MOLD_PATH_LENGTH = 600;
const CIRCUIT_PATH_LENGTH = 700;

export const GhostShapes: React.FC = () => {
	const frame = useCurrentFrame();

	// Draw progress (0 to 1 over GHOST_DRAW_DURATION frames)
	const drawProgress = interpolate(frame, [0, GHOST_DRAW_DURATION], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.cubic),
	});

	// Mold pulse — gentle amber glow starting at frame 90 (relative to ghost start at 15, so localFrame 75)
	const pulseFrame = Math.max(0, frame - 75);
	const pulsePhase = (pulseFrame % MOLD_PULSE_CYCLE) / MOLD_PULSE_CYCLE;
	const pulseOpacity = interpolate(
		Math.sin(pulsePhase * Math.PI * 2),
		[-1, 1],
		[GHOST_GLOW_OPACITY, GHOST_GLOW_OPACITY * 3],
		{ extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
	);

	const moldDashOffset = MOLD_PATH_LENGTH * (1 - drawProgress);
	const circuitDashOffset = CIRCUIT_PATH_LENGTH * (1 - drawProgress);

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{ position: 'absolute', top: 0, left: 0 }}
		>
			<defs>
				<filter id="moldGlow" x="-50%" y="-50%" width="200%" height="200%">
					<feGaussianBlur stdDeviation={GHOST_GLOW_BLUR} result="blur" />
					<feMerge>
						<feMergeNode in="blur" />
						<feMergeNode in="SourceGraphic" />
					</feMerge>
				</filter>
				<filter id="circuitGlow" x="-50%" y="-50%" width="200%" height="200%">
					<feGaussianBlur stdDeviation={GHOST_GLOW_BLUR} result="blur" />
					<feMerge>
						<feMergeNode in="blur" />
						<feMergeNode in="SourceGraphic" />
					</feMerge>
				</filter>
			</defs>

			{/* Mold cavity outline */}
			<g transform={`translate(${MOLD_POS.x}, ${MOLD_POS.y})`}>
				{/* Glow layer */}
				<path
					d={moldPath}
					fill="none"
					stroke={MOLD_COLOR}
					strokeWidth={GHOST_STROKE_WIDTH + 4}
					opacity={pulseFrame > 0 ? pulseOpacity : GHOST_GLOW_OPACITY}
					strokeDasharray={MOLD_PATH_LENGTH}
					strokeDashoffset={moldDashOffset}
					filter="url(#moldGlow)"
				/>
				{/* Main stroke */}
				<path
					d={moldPath}
					fill="none"
					stroke={MOLD_COLOR}
					strokeWidth={GHOST_STROKE_WIDTH}
					opacity={GHOST_OPACITY}
					strokeDasharray={MOLD_PATH_LENGTH}
					strokeDashoffset={moldDashOffset}
				/>
			</g>

			{/* Circuit schematic fragment */}
			<g transform={`translate(${CIRCUIT_POS.x}, ${CIRCUIT_POS.y})`}>
				{/* Glow layer */}
				<path
					d={circuitPath}
					fill="none"
					stroke={CIRCUIT_COLOR}
					strokeWidth={GHOST_STROKE_WIDTH + 4}
					opacity={GHOST_GLOW_OPACITY}
					strokeDasharray={CIRCUIT_PATH_LENGTH}
					strokeDashoffset={circuitDashOffset}
					filter="url(#circuitGlow)"
				/>
				{/* Main stroke */}
				<path
					d={circuitPath}
					fill="none"
					stroke={CIRCUIT_COLOR}
					strokeWidth={GHOST_STROKE_WIDTH}
					opacity={GHOST_OPACITY}
					strokeDasharray={CIRCUIT_PATH_LENGTH}
					strokeDashoffset={circuitDashOffset}
				/>
			</g>
		</svg>
	);
};
