import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
	CANVAS_WIDTH,
	CANVAS_HEIGHT,
	WALL_COLOR,
	NOZZLE_COLOR,
	MATERIAL_COLOR,
	WALL_POS,
	NOZZLE_POS,
	MATERIAL_POS,
	GHOST_FILL_OPACITY,
	GHOST_STROKE_WIDTH,
	GHOST_GLOW_BLUR,
	GHOST_GLOW_OPACITY,
	GHOST_LABEL_OPACITY,
	GHOST_LABEL_FONT_SIZE,
	FONT_FAMILY,
	GHOST_DRAW_START,
	GHOST_DRAW_END,
	PULSE_CYCLE_FRAMES,
} from "./constants";

// Path lengths for stroke-dashoffset animation
const WALL_PATH_LENGTH = 480;
const NOZZLE_PATH_LENGTH = 420;
const MATERIAL_PATH_LENGTH = 500;

export const GhostShapes: React.FC = () => {
	const frame = useCurrentFrame();

	const drawProgress = interpolate(
		frame,
		[GHOST_DRAW_START, GHOST_DRAW_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.inOut(Easing.cubic),
		},
	);

	// Gentle pulse after shapes are drawn (sinusoidal)
	const pulseRaw =
		frame >= 90
			? Math.sin(((frame - 90) / PULSE_CYCLE_FRAMES) * Math.PI * 2)
			: 0;
	const pulse = pulseRaw * 0.01; // very subtle opacity modulation

	const wallOffset = WALL_PATH_LENGTH * (1 - drawProgress);
	const nozzleOffset = NOZZLE_PATH_LENGTH * (1 - drawProgress);
	const materialOffset = MATERIAL_PATH_LENGTH * (1 - drawProgress);

	return (
		<AbsoluteFill>
			<svg
				width={CANVAS_WIDTH}
				height={CANVAS_HEIGHT}
				viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
			>
				<defs>
					<filter id="wallGlow">
						<feGaussianBlur
							stdDeviation={GHOST_GLOW_BLUR}
							result="blur"
						/>
						<feMerge>
							<feMergeNode in="blur" />
							<feMergeNode in="SourceGraphic" />
						</feMerge>
					</filter>
					<filter id="nozzleGlow">
						<feGaussianBlur
							stdDeviation={GHOST_GLOW_BLUR}
							result="blur"
						/>
						<feMerge>
							<feMergeNode in="blur" />
							<feMergeNode in="SourceGraphic" />
						</feMerge>
					</filter>
					<filter id="materialGlow">
						<feGaussianBlur
							stdDeviation={GHOST_GLOW_BLUR}
							result="blur"
						/>
						<feMerge>
							<feMergeNode in="blur" />
							<feMergeNode in="SourceGraphic" />
						</feMerge>
					</filter>
				</defs>

				{/* Wall segment — rectangular blocks */}
				<g
					opacity={GHOST_FILL_OPACITY + pulse}
					filter="url(#wallGlow)"
				>
					<path
						d={`M ${WALL_POS.x - 60} ${WALL_POS.y - 50}
							 h 40 v 100 h -40 Z
							 M ${WALL_POS.x - 10} ${WALL_POS.y - 70}
							 h 40 v 140 h -40 Z
							 M ${WALL_POS.x + 40} ${WALL_POS.y - 40}
							 h 40 v 90 h -40 Z`}
						fill="none"
						stroke={WALL_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH}
						strokeDasharray={WALL_PATH_LENGTH}
						strokeDashoffset={wallOffset}
					/>
				</g>

				{/* Wall glow layer */}
				<g opacity={GHOST_GLOW_OPACITY + pulse * 0.5}>
					<path
						d={`M ${WALL_POS.x - 60} ${WALL_POS.y - 50}
							 h 40 v 100 h -40 Z
							 M ${WALL_POS.x - 10} ${WALL_POS.y - 70}
							 h 40 v 140 h -40 Z
							 M ${WALL_POS.x + 40} ${WALL_POS.y - 40}
							 h 40 v 90 h -40 Z`}
						fill="none"
						stroke={WALL_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH + 4}
						strokeDasharray={WALL_PATH_LENGTH}
						strokeDashoffset={wallOffset}
						filter="url(#wallGlow)"
					/>
				</g>

				{/* Wall label */}
				<text
					x={WALL_POS.x}
					y={WALL_POS.y + 95}
					textAnchor="middle"
					fill={WALL_COLOR}
					opacity={GHOST_LABEL_OPACITY * drawProgress}
					fontSize={GHOST_LABEL_FONT_SIZE}
					fontFamily={FONT_FAMILY}
					fontWeight={600}
					letterSpacing={2}
				>
					WALLS
				</text>

				{/* Injection nozzle — tapered funnel */}
				<g
					opacity={GHOST_FILL_OPACITY + pulse}
					filter="url(#nozzleGlow)"
				>
					<path
						d={`M ${NOZZLE_POS.x - 40} ${NOZZLE_POS.y - 60}
							 L ${NOZZLE_POS.x + 40} ${NOZZLE_POS.y - 60}
							 L ${NOZZLE_POS.x + 15} ${NOZZLE_POS.y + 20}
							 L ${NOZZLE_POS.x + 10} ${NOZZLE_POS.y + 80}
							 L ${NOZZLE_POS.x - 10} ${NOZZLE_POS.y + 80}
							 L ${NOZZLE_POS.x - 15} ${NOZZLE_POS.y + 20}
							 Z`}
						fill="none"
						stroke={NOZZLE_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH}
						strokeDasharray={NOZZLE_PATH_LENGTH}
						strokeDashoffset={nozzleOffset}
					/>
				</g>

				{/* Nozzle glow layer */}
				<g opacity={GHOST_GLOW_OPACITY + pulse * 0.5}>
					<path
						d={`M ${NOZZLE_POS.x - 40} ${NOZZLE_POS.y - 60}
							 L ${NOZZLE_POS.x + 40} ${NOZZLE_POS.y - 60}
							 L ${NOZZLE_POS.x + 15} ${NOZZLE_POS.y + 20}
							 L ${NOZZLE_POS.x + 10} ${NOZZLE_POS.y + 80}
							 L ${NOZZLE_POS.x - 10} ${NOZZLE_POS.y + 80}
							 L ${NOZZLE_POS.x - 15} ${NOZZLE_POS.y + 20}
							 Z`}
						fill="none"
						stroke={NOZZLE_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH + 4}
						strokeDasharray={NOZZLE_PATH_LENGTH}
						strokeDashoffset={nozzleOffset}
						filter="url(#nozzleGlow)"
					/>
				</g>

				{/* Nozzle label */}
				<text
					x={NOZZLE_POS.x}
					y={NOZZLE_POS.y + 105}
					textAnchor="middle"
					fill={NOZZLE_COLOR}
					opacity={GHOST_LABEL_OPACITY * drawProgress}
					fontSize={GHOST_LABEL_FONT_SIZE}
					fontFamily={FONT_FAMILY}
					fontWeight={600}
					letterSpacing={2}
				>
					NOZZLE
				</text>

				{/* Material swatch — organic flowing shape */}
				<g
					opacity={GHOST_FILL_OPACITY + pulse}
					filter="url(#materialGlow)"
				>
					<path
						d={`M ${MATERIAL_POS.x - 50} ${MATERIAL_POS.y - 40}
							 C ${MATERIAL_POS.x - 30} ${MATERIAL_POS.y - 70},
							   ${MATERIAL_POS.x + 30} ${MATERIAL_POS.y - 70},
							   ${MATERIAL_POS.x + 50} ${MATERIAL_POS.y - 40}
							 C ${MATERIAL_POS.x + 60} ${MATERIAL_POS.y - 10},
							   ${MATERIAL_POS.x + 55} ${MATERIAL_POS.y + 30},
							   ${MATERIAL_POS.x + 40} ${MATERIAL_POS.y + 55}
							 C ${MATERIAL_POS.x + 20} ${MATERIAL_POS.y + 75},
							   ${MATERIAL_POS.x - 20} ${MATERIAL_POS.y + 75},
							   ${MATERIAL_POS.x - 40} ${MATERIAL_POS.y + 55}
							 C ${MATERIAL_POS.x - 55} ${MATERIAL_POS.y + 30},
							   ${MATERIAL_POS.x - 60} ${MATERIAL_POS.y - 10},
							   ${MATERIAL_POS.x - 50} ${MATERIAL_POS.y - 40}
							 Z`}
						fill="none"
						stroke={MATERIAL_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH}
						strokeDasharray={MATERIAL_PATH_LENGTH}
						strokeDashoffset={materialOffset}
					/>
					{/* Internal texture lines */}
					<path
						d={`M ${MATERIAL_POS.x - 30} ${MATERIAL_POS.y - 20}
							 C ${MATERIAL_POS.x - 10} ${MATERIAL_POS.y - 5},
							   ${MATERIAL_POS.x + 10} ${MATERIAL_POS.y + 10},
							   ${MATERIAL_POS.x + 30} ${MATERIAL_POS.y - 5}
							 M ${MATERIAL_POS.x - 25} ${MATERIAL_POS.y + 15}
							 C ${MATERIAL_POS.x - 5} ${MATERIAL_POS.y + 30},
							   ${MATERIAL_POS.x + 15} ${MATERIAL_POS.y + 35},
							   ${MATERIAL_POS.x + 35} ${MATERIAL_POS.y + 20}`}
						fill="none"
						stroke={MATERIAL_COLOR}
						strokeWidth={1}
						strokeDasharray={200}
						strokeDashoffset={200 * (1 - drawProgress)}
					/>
				</g>

				{/* Material glow layer */}
				<g opacity={GHOST_GLOW_OPACITY + pulse * 0.5}>
					<path
						d={`M ${MATERIAL_POS.x - 50} ${MATERIAL_POS.y - 40}
							 C ${MATERIAL_POS.x - 30} ${MATERIAL_POS.y - 70},
							   ${MATERIAL_POS.x + 30} ${MATERIAL_POS.y - 70},
							   ${MATERIAL_POS.x + 50} ${MATERIAL_POS.y - 40}
							 C ${MATERIAL_POS.x + 60} ${MATERIAL_POS.y - 10},
							   ${MATERIAL_POS.x + 55} ${MATERIAL_POS.y + 30},
							   ${MATERIAL_POS.x + 40} ${MATERIAL_POS.y + 55}
							 C ${MATERIAL_POS.x + 20} ${MATERIAL_POS.y + 75},
							   ${MATERIAL_POS.x - 20} ${MATERIAL_POS.y + 75},
							   ${MATERIAL_POS.x - 40} ${MATERIAL_POS.y + 55}
							 C ${MATERIAL_POS.x - 55} ${MATERIAL_POS.y + 30},
							   ${MATERIAL_POS.x - 60} ${MATERIAL_POS.y - 10},
							   ${MATERIAL_POS.x - 50} ${MATERIAL_POS.y - 40}
							 Z`}
						fill="none"
						stroke={MATERIAL_COLOR}
						strokeWidth={GHOST_STROKE_WIDTH + 4}
						strokeDasharray={MATERIAL_PATH_LENGTH}
						strokeDashoffset={materialOffset}
						filter="url(#materialGlow)"
					/>
				</g>

				{/* Material label */}
				<text
					x={MATERIAL_POS.x}
					y={MATERIAL_POS.y + 100}
					textAnchor="middle"
					fill={MATERIAL_COLOR}
					opacity={GHOST_LABEL_OPACITY * drawProgress}
					fontSize={GHOST_LABEL_FONT_SIZE}
					fontFamily={FONT_FAMILY}
					fontWeight={600}
					letterSpacing={2}
				>
					MATERIAL
				</text>
			</svg>
		</AbsoluteFill>
	);
};

export default GhostShapes;
