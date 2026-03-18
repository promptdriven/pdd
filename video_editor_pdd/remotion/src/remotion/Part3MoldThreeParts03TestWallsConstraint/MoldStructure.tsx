import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
	WALL_SEGMENTS,
	WALL_COLOR_DIM,
	CAVITY_COLOR,
	LABEL_COLOR_DIM,
	LABEL_COLOR_BRIGHT,
	CAVITY_LEFT,
	CAVITY_RIGHT,
	CAVITY_TOP,
	CAVITY_BOTTOM,
	WALL_STROKE,
	MONO_FONT,
	MOLD_CENTER_X,
	NOZZLE_Y,
	type WallSegment,
} from './constants';

/** Returns label position offset from a wall segment midpoint */
function getLabelOffset(seg: WallSegment): { dx: number; dy: number } {
	if (seg.normalX > 0) return { dx: -80, dy: 0 };
	if (seg.normalX < 0) return { dx: 14, dy: 0 };
	if (seg.normalY > 0) return { dx: 0, dy: 14 };
	return { dx: 0, dy: -14 };
}

interface MoldStructureProps {
	focusWallId: string | null;
	focusProgress: number; // 0..1
	wallFlashStates: Record<string, number>; // wallId → flash intensity 0..1
	fillLevel: number; // 0..1 how full the cavity is
}

const MoldStructure: React.FC<MoldStructureProps> = ({
	focusWallId,
	focusProgress,
	wallFlashStates,
	fillLevel,
}) => {
	const frame = useCurrentFrame();

	// Cavity fill height (from bottom up)
	const fillHeight = (CAVITY_BOTTOM - CAVITY_TOP) * fillLevel;
	const fillY = CAVITY_BOTTOM - fillHeight;

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{ position: 'absolute', top: 0, left: 0 }}
		>
			{/* Nozzle */}
			<line
				x1={MOLD_CENTER_X}
				y1={NOZZLE_Y - 40}
				x2={MOLD_CENTER_X}
				y2={CAVITY_TOP}
				stroke={WALL_COLOR_DIM}
				strokeWidth={2}
				opacity={0.5}
			/>
			<rect
				x={MOLD_CENTER_X - 15}
				y={NOZZLE_Y - 50}
				width={30}
				height={20}
				fill={WALL_COLOR_DIM}
				rx={3}
				opacity={0.6}
			/>

			{/* Cavity background fill (liquid level) */}
			{fillLevel > 0 && (
				<rect
					x={CAVITY_LEFT}
					y={fillY}
					width={CAVITY_RIGHT - CAVITY_LEFT}
					height={fillHeight}
					fill="#4A90D9"
					opacity={0.12}
					rx={2}
				/>
			)}

			{/* Cavity background */}
			<rect
				x={CAVITY_LEFT}
				y={CAVITY_TOP}
				width={CAVITY_RIGHT - CAVITY_LEFT}
				height={CAVITY_BOTTOM - CAVITY_TOP}
				fill={CAVITY_COLOR}
				stroke="none"
				rx={4}
			/>

			{/* Wall segments */}
			{WALL_SEGMENTS.map((seg) => {
				const flashIntensity = wallFlashStates[seg.id] || 0;
				const isFocused = focusWallId === seg.id;
				const baseOpacity = 0.4;
				const opacity = Math.min(1, baseOpacity + flashIntensity * 0.6);
				const strokeExpand = flashIntensity * 2;

				const midX = (seg.x1 + seg.x2) / 2;
				const midY = (seg.y1 + seg.y2) / 2;
				const offset = getLabelOffset(seg);

				// Label opacity: dim normally, bright on focus or flash
				const labelOpacity = isFocused
					? interpolate(focusProgress, [0, 1], [0.3, 1.0])
					: 0.3 + flashIntensity * 0.5;

				return (
					<g key={seg.id}>
						{/* Glow behind wall on flash */}
						{flashIntensity > 0.05 && (
							<line
								x1={seg.x1}
								y1={seg.y1}
								x2={seg.x2}
								y2={seg.y2}
								stroke="#D9944A"
								strokeWidth={WALL_STROKE + strokeExpand + 6}
								opacity={flashIntensity * 0.3}
								strokeLinecap="round"
								filter="url(#wallGlow)"
							/>
						)}
						{/* Wall line */}
						<line
							x1={seg.x1}
							y1={seg.y1}
							x2={seg.x2}
							y2={seg.y2}
							stroke="#D9944A"
							strokeWidth={WALL_STROKE + strokeExpand}
							opacity={opacity}
							strokeLinecap="round"
						/>
						{/* Label */}
						<text
							x={midX + offset.dx}
							y={midY + offset.dy}
							fill="#D9944A"
							opacity={labelOpacity}
							fontFamily="JetBrains Mono, Menlo, monospace"
							fontSize={9}
							textAnchor={seg.normalX > 0 ? 'end' : 'start'}
							dominantBaseline="middle"
						>
							{seg.label}
						</text>
					</g>
				);
			})}

			{/* SVG filters */}
			<defs>
				<filter id="wallGlow" x="-50%" y="-50%" width="200%" height="200%">
					<feGaussianBlur stdDeviation="4" />
				</filter>
			</defs>
		</svg>
	);
};

export default MoldStructure;
