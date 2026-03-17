import React from 'react';
import {
	useCurrentFrame,
	interpolate,
	Easing,
} from 'remotion';
import { CHART, COLORS, SEGMENTS, TIMING } from './constants';

/**
 * Converts degrees to radians.
 */
function degToRad(deg: number): number {
	return (deg * Math.PI) / 180;
}

/**
 * Describes an SVG arc path for a donut segment.
 * Angles are in degrees, 0 = 12 o'clock, clockwise.
 */
function describeArc(
	cx: number,
	cy: number,
	outerR: number,
	innerR: number,
	startDeg: number,
	endDeg: number,
): string {
	// Offset by -90 so 0 degrees = 12 o'clock
	const startRad = degToRad(startDeg - 90);
	const endRad = degToRad(endDeg - 90);

	const outerStartX = cx + outerR * Math.cos(startRad);
	const outerStartY = cy + outerR * Math.sin(startRad);
	const outerEndX = cx + outerR * Math.cos(endRad);
	const outerEndY = cy + outerR * Math.sin(endRad);

	const innerStartX = cx + innerR * Math.cos(endRad);
	const innerStartY = cy + innerR * Math.sin(endRad);
	const innerEndX = cx + innerR * Math.cos(startRad);
	const innerEndY = cy + innerR * Math.sin(startRad);

	const sweepAngle = endDeg - startDeg;
	const largeArc = sweepAngle > 180 ? 1 : 0;

	return [
		`M ${outerStartX} ${outerStartY}`,
		`A ${outerR} ${outerR} 0 ${largeArc} 1 ${outerEndX} ${outerEndY}`,
		`L ${innerStartX} ${innerStartY}`,
		`A ${innerR} ${innerR} 0 ${largeArc} 0 ${innerEndX} ${innerEndY}`,
		'Z',
	].join(' ');
}

/**
 * Computes label position on the outside of the donut.
 */
function getLabelPosition(
	cx: number,
	cy: number,
	radius: number,
	startDeg: number,
	endDeg: number,
): { x: number; y: number; anchorX: number; anchorY: number; align: 'left' | 'right' } {
	const midDeg = (startDeg + endDeg) / 2;
	const midRad = degToRad(midDeg - 90);
	const labelRadius = radius + 40;
	const anchorRadius = radius + 5;

	const x = cx + labelRadius * Math.cos(midRad);
	const y = cy + labelRadius * Math.sin(midRad);
	const anchorX = cx + anchorRadius * Math.cos(midRad);
	const anchorY = cy + anchorRadius * Math.sin(midRad);

	// Determine text alignment based on which side of chart
	const align = x > cx ? 'left' : 'right';

	return { x, y, anchorX, anchorY, align };
}

export const DonutChart: React.FC = () => {
	const frame = useCurrentFrame();

	// Phase 1: Ring outline fade in (frames 0-20)
	const ringOpacity = interpolate(
		frame,
		[TIMING.ringFadeStart, TIMING.ringFadeStart + TIMING.ringFadeDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	// Phase 2: Blue segment draw progress (frames 30-60)
	const blueProgress = interpolate(
		frame,
		[TIMING.blueSegmentStart, TIMING.blueSegmentStart + TIMING.blueSegmentDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);

	// Phase 3: Amber segment draw progress (frames 60-150)
	const amberProgress = interpolate(
		frame,
		[TIMING.amberSegmentStart, TIMING.amberSegmentStart + TIMING.amberSegmentDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.cubic),
		},
	);

	// Blue label opacity (fades in as segment completes)
	const blueLabelOpacity = interpolate(
		frame,
		[TIMING.blueSegmentStart + TIMING.blueSegmentDuration - 10, TIMING.blueSegmentStart + TIMING.blueSegmentDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		},
	);

	// Amber label opacity (fades in as segment completes)
	const amberLabelOpacity = interpolate(
		frame,
		[TIMING.amberSegmentStart + TIMING.amberSegmentDuration - 15, TIMING.amberSegmentStart + TIMING.amberSegmentDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		},
	);

	// Amber value scale emphasis (easeOut with back overshoot)
	const amberValueScale = interpolate(
		frame,
		[
			TIMING.amberSegmentStart + TIMING.amberSegmentDuration,
			TIMING.amberSegmentStart + TIMING.amberSegmentDuration + TIMING.valueEmphasisDuration,
		],
		[0.8, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.back(1.3)),
		},
	);

	const { centerX: cx, centerY: cy, outerRadius: outerR, innerRadius: innerR } = CHART;
	const blue = SEGMENTS.initialDev;
	const amber = SEGMENTS.maintenance;

	// Calculate drawn angles
	const blueEndAngle = blue.startAngle + (blue.endAngle - blue.startAngle) * blueProgress;
	const amberEndAngle = amber.startAngle + (amber.endAngle - amber.startAngle) * amberProgress;

	// Label positions
	const blueLabel = getLabelPosition(cx, cy, outerR, blue.startAngle, blue.endAngle);
	const amberLabel = getLabelPosition(cx, cy, outerR, amber.startAngle, amber.endAngle);

	return (
		<svg
			width={1920}
			height={1080}
			viewBox="0 0 1920 1080"
			style={{ position: 'absolute', top: 0, left: 0 }}
		>
			{/* Donut ring outline */}
			<circle
				cx={cx}
				cy={cy}
				r={(outerR + innerR) / 2}
				fill="none"
				stroke={COLORS.segmentBorder}
				strokeWidth={outerR - innerR}
				opacity={ringOpacity * 0.3}
			/>

			{/* Inner circle for donut hole */}
			<circle
				cx={cx}
				cy={cy}
				r={innerR}
				fill={COLORS.background}
				opacity={ringOpacity}
			/>

			{/* Blue segment — Initial Development */}
			{blueProgress > 0.001 && (
				<path
					d={describeArc(cx, cy, outerR, innerR, blue.startAngle, blueEndAngle)}
					fill={blue.color}
					stroke={COLORS.segmentBorder}
					strokeWidth={2}
				/>
			)}

			{/* Amber segment — Maintenance */}
			{amberProgress > 0.001 && (
				<path
					d={describeArc(cx, cy, outerR, innerR, amber.startAngle, amberEndAngle)}
					fill={amber.color}
					stroke={COLORS.segmentBorder}
					strokeWidth={2}
				/>
			)}

			{/* Center text */}
			<text
				x={cx}
				y={cy - 8}
				textAnchor="middle"
				dominantBaseline="middle"
				fontFamily="Inter, sans-serif"
				fontSize={11}
				fill={COLORS.centerText}
				opacity={ringOpacity * 0.4}
				letterSpacing={3}
				fontWeight={500}
			>
				SOFTWARE
			</text>
			<text
				x={cx}
				y={cy + 12}
				textAnchor="middle"
				dominantBaseline="middle"
				fontFamily="Inter, sans-serif"
				fontSize={11}
				fill={COLORS.centerText}
				opacity={ringOpacity * 0.4}
				letterSpacing={3}
				fontWeight={500}
			>
				COST
			</text>

			{/* Blue segment label + leader line */}
			<g opacity={blueLabelOpacity}>
				<line
					x1={blueLabel.anchorX}
					y1={blueLabel.anchorY}
					x2={blueLabel.x}
					y2={blueLabel.y}
					stroke={blue.color}
					strokeWidth={1}
					opacity={0.5}
				/>
				<text
					x={blueLabel.x + (blueLabel.align === 'left' ? 8 : -8)}
					y={blueLabel.y - 10}
					textAnchor={blueLabel.align === 'left' ? 'start' : 'end'}
					fontFamily="Inter, sans-serif"
					fontSize={14}
					fill={blue.color}
					opacity={0.7}
				>
					{blue.label}
				</text>
				<text
					x={blueLabel.x + (blueLabel.align === 'left' ? 8 : -8)}
					y={blueLabel.y + 12}
					textAnchor={blueLabel.align === 'left' ? 'start' : 'end'}
					fontFamily="Inter, sans-serif"
					fontSize={blue.valueSize}
					fontWeight={700}
					fill={blue.color}
				>
					{blue.value}
				</text>
			</g>

			{/* Amber segment label + leader line */}
			<g opacity={amberLabelOpacity}>
				<line
					x1={amberLabel.anchorX}
					y1={amberLabel.anchorY}
					x2={amberLabel.x}
					y2={amberLabel.y}
					stroke={amber.color}
					strokeWidth={1}
					opacity={0.5}
				/>
				<text
					x={amberLabel.x + (amberLabel.align === 'left' ? 8 : -8)}
					y={amberLabel.y - 10}
					textAnchor={amberLabel.align === 'left' ? 'start' : 'end'}
					fontFamily="Inter, sans-serif"
					fontSize={14}
					fill={amber.color}
					opacity={0.7}
				>
					{amber.label}
				</text>
				<text
					x={amberLabel.x + (amberLabel.align === 'left' ? 8 : -8)}
					y={amberLabel.y + 12}
					textAnchor={amberLabel.align === 'left' ? 'start' : 'end'}
					fontFamily="Inter, sans-serif"
					fontSize={amber.valueSize}
					fontWeight={700}
					fill={amber.color}
					style={{
						transform: `scale(${amberValueScale})`,
						transformOrigin: `${amberLabel.x}px ${amberLabel.y + 12}px`,
					}}
				>
					{amber.value}
				</text>
			</g>
		</svg>
	);
};

export default DonutChart;
