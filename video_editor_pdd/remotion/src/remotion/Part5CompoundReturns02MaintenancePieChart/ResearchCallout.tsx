import React from 'react';
import {
	useCurrentFrame,
	interpolate,
	Easing,
} from 'remotion';
import { COLORS, TIMING } from './constants';

interface ResearchCalloutProps {
	x: number;
	y: number;
	width: number;
	height: number;
	mainText: string;
	subText: string;
	source: string;
	iconType: 'bar_chart' | 'clock';
	/** The absolute frame at which this callout starts appearing */
	appearFrame: number;
}

/**
 * Simple bar chart icon rendered as SVG elements.
 */
const BarChartIcon: React.FC<{ color: string }> = ({ color }) => (
	<svg width={20} height={20} viewBox="0 0 20 20" style={{ flexShrink: 0 }}>
		<rect x={2} y={12} width={4} height={6} rx={1} fill={color} opacity={0.7} />
		<rect x={8} y={7} width={4} height={11} rx={1} fill={color} opacity={0.85} />
		<rect x={14} y={3} width={4} height={15} rx={1} fill={color} />
	</svg>
);

/**
 * Simple clock icon rendered as SVG elements.
 */
const ClockIcon: React.FC<{ color: string }> = ({ color }) => (
	<svg width={20} height={20} viewBox="0 0 20 20" style={{ flexShrink: 0 }}>
		<circle cx={10} cy={10} r={8} fill="none" stroke={color} strokeWidth={1.5} opacity={0.8} />
		<line x1={10} y1={10} x2={10} y2={5} stroke={color} strokeWidth={1.5} strokeLinecap="round" />
		<line x1={10} y1={10} x2={14} y2={10} stroke={color} strokeWidth={1.5} strokeLinecap="round" />
		<circle cx={10} cy={10} r={1} fill={color} />
	</svg>
);

export const ResearchCallout: React.FC<ResearchCalloutProps> = ({
	x,
	y,
	width,
	height,
	mainText,
	subText,
	source,
	iconType,
	appearFrame,
}) => {
	const frame = useCurrentFrame();

	// Slide-in from right
	const slideX = interpolate(
		frame,
		[appearFrame, appearFrame + TIMING.calloutSlideDuration],
		[30, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.cubic),
		},
	);

	const fadeIn = interpolate(
		frame,
		[appearFrame, appearFrame + TIMING.calloutSlideDuration],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.cubic),
		},
	);

	// Pulse effect on main text after slide-in completes
	const pulseStart = appearFrame + TIMING.calloutPulseDelay;
	const pulseScale = interpolate(
		frame,
		[pulseStart, pulseStart + TIMING.calloutPulseDuration / 2, pulseStart + TIMING.calloutPulseDuration],
		[1.0, 1.05, 1.0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.inOut(Easing.sin),
		},
	);

	if (frame < appearFrame) {
		return null;
	}

	const Icon = iconType === 'bar_chart' ? BarChartIcon : ClockIcon;

	return (
		<div
			style={{
				position: 'absolute',
				left: x - width / 2 + slideX,
				top: y - height / 2,
				width,
				height,
				backgroundColor: `rgba(30, 41, 59, 0.4)`,
				border: `1px solid rgba(51, 65, 85, 0.2)`,
				borderRadius: 8,
				opacity: fadeIn,
				display: 'flex',
				alignItems: 'center',
				padding: '0 16px',
				gap: 12,
				boxSizing: 'border-box',
			}}
		>
			<Icon color={COLORS.maintenance} />
			<div style={{ display: 'flex', flexDirection: 'column', gap: 2 }}>
				<div
					style={{
						fontFamily: 'Inter, sans-serif',
						fontSize: 16,
						fontWeight: 600,
						color: COLORS.calloutMain,
						transform: `scale(${pulseScale})`,
						transformOrigin: 'left center',
						whiteSpace: 'nowrap',
					}}
				>
					{mainText}
				</div>
				<div
					style={{
						fontFamily: 'Inter, sans-serif',
						fontSize: 11,
						color: COLORS.calloutSub,
						opacity: 0.5,
						whiteSpace: 'nowrap',
					}}
				>
					{subText}
				</div>
				<div
					style={{
						fontFamily: 'Inter, sans-serif',
						fontSize: 9,
						color: COLORS.calloutSource,
						opacity: 0.3,
						whiteSpace: 'nowrap',
					}}
				>
					{source}
				</div>
			</div>
		</div>
	);
};

export default ResearchCallout;
