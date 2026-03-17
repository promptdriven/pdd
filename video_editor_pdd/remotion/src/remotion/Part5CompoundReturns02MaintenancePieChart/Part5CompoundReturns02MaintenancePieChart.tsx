import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, CALLOUTS, TIMING } from './constants';
import { DonutChart } from './DonutChart';
import { ResearchCallout } from './ResearchCallout';

export const defaultPart5CompoundReturns02MaintenancePieChartProps = {};

export const Part5CompoundReturns02MaintenancePieChart: React.FC = () => {
	return (
		<AbsoluteFill
			style={{
				backgroundColor: COLORS.background,
				fontFamily: 'Inter, sans-serif',
			}}
		>
			{/* Title */}
			<div
				style={{
					position: 'absolute',
					top: 60,
					left: 0,
					right: 0,
					textAlign: 'center',
					fontFamily: 'Inter, sans-serif',
					fontSize: 28,
					fontWeight: 700,
					color: COLORS.calloutMain,
					letterSpacing: 1,
				}}
			>
				Where the Money Goes
			</div>

			{/* Donut Chart (SVG-based, handles its own animation) */}
			<DonutChart />

			{/* McKinsey Callout */}
			<ResearchCallout
				x={CALLOUTS.mckinsey.x}
				y={CALLOUTS.mckinsey.y}
				width={CALLOUTS.mckinsey.width}
				height={CALLOUTS.mckinsey.height}
				mainText={CALLOUTS.mckinsey.mainText}
				subText={CALLOUTS.mckinsey.subText}
				source={CALLOUTS.mckinsey.source}
				iconType={CALLOUTS.mckinsey.iconType}
				appearFrame={TIMING.mckinseyStart}
			/>

			{/* Stripe Callout */}
			<ResearchCallout
				x={CALLOUTS.stripe.x}
				y={CALLOUTS.stripe.y}
				width={CALLOUTS.stripe.width}
				height={CALLOUTS.stripe.height}
				mainText={CALLOUTS.stripe.mainText}
				subText={CALLOUTS.stripe.subText}
				source={CALLOUTS.stripe.source}
				iconType={CALLOUTS.stripe.iconType}
				appearFrame={TIMING.stripeStart}
			/>
		</AbsoluteFill>
	);
};

export default Part5CompoundReturns02MaintenancePieChart;
