import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, type WaveDataOverlayLayout } from './constants';

interface StatCalloutProps {
	icon: 'film-reel' | 'sparkle';
	label: string;
	color: string;
	y: number;
	fadeStart: number;
	fadeEnd: number;
	layout: WaveDataOverlayLayout;
}

const FilmReelIcon: React.FC<{ color: string; size: number }> = ({
	color,
	size,
}) => (
	<svg
		width={size}
		height={size}
		viewBox="0 0 24 24"
		fill="none"
		style={{ flexShrink: 0 }}
	>
		<circle cx="12" cy="12" r="10" stroke={color} strokeWidth="2" />
		<circle cx="12" cy="12" r="3" fill={color} />
		<circle cx="12" cy="5" r="1.5" fill={color} />
		<circle cx="12" cy="19" r="1.5" fill={color} />
		<circle cx="5" cy="12" r="1.5" fill={color} />
		<circle cx="19" cy="12" r="1.5" fill={color} />
	</svg>
);

const SparkleIcon: React.FC<{ color: string; size: number }> = ({
	color,
	size,
}) => (
	<svg
		width={size}
		height={size}
		viewBox="0 0 24 24"
		fill="none"
		style={{ flexShrink: 0 }}
	>
		<path
			d="M12 2L13.5 8.5L20 10L13.5 11.5L12 18L10.5 11.5L4 10L10.5 8.5L12 2Z"
			fill={color}
		/>
		<path
			d="M19 14L19.75 16.25L22 17L19.75 17.75L19 20L18.25 17.75L16 17L18.25 16.25L19 14Z"
			fill={color}
		/>
	</svg>
);

export const StatCallout: React.FC<StatCalloutProps> = ({
	icon,
	label,
	color,
	y,
	fadeStart,
	fadeEnd,
	layout,
}) => {
	const frame = useCurrentFrame();
	const { statX, typography } = layout;

	// Fade in with easeOutCubic
	const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	// Slide up 8px with easeOutCubic
	const translateY = interpolate(frame, [fadeStart, fadeEnd], [8, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	return (
		<div
			style={{
				position: 'absolute',
				left: statX,
				top: y,
				display: 'flex',
				alignItems: 'center',
				gap: 12,
				opacity,
				transform: `translateY(${translateY}px)`,
			}}
		>
			{icon === 'film-reel' ? (
				<FilmReelIcon color={color} size={typography.iconSize} />
			) : (
				<SparkleIcon color={color} size={typography.iconSize} />
			)}
			<span
				style={{
					fontFamily: typography.labelFontFamily,
					fontSize: typography.labelFontSize,
					fontWeight: typography.labelFontWeight,
					color: COLORS.labelText,
					whiteSpace: 'nowrap',
				}}
			>
				{label}
			</span>
		</div>
	);
};
