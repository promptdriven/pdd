import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, BADGE, TYPOGRAPHY, ANIMATION } from './constants';

interface StatBadgeProps {
	label: string;
	value: string;
	icon: 'wave' | 'clock' | 'thermometer';
	index: number;
}

const WaveIcon: React.FC<{ size: number }> = ({ size }) => (
	<svg width={size} height={size} viewBox="0 0 24 24" fill="none">
		<path
			d="M2 12C4 8 6 16 8 12C10 8 12 16 14 12C16 8 18 16 20 12C21 10 22 12 22 12"
			stroke={COLORS.goldAccent}
			strokeWidth="2"
			strokeLinecap="round"
		/>
	</svg>
);

const ClockIcon: React.FC<{ size: number }> = ({ size }) => (
	<svg width={size} height={size} viewBox="0 0 24 24" fill="none">
		<circle cx="12" cy="12" r="9" stroke={COLORS.goldAccent} strokeWidth="2" />
		<path d="M12 7V12L15 15" stroke={COLORS.goldAccent} strokeWidth="2" strokeLinecap="round" />
	</svg>
);

const ThermometerIcon: React.FC<{ size: number }> = ({ size }) => (
	<svg width={size} height={size} viewBox="0 0 24 24" fill="none">
		<path
			d="M14 14.76V3.5C14 2.67 13.33 2 12.5 2H11.5C10.67 2 10 2.67 10 3.5V14.76C8.79 15.56 8 16.92 8 18.5C8 20.99 10.01 23 12.5 23C14.99 23 17 20.99 17 18.5C17 16.92 16.21 15.56 15 14.76"
			stroke={COLORS.goldAccent}
			strokeWidth="1.5"
			strokeLinecap="round"
		/>
		<circle cx="12.5" cy="18.5" r="2" fill={COLORS.goldAccent} />
		<path d="M12.5 15V7" stroke={COLORS.goldAccent} strokeWidth="1.5" strokeLinecap="round" />
	</svg>
);

const ICONS = {
	wave: WaveIcon,
	clock: ClockIcon,
	thermometer: ThermometerIcon,
};

export const StatBadge: React.FC<StatBadgeProps> = ({
	label,
	value,
	icon,
	index,
}) => {
	const frame = useCurrentFrame();

	const badgeStarts = [ANIMATION.badge1Start, ANIMATION.badge2Start, ANIMATION.badge3Start];
	const badgeEnds = [ANIMATION.badge1End, ANIMATION.badge2End, ANIMATION.badge3End];
	const startFrame = badgeStarts[index];
	const endFrame = badgeEnds[index];

	const opacity = interpolate(frame, [startFrame, endFrame], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	const translateX = interpolate(frame, [startFrame, endFrame], [40, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	const IconComponent = ICONS[icon];
	const top = BADGE.topStart + index * (BADGE.height + BADGE.gap);

	return (
		<div
			style={{
				position: 'absolute',
				right: BADGE.rightOffset,
				top,
				width: BADGE.width,
				height: BADGE.height,
				borderRadius: BADGE.borderRadius,
				backgroundColor: COLORS.badgeBackground,
				border: `1px solid ${COLORS.badgeBorder}`,
				display: 'flex',
				alignItems: 'center',
				padding: '0 14px',
				gap: 10,
				opacity,
				transform: `translateX(${translateX}px)`,
			}}
		>
			<IconComponent size={20} />
			<div style={{ display: 'flex', flexDirection: 'column', gap: 1 }}>
				<span
					style={{
						fontFamily: TYPOGRAPHY.labelFontFamily,
						fontSize: TYPOGRAPHY.labelFontSize,
						fontWeight: TYPOGRAPHY.labelFontWeight,
						color: COLORS.labelText,
						lineHeight: 1.2,
					}}
				>
					{label}
				</span>
				<span
					style={{
						fontFamily: TYPOGRAPHY.labelFontFamily,
						fontSize: TYPOGRAPHY.valueFontSize,
						fontWeight: TYPOGRAPHY.valueFontWeight,
						color: COLORS.valueText,
						lineHeight: 1.2,
					}}
				>
					{value}
				</span>
			</div>
		</div>
	);
};
