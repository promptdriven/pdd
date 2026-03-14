import React from 'react';
import {
	AbsoluteFill,
	useCurrentFrame,
	interpolate,
	Easing,
	useVideoConfig,
} from 'remotion';
import {
	COLORS,
	ANIMATION_TIMING,
	resolveWaveDataOverlayLayout,
} from './constants';
import { GradientOverlay } from './GradientOverlay';
import { SineWavePath } from './SineWavePath';
import { AccentDots } from './AccentDots';
import { StatCallout } from './StatCallout';

export const VeoSection03WaveDataOverlay: React.FC = () => {
	const frame = useCurrentFrame();
	const { width, height } = useVideoConfig();
	const layout = resolveWaveDataOverlayLayout(width, height);

	// Final fade-out with easeInQuad (last 15 frames)
	const compositionOpacity = interpolate(
		frame,
		[ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
		[1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.in(Easing.quad),
		},
	);

	return (
		<AbsoluteFill
			style={{
				backgroundColor: '#00FF00',
				width,
				height,
			}}
		>
			<div style={{ opacity: compositionOpacity }}>
				<GradientOverlay width={layout.width} height={layout.height} />
				<SineWavePath layout={layout} />
				<AccentDots layout={layout} />
				<StatCallout
					icon={layout.statCallouts[0].icon}
					label={layout.statCallouts[0].label}
					color={layout.statCallouts[0].color}
					y={layout.statCallouts[0].y}
					fadeStart={ANIMATION_TIMING.stat1FadeStart}
					fadeEnd={ANIMATION_TIMING.stat1FadeEnd}
					layout={layout}
				/>
				<StatCallout
					icon={layout.statCallouts[1].icon}
					label={layout.statCallouts[1].label}
					color={layout.statCallouts[1].color}
					y={layout.statCallouts[1].y}
					fadeStart={ANIMATION_TIMING.stat2FadeStart}
					fadeEnd={ANIMATION_TIMING.stat2FadeEnd}
					layout={layout}
				/>
			</div>
		</AbsoluteFill>
	);
};

export const defaultVeoSection03WaveDataOverlayProps = {};

export default VeoSection03WaveDataOverlay;
