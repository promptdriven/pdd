import React from 'react';
import { useCurrentFrame, interpolate, spring } from 'remotion';
import { COLORS, ANIMATION_TIMING, type WaveDataOverlayLayout } from './constants';

interface AccentDotsProps {
	layout: WaveDataOverlayLayout;
}

export const AccentDots: React.FC<AccentDotsProps> = ({ layout }) => {
	const frame = useCurrentFrame();
	const { dots, wave } = layout;

	return (
		<>
			{dots.positions.map((x) => {
				// Calculate Y position on the sine wave crest
				const y =
					wave.centerY +
					wave.amplitude * Math.sin((2 * Math.PI * x) / wave.wavelength);

				// easeOutBack scale-in using spring (approximates easeOutBack overshoot)
				const scaleProgress = spring({
					frame: frame - ANIMATION_TIMING.dotsScaleStart,
					fps: 30,
					config: {
						damping: 10,
						stiffness: 150,
						mass: 0.5,
						overshootClamping: false,
					},
				});

				const scale =
					frame < ANIMATION_TIMING.dotsScaleStart ? 0 : scaleProgress;

				return (
					<div
						key={x}
						style={{
							position: 'absolute',
							left: x - dots.radius,
							top: y - dots.radius,
							width: dots.radius * 2,
							height: dots.radius * 2,
							borderRadius: '50%',
							backgroundColor: COLORS.accentDot,
							transform: `scale(${scale})`,
						}}
					/>
				);
			})}
		</>
	);
};
