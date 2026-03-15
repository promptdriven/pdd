import React from 'react';
import {
	AbsoluteFill,
	OffthreadVideo,
	staticFile,
} from 'remotion';
import { useVisualMediaSrc } from '../_shared/visual-runtime';
import { COLORS, DATA } from './constants';
import { GradientOverlay } from './GradientOverlay';
import { GridOverlay } from './GridOverlay';
import { WaveformGraph } from './WaveformGraph';
import { StatBadge } from './StatBadge';

export const VeoSection03WaveDataOverlay: React.FC = () => {
	const backgroundSrc = useVisualMediaSrc('backgroundSrc', 'veo/04_veo_broll.mp4');

	return (
		<AbsoluteFill style={{ backgroundColor: COLORS.background }}>
			{/* Background Veo footage */}
			{backgroundSrc ? (
				<AbsoluteFill>
					<OffthreadVideo
						src={staticFile(backgroundSrc)}
						style={{
							width: '100%',
							height: '100%',
							objectFit: 'cover',
						}}
						startFrom={52}
						muted
					/>
				</AbsoluteFill>
			) : null}

			{/* Gradient overlay fading from transparent to dark at bottom */}
			<GradientOverlay />

			{/* Grid lines at 25% intervals */}
			<GridOverlay />

			{/* Sinusoidal waveform in lower third */}
			<WaveformGraph />

			{/* Stat badges staggering in from the right */}
			<StatBadge
				label={DATA.waveHeight.label}
				value={DATA.waveHeight.value}
				icon="wave"
				index={0}
			/>
			<StatBadge
				label={DATA.wavePeriod.label}
				value={DATA.wavePeriod.value}
				icon="clock"
				index={1}
			/>
			<StatBadge
				label={DATA.waterTemp.label}
				value={DATA.waterTemp.value}
				icon="thermometer"
				index={2}
			/>
		</AbsoluteFill>
	);
};

export const defaultVeoSection03WaveDataOverlayProps = {};

export default VeoSection03WaveDataOverlay;
