import React from 'react';
import {
	AbsoluteFill,
	OffthreadVideo,
	staticFile,
} from 'remotion';
import { useVisualContractData, useVisualMediaSrc } from '../_shared/visual-runtime';
import { COLORS, resolveWaveOverlayBadges } from './constants';
import { GradientOverlay } from './GradientOverlay';
import { GridOverlay } from './GridOverlay';
import { WaveformGraph } from './WaveformGraph';
import { StatBadge } from './StatBadge';

export const VeoSection03WaveDataOverlay: React.FC = () => {
	const backgroundSrc = useVisualMediaSrc('backgroundSrc', 'veo/04_veo_broll.mp4');
	const contractData = useVisualContractData<Record<string, unknown>>();
	const badges = resolveWaveOverlayBadges(contractData);

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

			{/* Stat badges distributed across the lower data area */}
			{badges.map((badge, index) => (
				<StatBadge
					key={`${badge.label}-${index}`}
					label={badge.label}
					value={badge.value}
					icon={badge.icon}
					index={index}
					x={badge.x}
					y={badge.y}
				/>
			))}
		</AbsoluteFill>
	);
};

export const defaultVeoSection03WaveDataOverlayProps = {};

export default VeoSection03WaveDataOverlay;
