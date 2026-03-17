import React from 'react';
import {
	AbsoluteFill,
	Sequence,
	useCurrentFrame,
	interpolateColors,
	interpolate,
	Easing,
} from 'remotion';
import {
	BG_START,
	BG_END,
	DURATION_FRAMES,
	NODES,
	THESIS_APPEAR_FRAME,
} from './constants';
import {ParticleField} from './ParticleField';
import {TriangleGlow} from './TriangleGlow';
import {AnimatedNode} from './AnimatedNode';
import {CodeLines} from './CodeLines';
import {ThesisText} from './ThesisText';

export const defaultClosing06MoldGlowFinaleProps = {};

export const Closing06MoldGlowFinale: React.FC = () => {
	const frame = useCurrentFrame();

	// Background darkening: #0A1225 → #080E1A over first 60 frames
	const bgProgress = interpolate(frame, [0, 60], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.inOut(Easing.sin),
	});
	const backgroundColor = interpolateColors(
		bgProgress,
		[0, 1],
		[BG_START, BG_END]
	);

	return (
		<AbsoluteFill style={{backgroundColor}}>
			{/* Particle field — atmospheric, spawns from frame 0 */}
			<ParticleField />

			{/* Code lines — start visible, dim from frame 30 */}
			<Sequence from={30} durationInFrames={DURATION_FRAMES - 30}>
				<CodeLines />
			</Sequence>

			{/* Triangle edges with multi-layer glow — from frame 0 */}
			<TriangleGlow />

			{/* Nodes — radiant growth starting at frame 30 */}
			<Sequence from={30} durationInFrames={DURATION_FRAMES - 30}>
				{NODES.map((node) => (
					<AnimatedNode
						key={node.label}
						center={node.center}
						fillFrom={node.fillFrom}
						fillTo={node.fillTo}
						glowColor={node.glowColor}
					/>
				))}
			</Sequence>

			{/* Thesis text — appears at frame 130 */}
			<Sequence from={THESIS_APPEAR_FRAME} durationInFrames={DURATION_FRAMES - THESIS_APPEAR_FRAME}>
				<ThesisText />
			</Sequence>
		</AbsoluteFill>
	);
};

export default Closing06MoldGlowFinale;
