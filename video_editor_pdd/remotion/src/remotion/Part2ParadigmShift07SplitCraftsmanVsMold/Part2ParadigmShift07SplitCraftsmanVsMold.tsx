import React from 'react';
import {
	AbsoluteFill,
	useCurrentFrame,
	interpolate,
	Easing,
	OffthreadVideo,
	staticFile,
} from 'remotion';
import AuraGlow from './AuraGlow';
import PartDissolveReappear from './PartDissolveReappear';
import {
	CANVAS_WIDTH,
	CANVAS_HEIGHT,
	BG_COLOR,
	DIVIDER_COLOR,
	DIVIDER_OPACITY,
	DIVIDER_WIDTH_PX,
	DIVIDER_GAP,
	PANEL_WIDTH,
	AURA_AMBER,
	AURA_BLUE,
	FADE_IN_START,
	FADE_IN_END,
	FADE_OUT_START,
	FADE_OUT_END,
	LEFT_LABEL,
	RIGHT_LABEL,
	LABEL_FONT_SIZE,
	LABEL_PRIMARY_OPACITY,
} from './constants';

export const defaultPart2ParadigmShift07SplitCraftsmanVsMoldProps = {};

export const Part2ParadigmShift07SplitCraftsmanVsMold: React.FC = () => {
	const frame = useCurrentFrame();

	// Global fade-in from black (easeOutQuad, 15 frames)
	const fadeIn = interpolate(frame, [FADE_IN_START, FADE_IN_END], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// Global fade-out to black (last 30 frames)
	const fadeOut = interpolate(frame, [FADE_OUT_START, FADE_OUT_END], [1, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.in(Easing.quad),
	});

	const globalOpacity = Math.min(fadeIn, fadeOut);

	// Divider fade (same as global fade-in for first 15 frames)
	const dividerOpacity = interpolate(
		frame,
		[FADE_IN_START, FADE_IN_END],
		[0, DIVIDER_OPACITY],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
			easing: Easing.out(Easing.quad),
		},
	);

	// Label fade-in: appears after panels are established (frame 30-60)
	const labelOpacity = interpolate(frame, [30, 60], [0, LABEL_PRIMARY_OPACITY], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// Label fade-out with global
	const labelFadeOut = interpolate(
		frame,
		[FADE_OUT_START, FADE_OUT_END],
		[1, 0],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		},
	);

	const finalLabelOpacity = labelOpacity * labelFadeOut;

	const leftVideoSrc = staticFile('veo/craftsman_carving.mp4');
	const rightVideoSrc = staticFile('veo/mold_plastic_flow.mp4');

	return (
		<AbsoluteFill
			style={{
				backgroundColor: BG_COLOR,
				width: CANVAS_WIDTH,
				height: CANVAS_HEIGHT,
			}}
		>
			<div
				style={{
					position: 'absolute',
					top: 0,
					left: 0,
					width: '100%',
					height: '100%',
					opacity: globalOpacity,
					display: 'flex',
					flexDirection: 'row',
					alignItems: 'center',
					justifyContent: 'center',
				}}
			>
				{/* Left Panel — Craftsman */}
				<div
					style={{
						position: 'relative',
						width: PANEL_WIDTH,
						height: CANVAS_HEIGHT,
						overflow: 'hidden',
					}}
				>
					<OffthreadVideo
						src={leftVideoSrc}
						style={{
							width: '100%',
							height: '100%',
							objectFit: 'cover',
						}}
						muted
					/>

					{/* Amber aura on the object (lower region = chair) */}
					<AuraGlow
						color={AURA_AMBER}
						position="lower"
						radiusX={42}
						radiusY={32}
					/>

					{/* Left label */}
					<div
						style={{
							position: 'absolute',
							bottom: 40,
							left: 0,
							width: '100%',
							display: 'flex',
							justifyContent: 'center',
							pointerEvents: 'none',
						}}
					>
						<span
							style={{
								fontFamily:
									'Inter, SF Pro Display, -apple-system, sans-serif',
								fontSize: LABEL_FONT_SIZE,
								fontWeight: 600,
								color: '#FFFFFF',
								opacity: finalLabelOpacity,
								textShadow: '0 2px 8px rgba(0,0,0,0.7)',
								letterSpacing: '0.02em',
								padding: '6px 16px',
								backgroundColor: 'rgba(0,0,0,0.35)',
								borderRadius: 6,
							}}
						>
							{LEFT_LABEL}
						</span>
					</div>
				</div>

				{/* Center Divider */}
				<div
					style={{
						width: DIVIDER_GAP,
						height: CANVAS_HEIGHT,
						display: 'flex',
						alignItems: 'center',
						justifyContent: 'center',
						flexShrink: 0,
					}}
				>
					<div
						style={{
							width: DIVIDER_WIDTH_PX,
							height: '100%',
							backgroundColor: DIVIDER_COLOR,
							opacity: dividerOpacity,
						}}
					/>
				</div>

				{/* Right Panel — Injection Mold */}
				<div
					style={{
						position: 'relative',
						width: PANEL_WIDTH,
						height: CANVAS_HEIGHT,
						overflow: 'hidden',
					}}
				>
					<OffthreadVideo
						src={rightVideoSrc}
						style={{
							width: '100%',
							height: '100%',
							objectFit: 'cover',
						}}
						muted
					/>

					{/* Blue aura on the mold (center region = the mold itself) */}
					<AuraGlow
						color={AURA_BLUE}
						position="center"
						radiusX={45}
						radiusY={35}
					/>

					{/* Part dissolve/reappear effect */}
					<PartDissolveReappear />

					{/* Right label */}
					<div
						style={{
							position: 'absolute',
							bottom: 40,
							left: 0,
							width: '100%',
							display: 'flex',
							justifyContent: 'center',
							pointerEvents: 'none',
						}}
					>
						<span
							style={{
								fontFamily:
									'Inter, SF Pro Display, -apple-system, sans-serif',
								fontSize: LABEL_FONT_SIZE,
								fontWeight: 600,
								color: '#FFFFFF',
								opacity: finalLabelOpacity,
								textShadow: '0 2px 8px rgba(0,0,0,0.7)',
								letterSpacing: '0.02em',
								padding: '6px 16px',
								backgroundColor: 'rgba(0,0,0,0.35)',
								borderRadius: 6,
							}}
						>
							{RIGHT_LABEL}
						</span>
					</div>
				</div>
			</div>
		</AbsoluteFill>
	);
};

export default Part2ParadigmShift07SplitCraftsmanVsMold;
