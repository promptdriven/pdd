import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import { AnimatedDivider } from "./AnimatedDivider";
import { TitleText } from "./TitleText";
import { SubtitleText } from "./SubtitleText";
import { AccentParticles } from "./AccentParticles";
import { VignetteOverlay } from "./VignetteOverlay";

const BG_COLOR = "#0A1628";
const ACCENT_BLUE = "#3B82F6";
const COMP_WIDTH = 1920;
const COMP_HEIGHT = 1080;

export const defaultColdOpen10WhyThisMattersProps = {};

/**
 * ColdOpen10WhyThisMatters – a transition overlay / title card.
 *
 * Renders a dark navy backdrop with an expanding accent divider,
 * animated title ("Why This Matters"), a subtitle tagline,
 * drifting accent particles, and a vignette overlay.
 * Everything fades out cleanly in the final 30 frames.
 */
export const ColdOpen10WhyThisMatters: React.FC = () => {
	const frame = useCurrentFrame();

	// Subtle radial glow behind the center that pulses gently
	const glowScale = interpolate(
		frame,
		[0, 30, 60, 90, 120],
		[0.8, 1, 1.05, 0.98, 1.02],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	const glowOpacity = interpolate(
		frame,
		[0, 8, 120, 150],
		[0.15, 0.25, 0.25, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		}
	);

	return (
		<AbsoluteFill
			style={{
				backgroundColor: BG_COLOR,
				overflow: "hidden",
			}}
		>
			{/* Central radial glow */}
			<div
				style={{
					position: "absolute",
					top: COMP_HEIGHT / 2 - 300,
					left: COMP_WIDTH / 2 - 300,
					width: 600,
					height: 600,
					borderRadius: "50%",
					background: `radial-gradient(circle, ${ACCENT_BLUE}40 0%, transparent 70%)`,
					opacity: glowOpacity,
					transform: `scale(${glowScale})`,
				}}
			/>

			{/* Floating accent particles */}
			<AccentParticles />

			{/* Expanding horizontal divider */}
			<AnimatedDivider />

			{/* Main title */}
			<TitleText />

			{/* Subtitle tagline */}
			<SubtitleText />

			{/* Edge vignette */}
			<VignetteOverlay />
		</AbsoluteFill>
	);
};

export default ColdOpen10WhyThisMatters;
