import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
	TERMINAL_FADE_START,
	TERMINAL_FADE_DURATION,
	TERMINAL_COLOR,
	TERMINAL_FONT_SIZE,
	TERMINAL_X,
	TERMINAL_Y,
	CODE_FONT,
} from "./constants";

export const TerminalSnippet: React.FC = () => {
	const frame = useCurrentFrame();

	const opacity = interpolate(
		frame,
		[TERMINAL_FADE_START, TERMINAL_FADE_START + TERMINAL_FADE_DURATION],
		[0, 0.4],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);

	if (opacity <= 0) return null;

	return (
		<div
			style={{
				position: "absolute",
				left: TERMINAL_X,
				top: TERMINAL_Y,
				opacity,
				display: "flex",
				alignItems: "center",
				gap: 6,
			}}
		>
			<span
				style={{
					fontFamily: CODE_FONT,
					fontSize: TERMINAL_FONT_SIZE,
					color: "#6E7681",
				}}
			>
				$
			</span>
			<span
				style={{
					fontFamily: CODE_FONT,
					fontSize: TERMINAL_FONT_SIZE,
					color: TERMINAL_COLOR,
				}}
			>
				pdd generate
			</span>
			<span
				style={{
					fontFamily: CODE_FONT,
					fontSize: TERMINAL_FONT_SIZE + 2,
					color: TERMINAL_COLOR,
					marginLeft: 4,
				}}
			>
				✓
			</span>
		</div>
	);
};

export default TerminalSnippet;
