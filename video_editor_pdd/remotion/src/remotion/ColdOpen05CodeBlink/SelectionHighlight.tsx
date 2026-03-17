import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
	SELECTION_COLOR,
	SELECTION_START,
	SELECTION_END,
	LINE_HEIGHT,
} from "./constants";

interface SelectionHighlightProps {
	lineCount: number;
}

export const SelectionHighlight: React.FC<SelectionHighlightProps> = ({
	lineCount,
}) => {
	const frame = useCurrentFrame();

	// Selection sweeps from top to bottom over 15 frames
	const sweepProgress = interpolate(
		frame,
		[SELECTION_START, SELECTION_END],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.quad),
		},
	);

	if (sweepProgress <= 0) return null;

	const totalHeight = lineCount * LINE_HEIGHT;
	const revealedHeight = sweepProgress * totalHeight;

	return (
		<div
			style={{
				position: "absolute",
				left: 0,
				top: 0,
				width: "100%",
				height: revealedHeight,
				backgroundColor: SELECTION_COLOR,
				opacity: 0.2,
				pointerEvents: "none",
			}}
		/>
	);
};

export default SelectionHighlight;
