import React from "react";
import { useCurrentFrame } from "remotion";
import { CURSOR_BLINK_RATE, CODE_FONT_SIZE, LINE_HEIGHT } from "./constants";

interface CursorBlinkProps {
	lineIndex?: number;
	colOffset?: number;
}

export const CursorBlink: React.FC<CursorBlinkProps> = ({
	lineIndex = 0,
	colOffset = 0,
}) => {
	const frame = useCurrentFrame();
	const blinkCycle = Math.floor(frame / CURSOR_BLINK_RATE) % 2;
	const visible = blinkCycle === 0;

	return (
		<div
			style={{
				position: "absolute",
				left: 64 + colOffset,
				top: lineIndex * LINE_HEIGHT,
				width: 2,
				height: CODE_FONT_SIZE + 2,
				backgroundColor: "#C9D1D9",
				opacity: visible ? 0.8 : 0,
			}}
		/>
	);
};

export default CursorBlink;
