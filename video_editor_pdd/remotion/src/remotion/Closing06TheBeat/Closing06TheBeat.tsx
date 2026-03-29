import React from 'react';
import {AbsoluteFill, useCurrentFrame, interpolate} from 'remotion';
import {
	BG_START,
	BG_END,
	BG_DARKEN_START,
	BG_DARKEN_END,
} from './constants';
import {HorizontalRule} from './HorizontalRule';

export const defaultClosing06TheBeatProps = {};

/**
 * Hex color string to [r, g, b] tuple.
 */
function hexToRgb(hex: string): [number, number, number] {
	const n = parseInt(hex.replace('#', ''), 16);
	return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

function lerpColor(a: string, b: string, t: number): string {
	const [r1, g1, b1] = hexToRgb(a);
	const [r2, g2, b2] = hexToRgb(b);
	const r = Math.round(r1 + (r2 - r1) * t);
	const g = Math.round(g1 + (g2 - g1) * t);
	const bl = Math.round(b1 + (b2 - b1) * t);
	return `rgb(${r},${g},${bl})`;
}

/**
 * Section 7.6 — "The Beat"
 *
 * A deliberate 2-second pause. The screen holds on deep navy, a barely visible
 * horizontal rule appears at center, then everything fades to true black.
 * No narration, no typography — just negative space.
 */
export const Closing06TheBeat: React.FC = () => {
	const frame = useCurrentFrame();

	// Background: hold #0A0F1A for frames 0-29, then linearly fade to #000000
	// over frames 30-60.
	const bgProgress = interpolate(frame, [BG_DARKEN_START, BG_DARKEN_END], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	const backgroundColor = lerpColor(BG_START, BG_END, bgProgress);

	return (
		<AbsoluteFill
			style={{
				backgroundColor,
			}}
		>
			<HorizontalRule />
		</AbsoluteFill>
	);
};

export default Closing06TheBeat;
