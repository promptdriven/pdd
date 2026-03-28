import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate } from 'remotion';
import {
	BG_DEEP_NAVY,
	BG_TRUE_BLACK,
	BG_DARKEN_START,
	BG_DARKEN_DURATION,
} from './constants';

/**
 * Interpolates a hex color string between two hex values.
 * Only handles simple 6-digit hex codes (#RRGGBB).
 */
function lerpHexColor(from: string, to: string, t: number): string {
	const parseHex = (hex: string) => {
		const h = hex.replace('#', '');
		return {
			r: parseInt(h.substring(0, 2), 16),
			g: parseInt(h.substring(2, 4), 16),
			b: parseInt(h.substring(4, 6), 16),
		};
	};

	const f = parseHex(from);
	const toC = parseHex(to);

	const r = Math.round(f.r + (toC.r - f.r) * t);
	const g = Math.round(f.g + (toC.g - f.g) * t);
	const b = Math.round(f.b + (toC.b - f.b) * t);

	const toHex = (n: number) => n.toString(16).padStart(2, '0');
	return `#${toHex(r)}${toHex(g)}${toHex(b)}`;
}

/**
 * Full-screen background that transitions from deep navy to true black.
 * Holds navy for frames 0-30, then linearly darkens from frame 30-60.
 */
export const BackgroundFade: React.FC = () => {
	const frame = useCurrentFrame();

	// Linear transition from navy to black, frames 30-60
	const progress = interpolate(
		frame,
		[BG_DARKEN_START, BG_DARKEN_START + BG_DARKEN_DURATION],
		[0, 1],
		{
			extrapolateLeft: 'clamp',
			extrapolateRight: 'clamp',
		}
	);

	const bgColor = lerpHexColor(BG_DEEP_NAVY, BG_TRUE_BLACK, progress);

	return (
		<AbsoluteFill
			style={{
				backgroundColor: bgColor,
			}}
		/>
	);
};

export default BackgroundFade;
