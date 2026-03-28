import React from 'react';
import { AbsoluteFill } from 'remotion';
import { BackgroundFade } from './BackgroundFade';
import { HorizontalRule } from './HorizontalRule';
import { BG_DEEP_NAVY } from './constants';

/**
 * Section 7.6: The Beat
 *
 * A deliberate pause — the visual equivalent of a period at the end of a sentence.
 * Deep navy fading to true black with a barely-visible horizontal rule that
 * appears and dissolves at center screen.
 *
 * Duration: 60 frames @ 30fps (2 seconds)
 * No narration, no typography — just negative space.
 */
export const defaultClosing06TheBeatProps = {};

export const Closing06TheBeat: React.FC = () => {
	return (
		<AbsoluteFill
			style={{
				backgroundColor: BG_DEEP_NAVY,
				width: 1920,
				height: 1080,
			}}
		>
			{/* Background: deep navy → true black (linear, frames 30-60) */}
			<BackgroundFade />

			{/* Thin horizontal rule: fades in frames 15-30, fades out frames 45-60 */}
			<HorizontalRule />
		</AbsoluteFill>
	);
};

export default Closing06TheBeat;
