import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
	TERMINAL_BG,
	TERMINAL_BORDER,
	TERMINAL_TEXT,
	TERMINAL_COMMANDS,
	MONO_FONT,
} from './constants';

const TERMINAL_WIDTH = 320;
const TERMINAL_HEIGHT = 140;
const TERMINAL_X = 1920 - TERMINAL_WIDTH - 80; // ~1520
const TERMINAL_Y = 1080 - TERMINAL_HEIGHT - 60; // ~880

interface TerminalOverlayProps {
	/** Frame offset within the terminal's Sequence (0 = terminal appears) */
	entryFrame: number;
}

const TerminalOverlay: React.FC<TerminalOverlayProps> = ({ entryFrame }) => {
	const globalFrame = useCurrentFrame();
	const localFrame = globalFrame - entryFrame;

	if (localFrame < 0) return null;

	// Slide-in animation
	const slideY = interpolate(localFrame, [0, 15], [20, 0], {
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	const fadeIn = interpolate(localFrame, [0, 15], [0, 1], {
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.cubic),
	});

	return (
		<div
			style={{
				position: 'absolute',
				left: TERMINAL_X,
				top: TERMINAL_Y + slideY,
				width: TERMINAL_WIDTH,
				height: TERMINAL_HEIGHT,
				backgroundColor: TERMINAL_BG,
				border: `1px solid ${TERMINAL_BORDER}`,
				borderRadius: 6,
				padding: '10px 12px',
				opacity: fadeIn,
				overflow: 'hidden',
				boxSizing: 'border-box',
			}}
		>
			{/* Title bar dots */}
			<div
				style={{
					display: 'flex',
					gap: 5,
					marginBottom: 8,
				}}
			>
				<div
					style={{
						width: 6,
						height: 6,
						borderRadius: '50%',
						backgroundColor: '#EF4444',
						opacity: 0.6,
					}}
				/>
				<div
					style={{
						width: 6,
						height: 6,
						borderRadius: '50%',
						backgroundColor: '#F59E0B',
						opacity: 0.6,
					}}
				/>
				<div
					style={{
						width: 6,
						height: 6,
						borderRadius: '50%',
						backgroundColor: '#22C55E',
						opacity: 0.6,
					}}
				/>
			</div>

			{/* Terminal lines */}
			{TERMINAL_COMMANDS.map((cmd, idx) => {
				const lineFrame = localFrame - cmd.delay;
				if (lineFrame < 0) return null;

				const lineFade = interpolate(lineFrame, [0, 8], [0, 1], {
					extrapolateRight: 'clamp',
				});

				return (
					<div
						key={idx}
						style={{
							fontFamily: MONO_FONT,
							fontSize: 10,
							color: cmd.color,
							opacity: lineFade * 0.85,
							lineHeight: '16px',
							whiteSpace: 'nowrap',
							overflow: 'hidden',
						}}
					>
						{cmd.text}
					</div>
				);
			})}
		</div>
	);
};

export default TerminalOverlay;
