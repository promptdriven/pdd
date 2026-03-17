import React from 'react';
import {useCurrentFrame, Easing, interpolate} from 'remotion';
import {
	TERMINAL_BG,
	TEXT_DEFAULT,
	TEXT_MUTED,
	HEADER_COLOR,
	STRING_GREEN,
	MONO_FONT,
	TERMINAL_STRIP,
	TERMINAL_COMMANDS,
	FRAME_PDD_BUG_START,
	FRAME_PDD_FIX_START,
	FRAME_TESTS_PASS,
} from './constants';

const CHAR_DELAY = 2; // frames per character

/** Typing animation: reveals characters one by one */
const TypedText: React.FC<{
	text: string;
	startFrame: number;
	color: string;
	fontSize: number;
}> = ({text, startFrame, color, fontSize}) => {
	const frame = useCurrentFrame();
	const elapsed = frame - startFrame;
	const charsVisible = Math.max(0, Math.floor(elapsed / CHAR_DELAY));
	const visibleText = text.substring(0, charsVisible);

	// Blinking cursor
	const showCursor = charsVisible < text.length && elapsed >= 0;
	const cursorBlink = showCursor && Math.floor(frame / 8) % 2 === 0;

	return (
		<span style={{fontFamily: MONO_FONT, fontSize, color}}>
			{visibleText}
			{cursorBlink && (
				<span style={{opacity: 0.7}}>▊</span>
			)}
		</span>
	);
};

/** A terminal command line with prompt, command, and output */
const TerminalCommand: React.FC<{
	command: string;
	output: string;
	startFrame: number;
	outputColor?: string;
}> = ({command, output, startFrame, outputColor = TEXT_MUTED}) => {
	const frame = useCurrentFrame();
	const commandDuration = command.length * CHAR_DELAY;
	const outputStartFrame = startFrame + commandDuration + 6; // small pause after command

	const outputOpacity = interpolate(
		frame,
		[outputStartFrame, outputStartFrame + 8],
		[0, 0.7],
		{extrapolateLeft: 'clamp', extrapolateRight: 'clamp'},
	);

	if (frame < startFrame) return null;

	return (
		<div style={{marginBottom: 6}}>
			{/* Command line */}
			<div style={{display: 'flex', alignItems: 'center', gap: 8}}>
				<span style={{fontFamily: MONO_FONT, fontSize: 12, color: HEADER_COLOR}}>
					$
				</span>
				<TypedText
					text={command}
					startFrame={startFrame}
					color={TEXT_DEFAULT}
					fontSize={13}
				/>
			</div>

			{/* Output */}
			{frame >= outputStartFrame && (
				<div style={{paddingLeft: 20, marginTop: 2, opacity: outputOpacity}}>
					<span style={{fontFamily: MONO_FONT, fontSize: 11, color: outputColor}}>
						{output}
					</span>
				</div>
			)}
		</div>
	);
};

export const TerminalStrip: React.FC = () => {
	const frame = useCurrentFrame();

	// Layout fade-in
	const layoutOpacity = interpolate(frame, [0, 20], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// "All tests passing." output
	const allPassFrame = FRAME_TESTS_PASS + 4;
	const allPassOpacity = interpolate(frame, [allPassFrame, allPassFrame + 10], [0, 0.8], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	return (
		<div
			style={{
				position: 'absolute',
				left: TERMINAL_STRIP.x,
				top: TERMINAL_STRIP.y,
				width: TERMINAL_STRIP.width,
				height: TERMINAL_STRIP.height,
				backgroundColor: `${TERMINAL_BG}99`,
				borderRadius: 8,
				opacity: layoutOpacity,
				padding: '14px 20px',
				overflow: 'hidden',
			}}
		>
			{/* Terminal header bar */}
			<div
				style={{
					display: 'flex',
					gap: 6,
					marginBottom: 10,
				}}
			>
				<div style={{width: 10, height: 10, borderRadius: '50%', backgroundColor: '#EF4444', opacity: 0.6}} />
				<div style={{width: 10, height: 10, borderRadius: '50%', backgroundColor: '#F59E0B', opacity: 0.6}} />
				<div style={{width: 10, height: 10, borderRadius: '50%', backgroundColor: '#22C55E', opacity: 0.6}} />
			</div>

			{/* Command 1: pdd bug */}
			<TerminalCommand
				command={TERMINAL_COMMANDS[0].command}
				output={TERMINAL_COMMANDS[0].output}
				startFrame={FRAME_PDD_BUG_START}
			/>

			{/* Command 2: pdd fix */}
			<TerminalCommand
				command={TERMINAL_COMMANDS[1].command}
				output={TERMINAL_COMMANDS[1].output}
				startFrame={FRAME_PDD_FIX_START}
			/>

			{/* Final output: All tests passing */}
			{frame >= allPassFrame && (
				<div style={{paddingLeft: 20, marginTop: 4, opacity: allPassOpacity}}>
					<span style={{fontFamily: MONO_FONT, fontSize: 12, color: STRING_GREEN, fontWeight: 600}}>
						All tests passing.
					</span>
				</div>
			)}
		</div>
	);
};

export default TerminalStrip;
