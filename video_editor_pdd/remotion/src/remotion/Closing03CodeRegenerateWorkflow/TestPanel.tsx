import React from 'react';
import {useCurrentFrame, Easing, interpolate, spring} from 'remotion';
import {
	PANEL_BG,
	TEXT_DEFAULT,
	HEADER_COLOR,
	STRING_GREEN,
	BUG_RED,
	AMBER_HIGHLIGHT,
	PASS_GREEN,
	MONO_FONT,
	TEST_PANEL,
	EXISTING_TESTS,
	NEW_TEST,
	FRAME_PDD_BUG_START,
	FRAME_TESTS_PASS,
} from './constants';

const LINE_HEIGHT = 36;
const TEST_OFFSET_Y = 50;
const FPS = 30;

const TestLine: React.FC<{
	name: string;
	status: 'pass' | 'fail';
	index: number;
	highlight?: boolean;
}> = ({name, status, index, highlight}) => {
	const frame = useCurrentFrame();
	const icon = status === 'pass' ? '✓' : '✗';
	const iconColor = status === 'pass' ? STRING_GREEN : BUG_RED;

	// Bounce animation for the check flip (fail -> pass)
	const isNewTest = index === EXISTING_TESTS.length;
	const shouldBounce = isNewTest && status === 'pass';

	let scale = 1;
	if (shouldBounce) {
		const bounceProgress = spring({
			frame: frame - FRAME_TESTS_PASS,
			fps: FPS,
			config: {
				damping: 8,
				stiffness: 200,
				mass: 0.6,
			},
		});
		scale = interpolate(bounceProgress, [0, 1], [0.3, 1]);
	}

	return (
		<div
			style={{
				height: LINE_HEIGHT,
				display: 'flex',
				alignItems: 'center',
				gap: 12,
				paddingLeft: 20,
				...(highlight ? {
					backgroundColor: `${AMBER_HIGHLIGHT}14`,
				} : {}),
			}}
		>
			<span
				style={{
					fontFamily: MONO_FONT,
					fontSize: 14,
					color: iconColor,
					opacity: status === 'pass' ? 0.8 : 1,
					width: 20,
					textAlign: 'center',
					display: 'inline-block',
					transform: `scale(${scale})`,
				}}
			>
				{icon}
			</span>
			<span
				style={{
					fontFamily: MONO_FONT,
					fontSize: 12,
					color: TEXT_DEFAULT,
					opacity: 0.6,
				}}
			>
				{name}
			</span>
		</div>
	);
};

export const TestPanel: React.FC = () => {
	const frame = useCurrentFrame();

	// Layout fade-in
	const layoutOpacity = interpolate(frame, [0, 20], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// New test appears after pdd bug command starts + typing time
	const newTestAppearFrame = FRAME_PDD_BUG_START + 30; // after command typed + output
	const newTestOpacity = interpolate(frame, [newTestAppearFrame, newTestAppearFrame + 12], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
		easing: Easing.out(Easing.quad),
	});

	// Determine new test status
	const newTestStatus: 'pass' | 'fail' = frame >= FRAME_TESTS_PASS ? 'pass' : 'fail';

	// Green pulse ripple across test panel when all pass
	const pulseProgress = interpolate(frame, [FRAME_TESTS_PASS + 5, FRAME_TESTS_PASS + 20], [0, 1], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});
	const pulseOpacity = interpolate(frame, [FRAME_TESTS_PASS + 5, FRAME_TESTS_PASS + 15, FRAME_TESTS_PASS + 25], [0, 0.12, 0], {
		extrapolateLeft: 'clamp',
		extrapolateRight: 'clamp',
	});

	return (
		<div
			style={{
				position: 'absolute',
				left: TEST_PANEL.x,
				top: TEST_PANEL.y,
				width: TEST_PANEL.width,
				height: TEST_PANEL.height,
				backgroundColor: `${PANEL_BG}4D`,
				borderRadius: 8,
				opacity: layoutOpacity,
				overflow: 'hidden',
			}}
		>
			{/* Header */}
			<div
				style={{
					display: 'flex',
					alignItems: 'center',
					gap: 8,
					padding: '10px 16px',
					borderBottom: '1px solid rgba(100, 116, 139, 0.15)',
				}}
			>
				<span
					style={{
						fontFamily: MONO_FONT,
						fontSize: 11,
						color: HEADER_COLOR,
						opacity: 0.5,
					}}
				>
					test_user_parser.py
				</span>
			</div>

			{/* Test lines */}
			<div style={{padding: '12px 0'}}>
				{EXISTING_TESTS.map((test, i) => (
					<TestLine
						key={test}
						name={test}
						status="pass"
						index={i}
					/>
				))}

				{/* New test line */}
				{frame >= newTestAppearFrame && (
					<div style={{opacity: newTestOpacity}}>
						<TestLine
							name={NEW_TEST}
							status={newTestStatus}
							index={EXISTING_TESTS.length}
							highlight={newTestStatus === 'fail'}
						/>
					</div>
				)}
			</div>

			{/* Green pulse overlay */}
			{pulseOpacity > 0 && (
				<div
					style={{
						position: 'absolute',
						top: 0,
						left: 0,
						right: 0,
						bottom: 0,
						backgroundColor: PASS_GREEN,
						opacity: pulseOpacity,
						borderRadius: 8,
						pointerEvents: 'none',
					}}
				/>
			)}

			{/* Test count summary */}
			{frame >= FRAME_TESTS_PASS + 10 && (
				<div
					style={{
						position: 'absolute',
						bottom: 16,
						right: 20,
						fontFamily: MONO_FONT,
						fontSize: 11,
						color: STRING_GREEN,
						opacity: interpolate(frame, [FRAME_TESTS_PASS + 10, FRAME_TESTS_PASS + 22], [0, 0.6], {
							extrapolateLeft: 'clamp',
							extrapolateRight: 'clamp',
						}),
					}}
				>
					5/5 passing
				</div>
			)}
		</div>
	);
};

export default TestPanel;
