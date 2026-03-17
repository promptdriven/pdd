import React from "react";
import {
	AbsoluteFill,
	Sequence,
	useCurrentFrame,
	interpolate,
	Easing,
} from "remotion";
import { IDEChrome } from "./IDEChrome";
import { CodeBlock } from "./CodeBlock";
import { CursorBlink } from "./CursorBlink";
import { SelectionHighlight } from "./SelectionHighlight";
import { ParticleDissolve } from "./ParticleDissolve";
import { TerminalSnippet } from "./TerminalSnippet";
import {
	IDE_BG,
	TOTAL_FRAMES,
	OLD_CODE,
	NEW_CODE,
	DELETE_START,
	OLD_CODE_VISIBLE_END,
	PARTICLE_DURATION,
	NEW_BLOCK1_START,
	NEW_BLOCK2_START,
	NEW_BLOCK3_START,
	BLOCK_REVEAL_DURATION,
} from "./constants";

export const defaultColdOpen05CodeBlinkProps = {};

const OldCodeSection: React.FC = () => {
	const frame = useCurrentFrame();

	// Old code fades out at the delete moment
	const codeOpacity = interpolate(
		frame,
		[DELETE_START, DELETE_START + 3],
		[1, 0],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
		},
	);

	if (codeOpacity <= 0) return null;

	return (
		<div style={{ opacity: codeOpacity }}>
			<CodeBlock lines={OLD_CODE} />
		</div>
	);
};

const NewCodeSection: React.FC = () => {
	const frame = useCurrentFrame();

	// Block 1: lines 1-5 (indices 0-4)
	const block1Opacity = interpolate(
		frame,
		[NEW_BLOCK1_START, NEW_BLOCK1_START + BLOCK_REVEAL_DURATION],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.cubic),
		},
	);

	// Block 2: lines 6-10 (indices 5-9)
	const block2Opacity = interpolate(
		frame,
		[NEW_BLOCK2_START, NEW_BLOCK2_START + BLOCK_REVEAL_DURATION],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.cubic),
		},
	);

	// Block 3: lines 11-14 (indices 10-13)
	const block3Opacity = interpolate(
		frame,
		[NEW_BLOCK3_START, NEW_BLOCK3_START + BLOCK_REVEAL_DURATION],
		[0, 1],
		{
			extrapolateLeft: "clamp",
			extrapolateRight: "clamp",
			easing: Easing.out(Easing.cubic),
		},
	);

	if (frame < NEW_BLOCK1_START) return null;

	return (
		<div>
			<CodeBlock
				lines={NEW_CODE.slice(0, 5)}
				startLineNumber={1}
				opacity={block1Opacity}
			/>
			{block2Opacity > 0 && (
				<CodeBlock
					lines={NEW_CODE.slice(5, 10)}
					startLineNumber={6}
					opacity={block2Opacity}
				/>
			)}
			{block3Opacity > 0 && (
				<CodeBlock
					lines={NEW_CODE.slice(10, 14)}
					startLineNumber={11}
					opacity={block3Opacity}
				/>
			)}
		</div>
	);
};

export const ColdOpen05CodeBlink: React.FC = () => {
	const frame = useCurrentFrame();

	// Show cursor only when code is visible (old code or new code phase)
	const showOldCursor = frame < DELETE_START;
	const showNewCursor = frame >= NEW_BLOCK1_START;

	return (
		<AbsoluteFill style={{ backgroundColor: IDE_BG }}>
			<Sequence from={0} durationInFrames={TOTAL_FRAMES}>
				<IDEChrome>
					<div
						style={{
							position: "relative",
							padding: "16px 24px",
						}}
					>
						{/* Old code with selection highlight */}
						<div style={{ position: "relative" }}>
							<OldCodeSection />

							{/* Selection highlight overlay */}
							{frame >= 30 && frame < DELETE_START && (
								<SelectionHighlight lineCount={OLD_CODE.length} />
							)}

							{/* Cursor on old code */}
							{showOldCursor && <CursorBlink lineIndex={0} />}
						</div>

						{/* Particle dissolution */}
						{frame >= DELETE_START &&
							frame < DELETE_START + PARTICLE_DURATION + 10 && (
								<ParticleDissolve codeLines={OLD_CODE} />
							)}

						{/* Line numbers for empty editor phase */}
						{frame >= DELETE_START + 3 && frame < NEW_BLOCK1_START && (
							<div style={{ opacity: 0.3 }}>
								{/* Empty line numbers to show the void */}
								{Array.from({ length: 18 }, (_, i) => (
									<div
										key={i}
										style={{
											height: 22,
											lineHeight: "22px",
											fontFamily:
												"'JetBrains Mono', monospace",
											fontSize: 12,
											color: "#484F58",
											width: 40,
											textAlign: "right",
										}}
									>
										{i + 1}
									</div>
								))}
							</div>
						)}

						{/* New code blocks */}
						<NewCodeSection />

						{/* Cursor on new code */}
						{showNewCursor && <CursorBlink lineIndex={0} />}

						{/* Terminal snippet */}
						<TerminalSnippet />
					</div>
				</IDEChrome>
			</Sequence>
		</AbsoluteFill>
	);
};

export default ColdOpen05CodeBlink;
