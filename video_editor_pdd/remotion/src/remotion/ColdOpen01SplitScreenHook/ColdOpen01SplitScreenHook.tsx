import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { useVisualMediaSrc } from "../_shared/visual-runtime";
import { VideoPanel } from "./VideoPanel";
import { SplitLine } from "./SplitLine";
import { PanelLabel } from "./PanelLabel";
import {
	BG_COLOR,
	TOTAL_FRAMES,
	LEFT_LABEL_COLOR,
	LEFT_LABEL_TEXT,
	RIGHT_LABEL_COLOR,
	RIGHT_LABEL_TEXT,
} from "./constants";

export const defaultColdOpen01SplitScreenHookProps = {};

/**
 * Split Screen Hook — Developer Meets Grandmother
 *
 * Vertical split: LEFT shows a modern developer (Cursor IDE, AI-assisted edit),
 * RIGHT shows a 1950s grandmother darning a sock by lamplight.
 * Both complete their task simultaneously — the visual parallel is immediate.
 *
 * Hard cut from black at frame 0. No fade-in. 240 frames (8s at 30fps).
 */
export const ColdOpen01SplitScreenHook: React.FC = () => {
	const leftSrc = useVisualMediaSrc(
		"leftSrc",
		"veo/darning_split_screen.mp4",
	);
	const rightSrc = useVisualMediaSrc(
		"rightSrc",
		"veo/grandmother_darning_lamplight.mp4",
	);

	return (
		<AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
			<Sequence from={0} durationInFrames={TOTAL_FRAMES}>
				<AbsoluteFill>
					{/* Left panel — Developer (2025) */}
					<VideoPanel side="left" src={leftSrc} />

					{/* Right panel — Grandmother (1955) */}
					<VideoPanel side="right" src={rightSrc} />

					{/* Vertical split divider */}
					<SplitLine />

					{/* Year labels */}
					<PanelLabel
						text={LEFT_LABEL_TEXT}
						color={LEFT_LABEL_COLOR}
						side="left"
					/>
					<PanelLabel
						text={RIGHT_LABEL_TEXT}
						color={RIGHT_LABEL_COLOR}
						side="right"
					/>
				</AbsoluteFill>
			</Sequence>
		</AbsoluteFill>
	);
};

export default ColdOpen01SplitScreenHook;
