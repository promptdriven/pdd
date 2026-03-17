import React from "react";
import {
	CodeLine,
	CODE_FONT,
	CODE_FONT_SIZE,
	LINE_HEIGHT,
	LINE_NUMBER_COLOR,
	LINE_NUMBER_FONT_SIZE,
} from "./constants";

interface CodeBlockProps {
	lines: CodeLine[];
	startLineNumber?: number;
	opacity?: number;
}

export const CodeBlock: React.FC<CodeBlockProps> = ({
	lines,
	startLineNumber = 1,
	opacity = 1,
}) => {
	return (
		<div style={{ opacity }}>
			{lines.map((tokens, idx) => {
				const lineNum = startLineNumber + idx;
				return (
					<div
						key={lineNum}
						style={{
							display: "flex",
							alignItems: "baseline",
							height: LINE_HEIGHT,
							lineHeight: `${LINE_HEIGHT}px`,
						}}
					>
						{/* Line number */}
						<span
							style={{
								fontFamily: CODE_FONT,
								fontSize: LINE_NUMBER_FONT_SIZE,
								color: LINE_NUMBER_COLOR,
								opacity: 0.4,
								width: 40,
								textAlign: "right",
								marginRight: 24,
								userSelect: "none",
								flexShrink: 0,
							}}
						>
							{lineNum}
						</span>
						{/* Code tokens */}
						<span
							style={{
								fontFamily: CODE_FONT,
								fontSize: CODE_FONT_SIZE,
								whiteSpace: "pre",
							}}
						>
							{tokens.length === 0 ? (
								<span>&nbsp;</span>
							) : (
								tokens.map((token, tIdx) => (
									<span key={tIdx} style={{ color: token.color }}>
										{token.text}
									</span>
								))
							)}
						</span>
					</div>
				);
			})}
		</div>
	);
};

export default CodeBlock;
