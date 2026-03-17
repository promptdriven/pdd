// ColdOpen06StillPatchingBeat constants

// Canvas
export const BG_COLOR = "#0D1117";
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Animation timing (frames at 30fps)
export const TOTAL_FRAMES = 150;
export const CODE_DIM_START = 0;
export const CODE_DIM_END = 30;
export const TEXT_FADE_START = 30;
export const TEXT_FADE_END = 60;
export const LINE_DRAW_START = 75;
export const LINE_DRAW_END = 90;
// Frame 90-150: hold — complete stillness

// Code underlay
export const CODE_UNDERLAY_FINAL_OPACITY = 0.08;

// Question text
export const TEXT_COLOR = "#E2E8F0";
export const ACCENT_COLOR = "#D9944A";
export const TEXT_OPACITY = 0.9;
export const TEXT_SIZE = 42;
export const TEXT_WEIGHT = 300;
export const LETTER_SPACING = 1;

// Accent line
export const LINE_COLOR = "#334155";
export const LINE_OPACITY = 0.3;
export const LINE_WIDTH_PX = 120;
export const LINE_Y = 580;
export const LINE_CENTER_X = 960;

// Regenerated code lines (dimmed underlay from spec 05)
export const REGENERATED_CODE_LINES = [
  'import React from "react";',
  'import { useCallback, useState } from "react";',
  "",
  "interface FormProps {",
  "  onSubmit: (data: FormData) => void;",
  "}",
  "",
  "export const Form: React.FC<FormProps> = ({ onSubmit }) => {",
  "  const [value, setValue] = useState('');",
  "",
  "  const handleSubmit = useCallback(() => {",
  "    onSubmit({ value });",
  "  }, [value, onSubmit]);",
  "",
  "  return (",
  '    <form onSubmit={handleSubmit}>',
  '      <input value={value} onChange={e => setValue(e.target.value)} />',
  "      <button type=\"submit\">Submit</button>",
  "    </form>",
  "  );",
  "};",
];
