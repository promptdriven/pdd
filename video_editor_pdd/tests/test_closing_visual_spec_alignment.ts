import {
  NODES as DISSOLVE_LOOP_NODES,
  TERMINAL as DISSOLVE_LOOP_TERMINAL,
} from "../remotion/src/remotion/Closing05DissolveRegenerateLoop/constants";
import { NODES as TRIANGLE_NODES } from "../remotion/src/remotion/Closing04PddTriangle/constants";
import {
  BG_COLOR,
  URL_TEXT,
  CMD_LINE_1,
  CMD_LINE_2,
  TITLE_FADE_START,
  TITLE_FADE_DURATION,
  URL_FADE_START,
  URL_FADE_DURATION,
  CMD_BLOCK_FADE_START,
} from "../remotion/src/remotion/Closing09FinalTitleCard/constants";

describe("closing visual spec alignment", () => {
  it("keeps the PDD triangle node colors and descriptors aligned with the closing spec", () => {
    expect(TRIANGLE_NODES.prompt.color).toBe("#60A5FA");
    expect(TRIANGLE_NODES.tests.color).toBe("#4ADE80");
    expect(TRIANGLE_NODES.grounding.color).toBe("#D9944A");
    expect(TRIANGLE_NODES.prompt.descriptor).toBe("encode intent");
    expect(TRIANGLE_NODES.tests.descriptor).toBe("preserve behavior");
    expect(TRIANGLE_NODES.grounding.descriptor).toBe("maintain style");
    expect(TRIANGLE_NODES.prompt.descriptorY).toBeGreaterThan(TRIANGLE_NODES.prompt.labelY);
  });

  it("keeps the dissolve-regenerate triangle labels and ticker placement aligned with the closing spec", () => {
    expect(DISSOLVE_LOOP_NODES.map((node) => node.label)).toEqual([
      "PROMPT",
      "TESTS",
      "GROUNDING",
    ]);
    expect(DISSOLVE_LOOP_TERMINAL.x).toBe(960);
    expect(DISSOLVE_LOOP_TERMINAL.y).toBe(980);
    expect(DISSOLVE_LOOP_TERMINAL.color).toBe("#64748B");
    expect(DISSOLVE_LOOP_TERMINAL.opacity).toBe(0.5);
  });

  it("uses the final title-card copy from the authored spec", () => {
    expect(BG_COLOR).toBe("#0A0F1A");
    expect(URL_TEXT).toBe("promptdrivendevelopment.com");
    expect(CMD_LINE_1).toBe("uv tool install pdd-cli");
    expect(CMD_LINE_2).toBe("pdd update your_module.py");
  });

  it("reveals all final title-card content within the first 120 frames", () => {
    expect(TITLE_FADE_START).toBe(0);
    expect(TITLE_FADE_DURATION).toBe(30);
    expect(URL_FADE_START).toBe(30);
    expect(URL_FADE_DURATION).toBe(15);
    expect(CMD_BLOCK_FADE_START).toBe(45);
  });
});
