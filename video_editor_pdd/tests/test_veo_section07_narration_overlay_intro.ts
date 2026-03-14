import fs from "fs";
import path from "path";

describe("VeoSection07NarrationOverlayIntro BlurredBackground source", () => {
  it("supports either still images or video clips for the resolved background media", () => {
    const sourcePath = path.join(
      process.cwd(),
      "remotion/src/remotion/VeoSection07NarrationOverlayIntro/BlurredBackground.tsx"
    );
    const source = fs.readFileSync(sourcePath, "utf-8");

    expect(source).toContain("OffthreadVideo");
    expect(source).toContain("const isImageBackground =");
    expect(source).toContain("backgroundExtension === 'jpg'");
    expect(source).toContain("<Img");
    expect(source).toContain("<OffthreadVideo");
  });
});
