import fs from "fs";
import path from "path";

describe("Remotion font loading", () => {
  it("ships a local Inter font asset for deterministic renders", () => {
    const fontPath = path.join(
      process.cwd(),
      "remotion",
      "public",
      "fonts",
      "InterVariable-latin.woff2"
    );

    expect(fs.existsSync(fontPath)).toBe(true);
    expect(fs.statSync(fontPath).size).toBeGreaterThan(0);
  });

  it("loads the Inter font through a shared Remotion font loader", () => {
    const loaderPath = path.join(
      process.cwd(),
      "remotion",
      "src",
      "remotion",
      "_shared",
      "load-inter-font.ts"
    );

    expect(fs.existsSync(loaderPath)).toBe(true);

    const source = fs.readFileSync(loaderPath, "utf-8");
    expect(source).toMatch(/delayRender/);
    expect(source).toMatch(/continueRender/);
    expect(source).toMatch(/staticFile\("fonts\/InterVariable-latin\.woff2"\)/);
  });

  it("imports the shared font loader from Root.tsx", () => {
    const rootPath = path.join(
      process.cwd(),
      "remotion",
      "src",
      "remotion",
      "Root.tsx"
    );
    const source = fs.readFileSync(rootPath, "utf-8");

    expect(source).toMatch(/load-inter-font/);
  });
});
