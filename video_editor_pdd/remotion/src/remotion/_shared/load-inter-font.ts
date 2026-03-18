import { staticFile } from "remotion";

const INTER_FONT_URL = staticFile("fonts/InterVariable-latin.woff2");
const INTER_FONT_WEIGHTS = ["300", "400", "500", "600", "700", "900"];

let hasStartedLoading = false;

const loadInterFont = async () => {
  if (typeof document === "undefined" || typeof FontFace === "undefined") {
    return;
  }

  await Promise.all(
    INTER_FONT_WEIGHTS.map(async (weight) => {
      const face = new FontFace(
        "Inter",
        `url(${INTER_FONT_URL}) format("woff2")`,
        {
          style: "normal",
          weight,
        }
      );

      await face.load();
      document.fonts.add(face);
    })
  );
};

if (!hasStartedLoading) {
  hasStartedLoading = true;
  void loadInterFont().catch(() => undefined);
}

export {};
