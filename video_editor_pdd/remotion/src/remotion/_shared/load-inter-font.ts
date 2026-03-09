import { continueRender, delayRender, staticFile } from "remotion";

const INTER_FONT_URL = staticFile("fonts/InterVariable-latin.woff2");
const INTER_FONT_WEIGHTS = ["300", "400", "500", "600", "700", "900"];
const interFontHandle =
  typeof document !== "undefined" ? delayRender("Loading Inter font") : null;

let hasStartedLoading = false;
let hasFinishedLoading = false;

const finishFontLoad = () => {
  if (interFontHandle === null || hasFinishedLoading) {
    return;
  }

  hasFinishedLoading = true;
  continueRender(interFontHandle);
};

const loadInterFont = async () => {
  if (typeof document === "undefined") {
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
  void loadInterFont().catch(() => undefined).finally(finishFontLoad);
}

export {};
