import { resolveParticleOpacity } from "../remotion/src/remotion/AnimationSection06ParticleBurst/motion";

describe("AnimationSection06ParticleBurst particle fade contract", () => {
  it("keeps particles partially visible during the tail-fade window", () => {
    const opacity = resolveParticleOpacity({
      frame: 25,
      currentDistance: 300,
      maxDistance: 300,
    });

    expect(opacity).toBeGreaterThan(0.1);
    expect(opacity).toBeLessThan(0.4);
  });

  it("fades particles fully out by the final frame", () => {
    const opacity = resolveParticleOpacity({
      frame: 30,
      currentDistance: 300,
      maxDistance: 300,
    });

    expect(opacity).toBe(0);
  });
});
