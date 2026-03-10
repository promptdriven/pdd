import { resolveAnnotationTarget } from "../lib/annotation-target";

describe("resolveAnnotationTarget", () => {
  const project = {
    name: "test-project",
    sections: [
      {
        id: "animation_section",
        label: "Animation Section",
        videoFile: "animation_section.mp4",
        specDir: "animation_section",
        remotionDir: "S00-AnimationSection",
        compositionId: "AnimationSection",
        durationSeconds: 11.029333,
        offsetSeconds: 0,
      },
      {
        id: "veo_section",
        label: "Veo Section",
        videoFile: "veo_section.mp4",
        specDir: "veo_section",
        remotionDir: "S01-VeoSection",
        compositionId: "VeoSection",
        durationSeconds: 11.861333,
        offsetSeconds: 11.029333,
      },
    ],
  } as any;

  it("keeps section-local annotations unchanged", () => {
    expect(
      resolveAnnotationTarget(project, {
        sectionId: "animation_section",
        timestamp: 3.2,
        videoFile: "/api/video/outputs/sections/animation_section.mp4",
      })
    ).toEqual({
      sectionId: "animation_section",
      timestamp: 3.2,
      normalized: false,
    });
  });

  it("maps stitched full-video timestamps into the correct later section", () => {
    const target = resolveAnnotationTarget(project, {
      sectionId: "animation_section",
      timestamp: 16.821014,
      videoFile: "/api/video/outputs/full_video.mp4?v=123",
    });

    expect(target.sectionId).toBe("veo_section");
    expect(target.normalized).toBe(true);
    expect(target.timestamp).toBeCloseTo(5.791681, 5);
  });

  it("uses section duration overflow as a fallback signal even without a full_video path", () => {
    const target = resolveAnnotationTarget(project, {
      sectionId: "animation_section",
      timestamp: 12.5,
      videoFile: "/api/video/outputs/sections/animation_section.mp4",
    });

    expect(target.sectionId).toBe("veo_section");
    expect(target.normalized).toBe(true);
    expect(target.timestamp).toBeCloseTo(1.470667, 5);
  });

  it("prefers explicit global and section timestamps over heuristic inference", () => {
    const target = resolveAnnotationTarget(project, {
      sectionId: "animation_section",
      timestamp: 5.5,
      globalTimestamp: 16.8,
      sectionTimestamp: 5.770667,
      videoFile: "/api/video/outputs/full_video.mp4?v=456",
    });

    expect(target.sectionId).toBe("veo_section");
    expect(target.normalized).toBe(true);
    expect(target.timestamp).toBeCloseTo(5.770667, 5);
  });
});
