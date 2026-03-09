import {
  filterWordsForSpecTimingWindow,
  parseSpecTimingWindow,
} from "../lib/spec-timing-context";

describe("lib/spec-timing-context", () => {
  it("parses a spec timestamp window", () => {
    expect(
      parseSpecTimingWindow([
        "# Demo",
        "",
        "**Timestamp:** 0:03 - 0:08",
        "",
      ].join("\n"))
    ).toEqual({
      startSeconds: 3,
      endSeconds: 8,
    });
  });

  it("returns null when a spec has no timestamp window", () => {
    expect(parseSpecTimingWindow("# Demo\n\nNo timestamp")).toBeNull();
  });

  it("filters section-level timing words down to the selected spec window", () => {
    const words = [
      { word: "intro", start: 0.2, end: 0.5 },
      { word: "first", start: 3.2, end: 3.4 },
      { word: "section", start: 4.1, end: 4.5 },
      { word: "outro", start: 8.1, end: 8.4 },
    ];

    expect(
      filterWordsForSpecTimingWindow(words, {
        startSeconds: 3,
        endSeconds: 8,
      })
    ).toEqual([
      { word: "first", start: 3.2, end: 3.4 },
      { word: "section", start: 4.1, end: 4.5 },
    ]);
  });

  it("returns the full section timeline when the spec has no timestamp window", () => {
    const words = [
      { word: "alpha", start: 1, end: 1.2 },
      { word: "beta", start: 2, end: 2.2 },
    ];

    expect(filterWordsForSpecTimingWindow(words, null)).toEqual(words);
  });
});
