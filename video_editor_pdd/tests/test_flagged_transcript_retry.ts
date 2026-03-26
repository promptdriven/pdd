import {
  collectFlaggedSegmentsBelowThreshold,
  collectFlaggedSegmentsBelowThresholdBySection,
  runFlaggedTranscriptRerenderRetries,
  runFlaggedTranscriptRerenderRetriesAcrossSections,
  type SegmentValidationLike,
} from "../components/stages/_lib/flagged-transcript-retry";

describe("collectFlaggedSegmentsBelowThreshold", () => {
  it("returns unique warn/fail segment IDs strictly below the threshold", () => {
    const rows: SegmentValidationLike[] = [
      { segmentId: "seg_001", status: "warn", matchRatio: 0.79 },
      { segmentId: "seg_001", status: "warn", matchRatio: 0.79 },
      { segmentId: "seg_002", status: "fail", matchRatio: 0.1 },
      { segmentId: "seg_003", status: "warn", matchRatio: 0.94 },
      { segmentId: "seg_004", status: "pass", matchRatio: 0.2 },
      { segmentId: "seg_005", status: "skip", matchRatio: 0.0 },
      { segmentId: "seg_006", status: "warn", matchRatio: null },
    ];

    expect(collectFlaggedSegmentsBelowThreshold(rows, 94)).toEqual([
      "seg_001",
      "seg_002",
    ]);
  });

  it("clamps thresholds outside 0-100", () => {
    const rows: SegmentValidationLike[] = [
      { segmentId: "seg_001", status: "fail", matchRatio: 0.5 },
    ];

    expect(collectFlaggedSegmentsBelowThreshold(rows, 999)).toEqual(["seg_001"]);
    expect(collectFlaggedSegmentsBelowThreshold(rows, -10)).toEqual([]);
  });
});

describe("runFlaggedTranscriptRerenderRetries", () => {
  it("rerenders below-threshold segments and stops when refreshed rows clear the threshold", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("tts-job-1");
    const startAudioSync = jest
      .fn<Promise<string>, [string]>()
      .mockResolvedValue("sync-job-1");
    const waitForJob = jest.fn<Promise<void>, [string]>().mockResolvedValue();
    const reloadValidationRows = jest
      .fn<Promise<SegmentValidationLike[]>, []>()
      .mockResolvedValue([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.96 },
        { segmentId: "seg_002", status: "pass", matchRatio: 1 },
      ]);
    const onTtsJobStarted = jest.fn();
    const onAudioSyncJobStarted = jest.fn();

    const result = await runFlaggedTranscriptRerenderRetries({
      initialRows: [
        { segmentId: "seg_001", status: "warn", matchRatio: 0.72 },
        { segmentId: "seg_002", status: "fail", matchRatio: 0.51 },
      ],
      thresholdPercent: 94,
      maxRetries: 3,
      sectionId: "part1_economics",
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRows,
      onTtsJobStarted,
      onAudioSyncJobStarted,
    });

    expect(startTtsRerender).toHaveBeenCalledWith(["seg_001", "seg_002"]);
    expect(startAudioSync).toHaveBeenCalledWith("part1_economics");
    expect(waitForJob).toHaveBeenNthCalledWith(1, "tts-job-1");
    expect(waitForJob).toHaveBeenNthCalledWith(2, "sync-job-1");
    expect(reloadValidationRows).toHaveBeenCalledTimes(1);
    expect(onTtsJobStarted).toHaveBeenCalledWith({
      attempt: 1,
      jobId: "tts-job-1",
      segmentIds: ["seg_001", "seg_002"],
    });
    expect(onAudioSyncJobStarted).toHaveBeenCalledWith({
      attempt: 1,
      jobId: "sync-job-1",
      sectionId: "part1_economics",
    });
    expect(result).toEqual({
      attemptsCompleted: 1,
      finalRows: [
        { segmentId: "seg_001", status: "warn", matchRatio: 0.96 },
        { segmentId: "seg_002", status: "pass", matchRatio: 1 },
      ],
      remainingSegmentIds: [],
    });
  });

  it("keeps retrying until maxRetries when rows remain below threshold", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValueOnce("tts-job-1")
      .mockResolvedValueOnce("tts-job-2");
    const startAudioSync = jest
      .fn<Promise<string>, [string]>()
      .mockResolvedValueOnce("sync-job-1")
      .mockResolvedValueOnce("sync-job-2");
    const waitForJob = jest.fn<Promise<void>, [string]>().mockResolvedValue();
    const reloadValidationRows = jest
      .fn<Promise<SegmentValidationLike[]>, []>()
      .mockResolvedValueOnce([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.7 },
      ])
      .mockResolvedValueOnce([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.68 },
      ]);

    const result = await runFlaggedTranscriptRerenderRetries({
      initialRows: [{ segmentId: "seg_001", status: "warn", matchRatio: 0.71 }],
      thresholdPercent: 94,
      maxRetries: 2,
      sectionId: "part1_economics",
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRows,
    });

    expect(startTtsRerender).toHaveBeenCalledTimes(2);
    expect(startAudioSync).toHaveBeenCalledTimes(2);
    expect(result).toEqual({
      attemptsCompleted: 2,
      finalRows: [{ segmentId: "seg_001", status: "warn", matchRatio: 0.68 }],
      remainingSegmentIds: ["seg_001"],
    });
  });

  it("does nothing when there are no rows below the threshold", async () => {
    const startTtsRerender = jest.fn<Promise<string>, [string[]]>();
    const startAudioSync = jest.fn<Promise<string>, [string]>();
    const waitForJob = jest.fn<Promise<void>, [string]>();
    const reloadValidationRows = jest.fn<Promise<SegmentValidationLike[]>, []>();

    const initialRows: SegmentValidationLike[] = [
      { segmentId: "seg_001", status: "warn", matchRatio: 0.95 },
    ];

    const result = await runFlaggedTranscriptRerenderRetries({
      initialRows,
      thresholdPercent: 94,
      maxRetries: 3,
      sectionId: "part1_economics",
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRows,
    });

    expect(startTtsRerender).not.toHaveBeenCalled();
    expect(startAudioSync).not.toHaveBeenCalled();
    expect(reloadValidationRows).not.toHaveBeenCalled();
    expect(result).toEqual({
      attemptsCompleted: 0,
      finalRows: initialRows,
      remainingSegmentIds: [],
    });
  });

  it("restores the best-known segment states after retries finish", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValueOnce("tts-job-1")
      .mockResolvedValueOnce("tts-job-2");
    const startAudioSync = jest
      .fn<Promise<string>, [string]>()
      .mockResolvedValueOnce("sync-job-1")
      .mockResolvedValueOnce("sync-job-2")
      .mockResolvedValueOnce("sync-job-3");
    const waitForJob = jest.fn<Promise<void>, [string]>().mockResolvedValue();
    const reloadValidationRows = jest
      .fn<Promise<SegmentValidationLike[]>, []>()
      .mockResolvedValueOnce([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.82 },
      ])
      .mockResolvedValueOnce([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.75 },
      ])
      .mockResolvedValueOnce([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.82 },
      ]);
    const captureSegmentStates = jest
      .fn<Promise<Record<string, string>>, [string[]]>()
      .mockResolvedValueOnce({ seg_001: "baseline" })
      .mockResolvedValueOnce({ seg_001: "attempt-1" })
      .mockResolvedValueOnce({ seg_001: "attempt-2" });
    const restoreSegmentStates = jest.fn<Promise<void>, [Record<string, string>]>().mockResolvedValue();

    const result = await runFlaggedTranscriptRerenderRetries({
      initialRows: [{ segmentId: "seg_001", status: "warn", matchRatio: 0.8 }],
      thresholdPercent: 94,
      maxRetries: 2,
      sectionId: "part1_economics",
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRows,
      captureSegmentStates,
      restoreSegmentStates,
    });

    expect(captureSegmentStates).toHaveBeenNthCalledWith(1, ["seg_001"]);
    expect(captureSegmentStates).toHaveBeenNthCalledWith(2, ["seg_001"]);
    expect(captureSegmentStates).toHaveBeenNthCalledWith(3, ["seg_001"]);
    expect(restoreSegmentStates).toHaveBeenCalledWith({ seg_001: "attempt-1" });
    expect(startAudioSync).toHaveBeenNthCalledWith(3, "part1_economics");
    expect(result.finalRows).toEqual([
      { segmentId: "seg_001", status: "warn", matchRatio: 0.82 },
    ]);
  });

  it("continues after audio-sync wait errors when configured to tolerate them", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("tts-job-1");
    const startAudioSync = jest
      .fn<Promise<string>, [string]>()
      .mockResolvedValue("sync-job-1");
    const waitForJob = jest
      .fn<Promise<void>, [string]>()
      .mockResolvedValueOnce(undefined)
      .mockRejectedValueOnce(new Error("sync failed"));
    const reloadValidationRows = jest
      .fn<Promise<SegmentValidationLike[]>, []>()
      .mockResolvedValue([
        { segmentId: "seg_001", status: "warn", matchRatio: 0.91 },
      ]);

    const result = await runFlaggedTranscriptRerenderRetries({
      initialRows: [{ segmentId: "seg_001", status: "warn", matchRatio: 0.8 }],
      thresholdPercent: 94,
      maxRetries: 1,
      sectionId: "part1_economics",
      startTtsRerender,
      startAudioSync,
      waitForJob,
      continueOnAudioSyncError: true,
      reloadValidationRows,
    });

    expect(result).toEqual({
      attemptsCompleted: 1,
      finalRows: [{ segmentId: "seg_001", status: "warn", matchRatio: 0.91 }],
      remainingSegmentIds: ["seg_001"],
    });
  });
});

describe("collectFlaggedSegmentsBelowThresholdBySection", () => {
  it("returns only sections with rows below threshold", () => {
    expect(
      collectFlaggedSegmentsBelowThresholdBySection(
        {
          part1: [
            { segmentId: "part1_001", status: "warn", matchRatio: 0.79 },
            { segmentId: "part1_002", status: "pass", matchRatio: 1 },
          ],
          part2: [
            { segmentId: "part2_001", status: "warn", matchRatio: 0.96 },
          ],
          part3: [
            { segmentId: "part3_001", status: "fail", matchRatio: 0.2 },
          ],
        },
        94,
      ),
    ).toEqual({
      part1: ["part1_001"],
      part3: ["part3_001"],
    });
  });
});

describe("runFlaggedTranscriptRerenderRetriesAcrossSections", () => {
  it("rerenders all below-threshold segments and reruns only affected sections", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("tts-job-1");
    const startAudioSync = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("sync-job-1");
    const waitForJob = jest.fn<Promise<void>, [string]>().mockResolvedValue();
    const reloadValidationRowsBySection = jest
      .fn<Promise<Record<string, SegmentValidationLike[]>>, []>()
      .mockResolvedValue({
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.96 }],
        part3: [{ segmentId: "part3_001", status: "pass", matchRatio: 1 }],
      });

    const result = await runFlaggedTranscriptRerenderRetriesAcrossSections({
      initialRowsBySection: {
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.71 }],
        part2: [{ segmentId: "part2_001", status: "warn", matchRatio: 0.97 }],
        part3: [{ segmentId: "part3_001", status: "fail", matchRatio: 0.3 }],
      },
      thresholdPercent: 94,
      maxRetries: 2,
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRowsBySection,
    });

    expect(startTtsRerender).toHaveBeenCalledWith(["part1_001", "part3_001"]);
    expect(startAudioSync).toHaveBeenCalledWith(["part1", "part3"]);
    expect(waitForJob).toHaveBeenNthCalledWith(1, "tts-job-1");
    expect(waitForJob).toHaveBeenNthCalledWith(2, "sync-job-1");
    expect(result).toEqual({
      attemptsCompleted: 1,
      finalRowsBySection: {
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.96 }],
        part3: [{ segmentId: "part3_001", status: "pass", matchRatio: 1 }],
      },
      remainingSegmentIdsBySection: {},
    });
  });

  it("restores best-known segment states across sections after retries finish", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("tts-job-1");
    const startAudioSync = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValueOnce("sync-job-1")
      .mockResolvedValueOnce("sync-job-2");
    const waitForJob = jest.fn<Promise<void>, [string]>().mockResolvedValue();
    const reloadValidationRowsBySection = jest
      .fn<Promise<Record<string, SegmentValidationLike[]>>, []>()
      .mockResolvedValueOnce({
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.91 }],
        part3: [{ segmentId: "part3_001", status: "warn", matchRatio: 0.6 }],
      })
      .mockResolvedValueOnce({
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.91 }],
        part3: [{ segmentId: "part3_001", status: "warn", matchRatio: 0.6 }],
      });
    const captureSegmentStates = jest
      .fn<Promise<Record<string, string>>, [string[]]>()
      .mockResolvedValueOnce({
        part1_001: "baseline-1",
        part3_001: "baseline-3",
      })
      .mockResolvedValueOnce({
        part1_001: "attempt-1-1",
        part3_001: "attempt-1-3",
      });
    const restoreSegmentStates = jest.fn<Promise<void>, [Record<string, string>]>().mockResolvedValue();

    const result = await runFlaggedTranscriptRerenderRetriesAcrossSections({
      initialRowsBySection: {
        part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.8 }],
        part3: [{ segmentId: "part3_001", status: "warn", matchRatio: 0.5 }],
      },
      thresholdPercent: 94,
      maxRetries: 1,
      startTtsRerender,
      startAudioSync,
      waitForJob,
      reloadValidationRowsBySection,
      captureSegmentStates,
      restoreSegmentStates,
    });

    expect(restoreSegmentStates).toHaveBeenCalledWith({
      part1_001: "attempt-1-1",
      part3_001: "attempt-1-3",
    });
    expect(startAudioSync).toHaveBeenNthCalledWith(2, ["part1", "part3"]);
    expect(result.finalRowsBySection).toEqual({
      part1: [{ segmentId: "part1_001", status: "warn", matchRatio: 0.91 }],
      part3: [{ segmentId: "part3_001", status: "warn", matchRatio: 0.6 }],
    });
  });

  it("continues all-sections retries after audio-sync wait errors when configured to tolerate them", async () => {
    const startTtsRerender = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("tts-job-1");
    const startAudioSync = jest
      .fn<Promise<string>, [string[]]>()
      .mockResolvedValue("sync-job-1");
    const waitForJob = jest
      .fn<Promise<void>, [string]>()
      .mockResolvedValueOnce(undefined)
      .mockRejectedValueOnce(new Error("sync failed"));
    const reloadValidationRowsBySection = jest
      .fn<Promise<Record<string, SegmentValidationLike[]>>, []>()
      .mockResolvedValue({
        part4: [{ segmentId: "part4_001", status: "warn", matchRatio: 0.82 }],
      });

    const result = await runFlaggedTranscriptRerenderRetriesAcrossSections({
      initialRowsBySection: {
        part4: [{ segmentId: "part4_001", status: "warn", matchRatio: 0.5 }],
      },
      thresholdPercent: 94,
      maxRetries: 1,
      startTtsRerender,
      startAudioSync,
      waitForJob,
      continueOnAudioSyncError: true,
      reloadValidationRowsBySection,
    });

    expect(result).toEqual({
      attemptsCompleted: 1,
      finalRowsBySection: {
        part4: [{ segmentId: "part4_001", status: "warn", matchRatio: 0.82 }],
      },
      remainingSegmentIdsBySection: { part4: ["part4_001"] },
    });
  });
});
