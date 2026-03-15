import { resolveWaveOverlayBadges } from "../remotion/src/remotion/VeoSection03WaveDataOverlay/constants";

describe("VeoSection03WaveDataOverlay badge layout contract", () => {
  it("defaults to horizontally distributed badges across the data area", () => {
    const badges = resolveWaveOverlayBadges(null);

    expect(
      badges.map(({ x, y, label, value }) => ({ x, y, label, value }))
    ).toEqual([
      { x: 120, y: 680, label: "Wave Height", value: "0.8m" },
      { x: 860, y: 680, label: "Wave Period", value: "6.2s" },
      { x: 1600, y: 680, label: "Water Temp", value: "22°C" },
    ]);
  });

  it("uses contract-provided badge positions and labels when present", () => {
    const badges = resolveWaveOverlayBadges({
      stats: [
        { label: "Metric A", value: "1.0", icon: "wave", x: 140, y: 700 },
        { label: "Metric B", value: "2.0", icon: "clock", x: 900, y: 700 },
        { label: "Metric C", value: "3.0", icon: "thermometer", x: 1580, y: 700 },
      ],
    });

    expect(
      badges.map(({ x, y, label, value, icon }) => ({
        x,
        y,
        label,
        value,
        icon,
      }))
    ).toEqual([
      { x: 140, y: 700, label: "Metric A", value: "1.0", icon: "wave" },
      { x: 900, y: 700, label: "Metric B", value: "2.0", icon: "clock" },
      { x: 1580, y: 700, label: "Metric C", value: "3.0", icon: "thermometer" },
    ]);
  });
});
