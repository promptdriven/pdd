## Verdict
warn
## Summary
The title card renders correctly with all primary text elements: section label 'WHERE TO START', main title 'WHERE TO' and 'START', and horizontal rule between them. Background is the correct deep navy-black. Layout is centered as specified. The ghost module grid (6x4 rectangles at 0.06 opacity with one brighter at 0.08) is not discernible in the frame — while the spec defines these at near-invisible opacity levels (0.06–0.08), the element is flagged as critical ('one_module_preview'). At frame 515/546 (fade-out phase), elements should be partially faded but still appear at full or near-full brightness, which is acceptable under easeIn(quad) at ~48% through the transition. The blueprint grid at 0.05 opacity is also not discernible but is decorative.
