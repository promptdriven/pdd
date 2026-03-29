## Verdict
pass
## Summary
The ghost background curve does not match the spec. The spec calls for an inverse hyperbola descending from upper-left to lower-right at 0.04 opacity with a #D9944A stroke. The rendered frame shows a circular/arc shape positioned in the upper-right corner instead. The shape's geometry (circle vs. hyperbola) and position (upper-right vs. spanning upper-left to lower-right) differ from the spec. All other elements — 'PART 4' label, 'THE PRECISION', horizontal rule, 'TRADEOFF', background color, and layout centering — match the spec well. The fade-out state at frame 209/240 is plausible for the easeIn(quad) timing.
