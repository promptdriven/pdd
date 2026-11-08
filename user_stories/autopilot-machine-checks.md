As an Autopilot operator, I want heavy checks and open runs to fit my machine, so that checks do not overload it or make waiting issues look stuck.

## Acceptance criteria

1. Check slots follow usable cores and free memory. A machine resize takes effect at the next tick. The documented rule covers small machines and large VMs.
2. Each Linux check gets a distinct CPU share when taskset is available. Other platforms receive a CPU hint and use fewer default slots.
3. Personal computers use at most half their cores by default. A busy machine waits before starting new checks.
4. Default open runs follow check slots. Explicit run and check limits are saved and take precedence. Current native admission enforces the open-run limit without changing coordinator identity after a resize.
5. Status shows calculated and chosen limits, busy and waiting checks, and cores per check. Waiting preserves queue order and pauses the existing stuck clock.
6. Capacity reads and ticks use native ports and no AI calls. Existing queue cleanup and suite-failure handling remain in effect. Machine-caused retries belong to a separate feature.

## Rules to check

Check slots and open runs obey the machine capacity rule owned by the shared queue prompt. CPU lists of simultaneous checks are disjoint. No new check starts above the selected slot count or while load exceeds usable cores. A capacity change does not revoke running work.
