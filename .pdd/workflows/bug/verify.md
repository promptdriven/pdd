# Run the regression and relevant native tests

Run the regression against the old behavior and retain its real failure when feasible; then run it against the fix and retain the pass. Use disposable source copies for wrong-behavior controls, never production state. Run nearby unaffected cases and the project's required checks.

Report commands, exit status, checked revision, actual outcomes and gaps. An expected failure demonstrates that this test detects this defect; a pass covers only the exercised behavior. Native tests are not prompt execution or general formal proof.
