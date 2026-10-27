# Merge review subagent

Use the exact PR identity and head recorded by PDD and the saved wait-merge step. Summarize current feedback and whether evidence still concerns that head. Return observations and gaps to the main chat. Do not invent an agent handoff schema for this runner-owned merge stage, claim merge from approval, merge the PR or enable automatic merge.

There is no mandatory wait-merge agent report. Return your observations to the main chat; do not invent a report command. PDD observes the real merge of the recorded PR; an unmerged or changed head leaves work pending. Changed behavior requires the relevant checks and review again through PDD.
