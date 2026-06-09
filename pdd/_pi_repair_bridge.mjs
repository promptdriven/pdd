// Pi repair session bridge for pdd interactive checkup.
// Usage: node _pi_repair_bridge.mjs <context.json> <output.json>
//
// Pi drives the full interactive session. Approved patches are recorded via
// the propose_repair_options custom tool and written to output.json on exit.

import { createAgentSession, defineTool } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { readFileSync, writeFileSync } from "fs";

const [, , contextPath, outputPath] = process.argv;
if (!contextPath || !outputPath) {
  console.error("Usage: node _pi_repair_bridge.mjs <context.json> <output.json>");
  process.exit(1);
}

const report = JSON.parse(readFileSync(contextPath, "utf8"));
const approvedPatches = [];

const proposeRepairOptions = defineTool({
  name: "propose_repair_options",
  label: "Record Repair Patches",
  description:
    "Record structured repair patches that the user has approved for a finding.",
  parameters: Type.Object({
    finding_id: Type.String({ description: "ID of the finding being repaired" }),
    patches: Type.Array(
      Type.Object({
        kind: Type.String({ description: "Patch kind, e.g. vocab_definition, contract_rule" }),
        target: Type.String({ description: "Relative path to the prompt file" }),
        anchor: Type.Record(Type.String(), Type.Unknown(), {
          description: "Anchor locating the insertion point",
        }),
        replacement: Type.String({ description: "New text to insert or replace" }),
      })
    ),
  }),
  execute: async (_toolCallId, { patches }) => {
    // Do not spread finding_id into patch objects — ApprovedPatch has no such field.
    approvedPatches.push(...patches);
    return {
      content: [{ type: "text", text: `Recorded ${patches.length} patch(es).` }],
      details: { recorded: patches.length },
    };
  },
});

const session = await createAgentSession({
  tools: ["read", "grep"],
  customTools: [proposeRepairOptions],
});

const findings = (report.findings ?? [])
  .map((f) => `  - ${f.finding_id ?? f.id ?? "?"}: ${f.summary ?? f.check ?? ""}`)
  .join("\n");

try {
  await session.prompt(
    `You are running an interactive prompt-repair session for the pdd CLI.\n\n` +
    `Repair report:\n${JSON.stringify(report, null, 2)}\n\n` +
    `Findings to address:\n${findings || "  (none)"}\n\n` +
    `For each finding: explain the issue, propose repair options, and — once ` +
    `the user approves — call propose_repair_options with the approved patches. ` +
    `When all findings are addressed, summarise what was recorded and finish.`
  );
  writeFileSync(outputPath, JSON.stringify({ approved_patches: approvedPatches }, null, 2));
} finally {
  session.dispose();
}
