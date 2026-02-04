import assert from "assert";
import { execSync } from "child_process";
import path from "path";
import { add } from "../src/utils";

function testUtilsAddReturnsFive() {
  const result = add(2, 3);
  assert.strictEqual(result, 5, "utils.add(2,3) must return 5");
}

function testMainPrintsFive() {
  const mainPath = path.join(__dirname, "../src/main.ts");
  const tsnode = path.join(process.cwd(), "node_modules", ".bin", "ts-node");
  const output = execSync(`${JSON.stringify(tsnode)} ${JSON.stringify(mainPath)}`).toString().trim();
  assert.strictEqual(output, "5", "main.ts should print 5");
}

try {
  testUtilsAddReturnsFive();
  testMainPrintsFive();
  console.log("All tests passed!");
} catch (err: unknown) {
  console.error("Test failed:", err instanceof Error ? err.message : String(err));
  process.exit(1);
}
