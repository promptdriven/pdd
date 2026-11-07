// Implements prompts/cli/interface-draft.prompt.md.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, relative, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { gitFiles, findTests, readPrompt, promptRefusal, interfaceBlocks, interfaceSchemaProblems, proseSha256, sourceFilePort, sha256 } from './runtime-preflight.mjs';
import { loadRuntimeWorkspace, allowsRuntimePath, nativeWorkspaceFiles } from './runtime-workspace.mjs';

function promptPaths(root) {
  const found = findTests({root, excludeFixtureProjects:true});
  return [...found.discoveryVisible].filter(path => path.endsWith('.prompt.md')).sort();
}
export function missingInterfaces(root) {
  return promptPaths(root).filter(path => !interfaceBlocks(sourceFilePort(root).read({path}).content).length);
}
export function interfaceFindings({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  return paths.flatMap(path => {
    try {
      const prompt = readPrompt(root, visible, path), problem = promptRefusal(prompt, 'interface');
      if (problem) return [{...problem, path}];
      return interfaceSchemaProblems(prompt.interface).map(item => ({code:item.code,path,section:item.pointer,message:`${path} ${item.pointer} ${item.rule}`}));
    } catch (error) { return [{code:error.code ?? 'interface-unreadable',path,message:error.message}]; }
  });
}
export function runtimeCoverage({root, paths = promptPaths(root)}) {
  const visible = new Set(gitFiles(root));
  let checkable = 0, native_only = 0;
  for (const path of paths) {
    try {
      const prompt = readPrompt(root,visible,path);
      if (promptRefusal(prompt,'interface') || interfaceSchemaProblems(prompt.interface).length) continue;
      if (prompt.interface.kind === 'native-only') native_only++;
      else if (Array.isArray(prompt.interface.entries) && prompt.interface.entries.length) checkable++;
    } catch { /* Missing and invalid source remains in the denominator. */ }
  }
  return {checkable,total:paths.length,native_only};
}

