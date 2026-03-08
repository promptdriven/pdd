import path from "path";

function stripSpecsPrefix(specDir: string): string {
  return specDir.replace(/^specs[\\/]/, "").replace(/^[\\/]+/, "");
}

export function resolveSectionSpecDir(specDir: string): string {
  return path.join(process.cwd(), "specs", stripSpecsPrefix(specDir));
}

export function resolveSectionSpecFile(
  specDir: string,
  fileName: string
): string {
  return path.join(resolveSectionSpecDir(specDir), fileName);
}

export function toSectionSpecPath(specDir: string, fileName: string): string {
  const relativeDir = stripSpecsPrefix(specDir).replace(/\\/g, "/");
  return path.posix.join("specs", relativeDir, fileName);
}
