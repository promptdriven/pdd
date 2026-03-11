import path from "path";
import { getProjectDir } from "@/lib/projects";

function stripSpecsPrefix(specDir: string): string {
  return specDir.replace(/^specs[\\/]/, "").replace(/^[\\/]+/, "");
}

export function resolveSectionSpecDir(specDir: string): string {
  if (path.isAbsolute(specDir)) {
    return specDir;
  }
  return path.join(getProjectDir(), "specs", stripSpecsPrefix(specDir));
}

export function resolveSectionSpecFile(
  specDir: string,
  fileName: string
): string {
  return path.join(resolveSectionSpecDir(specDir), fileName);
}

export function toSectionSpecPath(specDir: string, fileName: string): string {
  const relativeDir = path.isAbsolute(specDir)
    ? path
        .relative(path.join(getProjectDir(), "specs"), specDir)
        .replace(/\\/g, "/")
        .replace(/^[./]+/, "")
    : stripSpecsPrefix(specDir).replace(/\\/g, "/");
  return path.posix.join("specs", relativeDir, fileName);
}
