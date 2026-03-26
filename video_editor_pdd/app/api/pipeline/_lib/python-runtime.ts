import fs from "fs";
import path from "path";

export type PythonRunSpec = {
  command: string;
  argsPrefix: string[];
  env: NodeJS.ProcessEnv;
};

function buildSanitizedPythonEnv(
  sourceEnv: NodeJS.ProcessEnv = process.env
): NodeJS.ProcessEnv {
  const env = { ...sourceEnv };
  env.PYTHONNOUSERSITE = env.PYTHONNOUSERSITE || "1";
  delete env.PYTHONPATH;
  return env;
}

/**
 * Resolve the Python command used by pipeline stages that shell out to Python.
 *
 * Preference order:
 * 1. Explicit override via PIPELINE_PYTHON_EXECUTABLE / PYTHON_EXECUTABLE
 * 2. Current conda env python when already inside the preferred env
 * 3. `conda run -n <preferred>` when a preferred env is requested
 * 4. Current conda env python
 * 5. Bare `python3`
 */
export function resolvePythonRunSpec(options?: {
  preferredCondaEnv?: string;
  env?: NodeJS.ProcessEnv;
}): PythonRunSpec {
  const env = options?.env ?? process.env;
  const preferredCondaEnv = options?.preferredCondaEnv;
  const sanitizedEnv = buildSanitizedPythonEnv(env);

  const explicitPython =
    env.PIPELINE_PYTHON_EXECUTABLE || env.PYTHON_EXECUTABLE || "";
  if (explicitPython && fs.existsSync(explicitPython)) {
    return {
      command: explicitPython,
      argsPrefix: [],
      env: sanitizedEnv,
    };
  }

  const currentCondaEnv = env.CONDA_DEFAULT_ENV || "";
  const currentCondaPrefix = env.CONDA_PREFIX || "";
  if (
    preferredCondaEnv &&
    currentCondaEnv === preferredCondaEnv &&
    currentCondaPrefix
  ) {
    const currentPython = path.join(currentCondaPrefix, "bin", "python");
    if (fs.existsSync(currentPython)) {
      return {
        command: currentPython,
        argsPrefix: [],
        env: sanitizedEnv,
      };
    }
  }

  const condaExe = env.CONDA_EXE || "";
  if (preferredCondaEnv && condaExe && fs.existsSync(condaExe)) {
    return {
      command: condaExe,
      argsPrefix: ["run", "--no-capture-output", "-n", preferredCondaEnv, "python"],
      env: sanitizedEnv,
    };
  }

  if (currentCondaPrefix) {
    const currentPython = path.join(currentCondaPrefix, "bin", "python");
    if (fs.existsSync(currentPython)) {
      return {
        command: currentPython,
        argsPrefix: [],
        env: sanitizedEnv,
      };
    }
  }

  return {
    command: "python3",
    argsPrefix: [],
    env: sanitizedEnv,
  };
}
