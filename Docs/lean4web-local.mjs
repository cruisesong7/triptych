import { spawn } from "node:child_process";
import { existsSync, realpathSync } from "node:fs";
import { dirname, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = realpathSync(resolve(dirname(fileURLToPath(import.meta.url)), ".."));
const requestedLean4webRoot = resolve(
  process.env.LEAN4WEB_DIR || process.argv[2] || resolve(repoRoot, "..", "lean4web"),
);
const requestedServer = resolve(requestedLean4webRoot, "server", "index.mjs");

if (!existsSync(requestedServer)) {
  console.error(`lean4web server not found at ${requestedServer}`);
  console.error("Set LEAN4WEB_DIR or pass the lean4web checkout path as the first argument.");
  process.exit(2);
}

const lean4webRoot = realpathSync(requestedLean4webRoot);
const server = resolve(lean4webRoot, "server", "index.mjs");

const child = spawn(process.execPath, [server], {
  cwd: lean4webRoot,
  env: {
    ...process.env,
    NODE_ENV: "development",
    GITHUB_ACTIONS: "true",
    VITE_COLLAB: "false",
    PROJECTS_BASE_PATH: relative(lean4webRoot, repoRoot),
    PORT: process.env.PORT || "3000",
  },
  stdio: "inherit",
});

for (const signal of ["SIGINT", "SIGTERM"]) {
  process.on(signal, () => child.kill(signal));
}

child.on("exit", (code) => process.exit(code ?? 1));
