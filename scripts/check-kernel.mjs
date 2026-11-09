import { readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(fileURLToPath(new URL("..", import.meta.url)));
const kernelRoots = [
  "Solcore/Abi",
  "Solcore/Abi.lean",
  "Solcore/Core",
  "Solcore/Util",
  "Solcore/ContractRuntime",
  "Solcore/Resolved",
  "Solcore/Resolved.lean",
  "Solcore/SourceSemantics",
  "Solcore/SourceSemantics.lean",
  "Solcore/Synthesis/Source/ScalarMeaning",
  "Solcore/TypeSystem",
  "Solcore/TypeSystem.lean",
  "Solcore/Frontend",
  "Solcore/Frontend.lean",
  "Solcore/Syntax",
  "Solcore/Workspace",
];
const forbidden = /\b(sorry|admit|partial|unsafe|axiom|noncomputable|extern|implemented_by)\b/;
const violations = [];

function visit(path) {
  for (const name of readdirSync(path)) {
    const child = join(path, name);
    if (statSync(child).isDirectory()) {
      visit(child);
    } else if (name.endsWith(".lean")) {
      const lines = readFileSync(child, "utf8").split("\n");
      lines.forEach((line, index) => {
        if (forbidden.test(line)) {
          violations.push(`${relative(root, child)}:${index + 1}: ${line.trim()}`);
        }
      });
    }
  }
}

for (const kernelRoot of kernelRoots) {
  const path = join(root, kernelRoot);
  try {
    if (statSync(path).isDirectory()) {
      visit(path);
    } else if (path.endsWith(".lean")) {
      const lines = readFileSync(path, "utf8").split("\n");
      lines.forEach((line, index) => {
        if (forbidden.test(line)) {
          violations.push(
            `${relative(root, path)}:${index + 1}: ${line.trim()}`,
          );
        }
      });
    }
  } catch (error) {
    if (error.code !== "ENOENT") {
      throw error;
    }
  }
}

if (violations.length > 0) {
  throw new Error(`semantic kernel contains forbidden declarations:\n${violations.join("\n")}`);
}

console.log("semantic kernel policy verified");
