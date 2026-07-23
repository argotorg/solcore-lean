import { readdirSync, readFileSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(fileURLToPath(new URL("..", import.meta.url)));
const kernelRoots = ["Solcore/Core", "Solcore/Semantics"];
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
          violations.push(`${child.slice(root.length + 1)}:${index + 1}: ${line.trim()}`);
        }
      });
    }
  }
}

for (const relative of kernelRoots) {
  const path = join(root, relative);
  try {
    if (statSync(path).isDirectory()) {
      visit(path);
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
