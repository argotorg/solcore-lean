import { createHash } from "node:crypto";
import { readdirSync, readFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");

function readJson(path) {
  return JSON.parse(readFileSync(join(root, path), "utf8"));
}

function sha256(text) {
  return createHash("sha256").update(text).digest("hex");
}

function assert(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

function sortedObject(value) {
  if (Array.isArray(value)) {
    return value.map(sortedObject);
  }
  if (value !== null && typeof value === "object") {
    return Object.fromEntries(
      Object.keys(value)
        .sort()
        .map((key) => [key, sortedObject(value[key])]),
    );
  }
  return value;
}

function verifyFileSet(bundle) {
  const paths = bundle.files.map((file) => file.path);
  const sortedPaths = [...paths].sort();
  assert(
    JSON.stringify(paths) === JSON.stringify(sortedPaths),
    `${bundle.id}: files are not in C byte order`,
  );
  const entries = bundle.files
    .map(
      (file) =>
        `${file.path}\t${file.byteSize}\t${file.sha256}\n`,
    )
    .join("");
  const digest = sha256(`solcore-fileset-sha256-v1\n${entries}`);
  assert(
    digest === bundle.manifestSha256,
    `${bundle.id}: manifest digest mismatch (${digest})`,
  );
}

function verifyFilesOnDisk(bundle, sourceRoot) {
  for (const file of bundle.files) {
    const bytes = readFileSync(join(sourceRoot, file.path));
    assert(bytes.byteLength === file.byteSize, `${bundle.id}/${file.path}: byte size mismatch`);
    assert(sha256(bytes) === file.sha256, `${bundle.id}/${file.path}: content digest mismatch`);
  }
}

const standardLibrary = readJson("metadata/standard-library.json");
assert(
  standardLibrary.digestAlgorithm.id === "solcore-fileset-sha256-v1",
  "unknown standard-library digest algorithm",
);
verifyFileSet(standardLibrary.canonical);
for (const snapshot of standardLibrary.compatibilitySnapshots) {
  verifyFileSet(snapshot);
}

const oracleSchema = readJson("schema/oracle-v1.schema.json");
const schemaIssues = [];
function verifySchemaNode(value, path = "$") {
  if (Array.isArray(value)) {
    value.forEach((entry, index) => verifySchemaNode(entry, `${path}[${index}]`));
    return;
  }
  if (value === null || typeof value !== "object") {
    return;
  }
  if (value.type === "object" && value.additionalProperties !== false) {
    schemaIssues.push(`${path}: protocol object is not closed`);
  }
  if (
    Array.isArray(value.required) &&
    new Set(value.required).size !== value.required.length
  ) {
    schemaIssues.push(`${path}: required contains duplicates`);
  }
  if (typeof value.$ref === "string" && value.$ref.startsWith("#/$defs/")) {
    const name = value.$ref.slice("#/$defs/".length);
    if (oracleSchema.$defs[name] === undefined) {
      schemaIssues.push(`${path}: unresolved local ref ${value.$ref}`);
    }
  }
  for (const [key, entry] of Object.entries(value)) {
    verifySchemaNode(entry, `${path}.${key}`);
  }
}
verifySchemaNode(oracleSchema);
assert(schemaIssues.length === 0, schemaIssues.join("\n"));

const argumentValue = (name) => {
  const index = process.argv.indexOf(name);
  return index < 0 ? undefined : process.argv[index + 1];
};
const canonicalSourceRoot = argumentValue("--canonical-source-root");
if (canonicalSourceRoot !== undefined) {
  verifyFilesOnDisk(standardLibrary.canonical, canonicalSourceRoot);
}
const compatibilitySourceRoot = argumentValue("--compatibility-source-root");
if (compatibilitySourceRoot !== undefined) {
  for (const snapshot of standardLibrary.compatibilitySnapshots) {
    verifyFilesOnDisk(snapshot, compatibilitySourceRoot);
  }
}

const profileManifest = readJson("profiles/manifest.json");
assert(
  profileManifest.digestAlgorithm === "lean-json-compress-sha256-v1",
  "unknown profile digest algorithm",
);
for (const entry of profileManifest.profiles) {
  const profile = readJson(entry.path);
  assert(profile.id === entry.id, `${entry.path}: profile id mismatch`);
  assert(profile.language.id === entry.spec, `${entry.path}: spec id mismatch`);
  const encoded = JSON.stringify(sortedObject(profile));
  const digest = `sha256:${sha256(encoded)}`;
  assert(digest === entry.digest, `${entry.path}: profile digest mismatch (${digest})`);
}

const baselineManifest = readJson("metadata/baselines.json");
const bundleIds = new Set([
  standardLibrary.canonical.id,
  ...standardLibrary.compatibilitySnapshots.map((snapshot) => snapshot.id),
]);
for (const implementation of baselineManifest.implementations) {
  assert(
    bundleIds.has(implementation.standardLibraryBundle),
    `${implementation.id}: unknown standard-library bundle`,
  );
}

const oraclePath = join(root, ".lake", "build", "bin", "solcore-oracle");
const oracle = spawnSync(oraclePath, ["capabilities"], { encoding: "utf8" });
assert(
  oracle.status === 0,
  `oracle capabilities failed: ${oracle.error?.message ?? oracle.stderr}`,
);
const response = JSON.parse(oracle.stdout);
const report = response.verdict.result.value;
const profileEntry = profileManifest.profiles.find(
  (entry) => entry.id === report.profile.id,
);
assert(profileEntry !== undefined, "oracle returned an unregistered profile");
assert(
  report.profileDigest === profileEntry.digest,
  "oracle profile digest differs from profiles/manifest.json",
);
assert(
  JSON.stringify(sortedObject(report.profile)) ===
    JSON.stringify(sortedObject(readJson(profileEntry.path))),
  "oracle profile differs from the checked-in profile",
);

const expectedStandardLibrary = {
  sourceRevision: standardLibrary.canonical.sourceRevision,
  manifestAlgorithm: standardLibrary.digestAlgorithm.id,
  manifestSha256: standardLibrary.canonical.manifestSha256,
  files: standardLibrary.canonical.files,
};
assert(
  JSON.stringify(sortedObject(report.profile.language.standardLibrary)) ===
    JSON.stringify(sortedObject(expectedStandardLibrary)),
  "oracle standard-library metadata differs from metadata/standard-library.json",
);

const adrFiles = readdirSync(join(root, "docs", "adr"));
for (const feature of report.features) {
  if (feature.adr !== null) {
    assert(
      adrFiles.some((file) => file.startsWith(`${feature.adr}-`)),
      `${feature.feature}: referenced ADR-${feature.adr} does not exist`,
    );
  }
}

const implementationMetadata = new Map(
  baselineManifest.implementations.map((implementation) => [implementation.id, implementation]),
);
assert(
  report.baselines.length === implementationMetadata.size,
  "oracle and metadata contain different baseline sets",
);
for (const baseline of report.baselines) {
  const metadata = implementationMetadata.get(baseline.implementation);
  assert(metadata !== undefined, `${baseline.implementation}: missing baseline metadata`);
  const expected = {
    implementation: metadata.id,
    repository: metadata.repository,
    revision: metadata.revision,
    role: metadata.role,
    standardLibraryBundle: metadata.standardLibraryBundle,
    nativeSettings: {
      solver: metadata.nativeSettings.solver.mode,
      generatedDispatch: metadata.nativeSettings.generatedDispatch.enabled,
      primitiveSurface: metadata.nativeSettings.evm.primitiveSurface,
      bytecodeRuntime: metadata.nativeSettings.evm.bytecodeRuntime,
      nativeBackendTarget: metadata.nativeSettings.evm.nativeBackendTarget,
      externalYulCompilerTarget: metadata.nativeSettings.evm.externalYulCompilerTarget,
    },
    notes: metadata.capabilityNote,
  };
  assert(
    JSON.stringify(sortedObject(baseline)) === JSON.stringify(sortedObject(expected)),
    `${baseline.implementation}: Lean baseline differs from metadata/baselines.json`,
  );
}

const goldenManifest = readJson("Tests/golden/wire-manifest.json");
for (const golden of goldenManifest.cases) {
  const input =
    golden.stdin !== undefined && golden.stdin !== null
      ? readFileSync(join(root, golden.stdin), "utf8")
      : (golden.stdinLiteral ?? undefined);
  const run = spawnSync(oraclePath, golden.arguments, {
    encoding: "utf8",
    input,
  });
  assert(run.status === 0, `${golden.id}: oracle exited with ${run.status}`);
  assert(
    sha256(run.stdout) === golden.sha256,
    `${golden.id}: canonical wire output changed`,
  );
  if (golden.expected !== undefined) {
    assert(
      run.stdout === readFileSync(join(root, golden.expected), "utf8"),
      `${golden.id}: output differs from its checked-in golden`,
    );
  }
}

console.log("solcore metadata verified");
