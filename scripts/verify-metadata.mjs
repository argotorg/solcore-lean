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

const schemaPaths = readdirSync(join(root, "schema"))
  .filter((file) => file.endsWith(".schema.json"))
  .sort()
  .map((file) => `schema/${file}`);
const schemas = schemaPaths.map((path) => ({
  path,
  value: readJson(path),
}));
const schemasById = new Map();
const schemaIssues = [];

for (const schema of schemas) {
  assert(
    typeof schema.value.$id === "string" && schema.value.$id.length > 0,
    `${schema.path}: schema has no $id`,
  );
  if (schemasById.has(schema.value.$id)) {
    schemaIssues.push(`${schema.path}: duplicate schema id ${schema.value.$id}`);
  } else {
    schemasById.set(schema.value.$id, schema);
  }
}

const oracleV1SchemaId = "urn:solcore:oracle:v1";
const oracleV2SchemaId = "urn:solcore:oracle:v2";
const oracleV3SchemaId = "urn:solcore:oracle:v3";
const oracleV4SchemaId = "urn:solcore:oracle:v4";
const semanticCoreV1SchemaId = "urn:solcore:semantic-core:v1";
const semanticCoreV2SchemaId = "urn:solcore:semantic-core:v2";
const surfaceV1SchemaId = "urn:solcore:surface:v1";
const parseResultV1SchemaId = "urn:solcore:parse-result:v1";
const permittedExternalRefs = new Map([
  [oracleV2SchemaId, new Set([oracleV1SchemaId, semanticCoreV1SchemaId])],
  [oracleV3SchemaId, new Set([oracleV1SchemaId, semanticCoreV2SchemaId])],
  [oracleV4SchemaId, new Set([
    surfaceV1SchemaId,
    parseResultV1SchemaId,
  ])],
  [parseResultV1SchemaId, new Set([surfaceV1SchemaId])],
]);
let semanticCoreV1ReferenceCount = 0;
let semanticCoreV2ReferenceCount = 0;
let surfaceV1ParseResultReferenceCount = 0;
let oracleV4SurfaceReferenceCount = 0;
let oracleV4ParseResultReferenceCount = 0;

function resolveJsonPointer(document, fragment) {
  let pointer;
  try {
    pointer = decodeURIComponent(fragment);
  } catch {
    return false;
  }
  if (pointer === "") {
    return true;
  }
  if (!pointer.startsWith("/")) {
    return false;
  }
  let current = document;
  for (const encodedToken of pointer.slice(1).split("/")) {
    const token = encodedToken.replaceAll("~1", "/").replaceAll("~0", "~");
    if (
      current === null ||
      typeof current !== "object" ||
      !Object.prototype.hasOwnProperty.call(current, token)
    ) {
      return false;
    }
    current = current[token];
  }
  return true;
}

function verifySchemaRef(ref, schema, path) {
  const hashIndex = ref.indexOf("#");
  const targetId = hashIndex < 0 ? ref : ref.slice(0, hashIndex);
  const fragment = hashIndex < 0 ? "" : ref.slice(hashIndex + 1);
  const targetSchema =
    targetId === "" ? schema : schemasById.get(targetId);
  if (targetSchema === undefined) {
    schemaIssues.push(`${schema.path}${path}: unresolved schema ref ${ref}`);
    return;
  }
  if (targetId !== "" && targetId !== schema.value.$id) {
    const permitted = permittedExternalRefs.get(schema.value.$id);
    if (permitted === undefined || !permitted.has(targetId)) {
      schemaIssues.push(`${schema.path}${path}: external schema ref is not permitted: ${ref}`);
      return;
    }
    if (
      schema.value.$id === oracleV2SchemaId &&
      targetId === semanticCoreV1SchemaId
    ) {
      semanticCoreV1ReferenceCount += 1;
    }
    if (
      schema.value.$id === oracleV3SchemaId &&
      targetId === semanticCoreV2SchemaId
    ) {
      semanticCoreV2ReferenceCount += 1;
    }
    if (
      schema.value.$id === parseResultV1SchemaId &&
      targetId === surfaceV1SchemaId
    ) {
      surfaceV1ParseResultReferenceCount += 1;
    }
    if (schema.value.$id === oracleV4SchemaId) {
      if (targetId === surfaceV1SchemaId) {
        oracleV4SurfaceReferenceCount += 1;
      } else if (targetId === parseResultV1SchemaId) {
        oracleV4ParseResultReferenceCount += 1;
      }
    }
  }
  if (!resolveJsonPointer(targetSchema.value, fragment)) {
    schemaIssues.push(`${schema.path}${path}: unresolved JSON pointer ${ref}`);
  }
}

function verifySchemaNode(value, schema, path = "$") {
  if (Array.isArray(value)) {
    value.forEach((entry, index) =>
      verifySchemaNode(entry, schema, `${path}[${index}]`),
    );
    return;
  }
  if (value === null || typeof value !== "object") {
    return;
  }
  if (value.type === "object" && value.additionalProperties !== false) {
    schemaIssues.push(`${schema.path}${path}: schema object is not closed`);
  }
  if (
    Array.isArray(value.required) &&
    new Set(value.required).size !== value.required.length
  ) {
    schemaIssues.push(`${schema.path}${path}: required contains duplicates`);
  }
  if (typeof value.$ref === "string") {
    verifySchemaRef(value.$ref, schema, `${path}.$ref`);
  }
  for (const [key, entry] of Object.entries(value)) {
    verifySchemaNode(entry, schema, `${path}.${key}`);
  }
}

for (const schema of schemas) {
  verifySchemaNode(schema.value, schema);
}
assert(
  schemasById.has(oracleV1SchemaId),
  "schema/oracle-v1.schema.json is not registered by $id",
);
assert(
  schemasById.has(oracleV2SchemaId),
  "schema/oracle-v2.schema.json is not registered by $id",
);
assert(
  schemasById.has(oracleV3SchemaId),
  "schema/oracle-v3.schema.json is not registered by $id",
);
assert(
  schemasById.has(oracleV4SchemaId),
  "schema/oracle-v4.schema.json is not registered by $id",
);
assert(
  schemasById.has(semanticCoreV1SchemaId),
  "schema/semantic-core-v1.schema.json is not registered by $id",
);
assert(
  schemasById.has(semanticCoreV2SchemaId),
  "schema/semantic-core-v2.schema.json is not registered by $id",
);
assert(
  schemasById.has(surfaceV1SchemaId),
  "schema/surface-v1.schema.json is not registered by $id",
);
assert(
  schemasById.has(parseResultV1SchemaId),
  "schema/parse-result-v1.schema.json is not registered by $id",
);
assert(
  semanticCoreV1ReferenceCount > 0,
  "oracle v2 schema does not reference the registered Semantic Core v1 schema",
);
assert(
  semanticCoreV2ReferenceCount > 0,
  "oracle v3 schema does not reference the registered Semantic Core v2 schema",
);
assert(
  surfaceV1ParseResultReferenceCount === 1,
  "parse-result v1 schema must reference the registered Surface v1 schema exactly once",
);
assert(
  oracleV4SurfaceReferenceCount === 7 &&
    oracleV4ParseResultReferenceCount === 1,
  "Oracle v4 schema has an unexpected external reference surface",
);

const semanticCoreV1Schema = schemasById.get(semanticCoreV1SchemaId).value;
const semanticCoreV2Schema = schemasById.get(semanticCoreV2SchemaId).value;
const surfaceV1Schema = schemasById.get(surfaceV1SchemaId).value;
const parseResultV1Schema = schemasById.get(parseResultV1SchemaId).value;
const oracleV4Schema = schemasById.get(oracleV4SchemaId).value;
assert(
  surfaceV1Schema.$ref === "#/$defs/file" &&
    surfaceV1Schema.$defs.file.properties.schema.const ===
      "solcore-surface/v1" &&
    surfaceV1Schema.$defs.file.required.includes("schema"),
  "Surface v1 schema does not enforce its root schema discriminator",
);
assert(
  parseResultV1Schema.type === "object" &&
    parseResultV1Schema.additionalProperties === false &&
    JSON.stringify(Object.keys(parseResultV1Schema.properties).sort()) ===
      JSON.stringify(["schema", "value"]) &&
    JSON.stringify([...parseResultV1Schema.required].sort()) ===
      JSON.stringify(["schema", "value"]) &&
    parseResultV1Schema.properties.schema.const ===
      "solcore-parse-result/v1" &&
    parseResultV1Schema.properties.value.$ref === surfaceV1Schema.$id,
  "Parse-result v1 schema is not the strict Surface v1 wrapper",
);
const frozenCoreDefinitionNames = [
  "nat",
  "type",
  "word256",
  "unitExpr",
  "boolExpr",
  "wordExpr",
  "varExpr",
  "letExpr",
  "ifExpr",
  "value",
];
for (const definitionName of frozenCoreDefinitionNames) {
  assert(
    JSON.stringify(sortedObject(semanticCoreV2Schema.$defs[definitionName])) ===
      JSON.stringify(sortedObject(semanticCoreV1Schema.$defs[definitionName])),
    `Semantic Core v2 changed frozen v1 definition ${definitionName}`,
  );
}
assert(
  JSON.stringify(semanticCoreV2Schema.$defs.unaryExpr.properties.op.enum) ===
    JSON.stringify(["boolNot", "wordNot"]),
  "Semantic Core v2 unary operator enum differs from ADR-0011",
);
assert(
  JSON.stringify(semanticCoreV2Schema.$defs.binaryExpr.properties.op.enum) ===
    JSON.stringify([
      "wordAdd",
      "wordSub",
      "wordMul",
      "wordDiv",
      "wordMod",
      "wordEq",
      "wordGt",
      "wordAnd",
      "wordOr",
      "wordXor",
      "wordShl",
      "wordShr",
    ]),
  "Semantic Core v2 binary operator enum differs from ADR-0011",
);
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
const registeredProfiles = new Map();
for (const entry of profileManifest.profiles) {
  const profile = readJson(entry.path);
  assert(profile.id === entry.id, `${entry.path}: profile id mismatch`);
  assert(profile.language.id === entry.spec, `${entry.path}: spec id mismatch`);
  const encoded = JSON.stringify(sortedObject(profile));
  const digest = `sha256:${sha256(encoded)}`;
  assert(digest === entry.digest, `${entry.path}: profile digest mismatch (${digest})`);
  assert(
    !registeredProfiles.has(entry.id),
    `${entry.path}: duplicate profile id ${entry.id}`,
  );
  registeredProfiles.set(entry.id, { entry, profile });
}

const registeredM1aProfile = registeredProfiles.get("core-m1a-v1");
assert(registeredM1aProfile !== undefined, "core-m1a-v1 profile is not registered");
const oracleV2Schema = schemasById.get(oracleV2SchemaId).value;
assert(
  JSON.stringify(sortedObject(oracleV2Schema.$defs.m1aProfile.const)) ===
    JSON.stringify(sortedObject(registeredM1aProfile.profile)),
  "Oracle v2 schema profile const differs from the registered M1a profile",
);
assert(
  oracleV2Schema.$defs.profileRef.properties.digest.const ===
    registeredM1aProfile.entry.digest,
  "Oracle v2 schema profile digest differs from the profile manifest",
);
const registeredM1cProfile = registeredProfiles.get("core-m1c-v1");
assert(registeredM1cProfile !== undefined, "core-m1c-v1 profile is not registered");
const oracleV3Schema = schemasById.get(oracleV3SchemaId).value;
assert(
  oracleV3Schema.$defs.request.properties.spec.const ===
    registeredM1cProfile.entry.spec &&
    oracleV3Schema.$defs.profileRef.properties.id.const ===
      registeredM1cProfile.entry.id,
  "Oracle v3 schema spec or profile id differs from the profile manifest",
);
assert(
  JSON.stringify(sortedObject(oracleV3Schema.$defs.m1cProfile.const)) ===
    JSON.stringify(sortedObject(registeredM1cProfile.profile)),
  "Oracle v3 schema profile const differs from the registered M1c profile",
);
assert(
  oracleV3Schema.$defs.profileRef.properties.digest.const ===
    registeredM1cProfile.entry.digest,
  "Oracle v3 schema profile digest differs from the profile manifest",
);
assert(
  oracleV3Schema.$defs.capabilityReport.properties.profileDigest.const ===
    registeredM1cProfile.entry.digest,
  "Oracle v3 capability profile digest differs from the profile manifest",
);
assert(
  oracleV3Schema.$defs.capabilityReport.properties.coreSchema.const ===
    semanticCoreV2Schema.$defs.program.properties.schema.const,
  "Oracle v3 schema does not bind the registered Semantic Core v2 schema",
);

const legacyProfileIds = ["core-v1", "core-m1a-v1", "core-m1c-v1"];
for (const profileId of legacyProfileIds) {
  const registered = registeredProfiles.get(profileId);
  assert(registered !== undefined, `${profileId} profile is not registered`);
  assert(
    registered.profile.language.grammarVersion === null,
    `${profileId} unexpectedly acquired a grammar version`,
  );
  assert(
    !registered.profile.language.knownFeatures.includes("surfaceGrammar"),
    `${profileId} unexpectedly acquired the Surface grammar feature`,
  );
}

const registeredM2bProfile = registeredProfiles.get("frontend-m2b-v1");
assert(
  registeredM2bProfile !== undefined,
  "frontend-m2b-v1 profile is not registered",
);
const m2bProfile = registeredM2bProfile.profile;
assert(
  registeredM2bProfile.entry.spec === "solcore/0.1.0-draft.4" &&
    m2bProfile.language.id === registeredM2bProfile.entry.spec,
  "M2b frontend profile is not bound to draft.4",
);
assert(
  m2bProfile.language.grammarVersion === 1 &&
    m2bProfile.language.staticSemanticsVersion === 2 &&
    m2bProfile.language.dynamicSemanticsVersion === 2,
  "draft.4 does not add grammar version 1 while carrying semantics version 2",
);
assert(
  JSON.stringify(m2bProfile.language.knownFeatures) ===
    JSON.stringify([
      ...registeredM1cProfile.profile.language.knownFeatures,
      "surfaceGrammar",
    ]),
  "draft.4 known features do not extend draft.3 by exactly surfaceGrammar",
);
assert(
  m2bProfile.scope === "frontend" &&
    m2bProfile.observation === "staticVerdictV1" &&
    m2bProfile.contractRuntime === null &&
    JSON.stringify(m2bProfile.enabledFeatures) ===
      JSON.stringify(["surfaceGrammar"]),
  "M2b frontend profile has an incompatible scope, observation, or feature set",
);
assert(
  oracleV4Schema.$defs.request.properties.spec.const ===
      registeredM2bProfile.entry.spec &&
    oracleV4Schema.$defs.profileRef.properties.id.const ===
      registeredM2bProfile.entry.id &&
    oracleV4Schema.$defs.profileRef.properties.digest.const ===
      registeredM2bProfile.entry.digest,
  "Oracle v4 schema request binding differs from the profile manifest",
);
assert(
  JSON.stringify(sortedObject(oracleV4Schema.$defs.m2bProfile.const)) ===
    JSON.stringify(sortedObject(m2bProfile)),
  "Oracle v4 schema profile const differs from the registered M2b profile",
);
assert(
  oracleV4Schema.$defs.capabilityReport.properties.profileDigest.const ===
      registeredM2bProfile.entry.digest &&
    oracleV4Schema.$defs.capabilityReport.properties.surfaceSchema.const ===
      surfaceV1Schema.$defs.file.properties.schema.const &&
    oracleV4Schema.$defs.capabilityReport.properties.parseResultSchema.const ===
      parseResultV1Schema.properties.schema.const,
  "Oracle v4 capability schema bindings differ from registered publication schemas",
);
assert(
  JSON.stringify(
    oracleV4Schema.$defs.nonAssociativeBinaryOperator.enum,
  ) === JSON.stringify(["lt", "gt", "le", "ge", "eq", "ne"]),
  "Oracle v4 SP0002 operator set differs from ADR-0013",
);
for (const verdictName of [
  "lexicalRejectedVerdict",
  "parsingRejectedVerdict",
]) {
  const diagnostics =
    oracleV4Schema.$defs[verdictName].properties.diagnostics;
  assert(
    diagnostics.minItems === 1 && diagnostics.maxItems === 1,
    `Oracle v4 ${verdictName} does not require exactly one diagnostic`,
  );
}
assert(
  oracleV4Schema.$defs.parseAcceptedVerdict.properties.result.$ref ===
    parseResultV1SchemaId,
  "Oracle v4 accepted parse verdict does not use parse-result v1",
);

const baselineManifest = readJson("metadata/baselines.json");
const expectedCapabilityBaselines = baselineManifest.implementations.map(
  (implementation) => ({
    implementation: implementation.id,
    repository: implementation.repository,
    revision: implementation.revision,
    role: implementation.role,
    standardLibraryBundle: implementation.standardLibraryBundle,
    nativeSettings: {
      solver: implementation.nativeSettings.solver.mode,
      generatedDispatch: implementation.nativeSettings.generatedDispatch.enabled,
      primitiveSurface: implementation.nativeSettings.evm.primitiveSurface,
      bytecodeRuntime: implementation.nativeSettings.evm.bytecodeRuntime,
      nativeBackendTarget: implementation.nativeSettings.evm.nativeBackendTarget,
      externalYulCompilerTarget:
        implementation.nativeSettings.evm.externalYulCompilerTarget,
    },
    notes: implementation.capabilityNote,
  }),
);
assert(
  JSON.stringify(sortedObject(
    oracleV4Schema.$defs.capabilityReport.properties.baselines.const,
  )) === JSON.stringify(sortedObject(expectedCapabilityBaselines)),
  "Oracle v4 capability baselines differ from metadata/baselines.json",
);
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
function readCapabilityOutput(argument) {
  const oracle = spawnSync(oraclePath, [argument], { encoding: "utf8" });
  assert(
    oracle.status === 0,
    `oracle ${argument} failed: ${oracle.error?.message ?? oracle.stderr}`,
  );
  const response = JSON.parse(oracle.stdout);
  assert(
    response.verdict?.kind === "accepted" &&
      response.verdict.result?.value !== undefined,
    `oracle ${argument} did not return an accepted capability report`,
  );
  return { response, report: response.verdict.result.value };
}

function verifyCapabilityProfile(argument, expectedProfileId, response, report) {
  const registered = registeredProfiles.get(expectedProfileId);
  assert(
    registered !== undefined,
    `oracle ${argument} expected profile is not registered`,
  );
  assert(
    report.profile?.id === expectedProfileId,
    `oracle ${argument} returned profile ${report.profile?.id ?? "<missing>"} instead of ${expectedProfileId}`,
  );
  assert(
    response.spec === registered.entry.spec && report.spec === registered.entry.spec,
    `oracle ${argument} spec differs from profiles/manifest.json`,
  );
  assert(
    response.profile?.id === registered.entry.id &&
      response.profile?.digest === registered.entry.digest,
    `oracle ${argument} response profile differs from profiles/manifest.json`,
  );
  assert(
    report.profileDigest === registered.entry.digest,
    `oracle ${argument} profile digest differs from profiles/manifest.json`,
  );
  assert(
    JSON.stringify(sortedObject(report.profile)) ===
      JSON.stringify(sortedObject(registered.profile)),
    `oracle ${argument} profile differs from the checked-in profile`,
  );
}

const v1Capabilities = readCapabilityOutput("capabilities");
verifyCapabilityProfile(
  "capabilities",
  "core-v1",
  v1Capabilities.response,
  v1Capabilities.report,
);
const v2Capabilities = readCapabilityOutput("capabilities-v2");
verifyCapabilityProfile(
  "capabilities-v2",
  "core-m1a-v1",
  v2Capabilities.response,
  v2Capabilities.report,
);
const v3Capabilities = readCapabilityOutput("capabilities-v3");
verifyCapabilityProfile(
  "capabilities-v3",
  "core-m1c-v1",
  v3Capabilities.response,
  v3Capabilities.report,
);
assert(
  v3Capabilities.response.schema === "solcore-oracle/v3" &&
    v3Capabilities.report.schema === "solcore-capabilities/v3",
  "capabilities-v3 returned an incompatible Oracle or capability schema",
);
assert(
  v3Capabilities.report.coreSchema ===
    semanticCoreV2Schema.$defs.program.properties.schema.const,
  "capabilities-v3 does not bind the registered Semantic Core v2 schema",
);
const report = v1Capabilities.report;

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
for (const capability of [v1Capabilities, v2Capabilities, v3Capabilities]) {
  for (const feature of capability.report.features) {
    if (feature.adr !== null) {
      assert(
        adrFiles.some((file) => file.startsWith(`${feature.adr}-`)),
        `${feature.feature}: referenced ADR-${feature.adr} does not exist`,
      );
    }
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
