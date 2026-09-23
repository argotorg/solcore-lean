import { createHash } from "node:crypto";
import { readdirSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");

function readJson(path) {
  return JSON.parse(readFileSync(join(root, path), "utf8"));
}

function sha256(value) {
  return createHash("sha256").update(value).digest("hex");
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
  assert(
    JSON.stringify(paths) === JSON.stringify([...paths].sort()),
    `${bundle.id}: files are not in C byte order`,
  );
  const entries = bundle.files
    .map((file) => `${file.path}\t${file.byteSize}\t${file.sha256}\n`)
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
    throw new Error(`${schema.path}${path}: schema object is not closed`);
  }
  if (
    Array.isArray(value.required) &&
    new Set(value.required).size !== value.required.length
  ) {
    throw new Error(`${schema.path}${path}: required contains duplicates`);
  }
  if (typeof value.$ref === "string") {
    const hashIndex = value.$ref.indexOf("#");
    const targetId = hashIndex < 0 ? value.$ref : value.$ref.slice(0, hashIndex);
    const fragment = hashIndex < 0 ? "" : value.$ref.slice(hashIndex + 1);
    assert(
      targetId === "" || targetId === schema.value.$id,
      `${schema.path}${path}.$ref: external schema reference ${value.$ref}`,
    );
    assert(
      resolveJsonPointer(schema.value, fragment),
      `${schema.path}${path}.$ref: unresolved JSON pointer ${value.$ref}`,
    );
  }
  for (const [key, entry] of Object.entries(value)) {
    verifySchemaNode(entry, schema, `${path}.${key}`);
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

const schemaPaths = readdirSync(join(root, "schema"))
  .filter((file) => file.endsWith(".schema.json"))
  .sort()
  .map((file) => `schema/${file}`);
assert(
  JSON.stringify(schemaPaths) === JSON.stringify([
    "schema/semantic-core-v1.schema.json",
    "schema/semantic-core-v2.schema.json",
  ]),
  "unexpected schema inventory",
);
const schemas = schemaPaths.map((path) => ({ path, value: readJson(path) }));
const schemaIds = new Set();
for (const schema of schemas) {
  assert(
    typeof schema.value.$id === "string" && schema.value.$id.length > 0,
    `${schema.path}: schema has no $id`,
  );
  assert(!schemaIds.has(schema.value.$id), `${schema.path}: duplicate schema id`);
  schemaIds.add(schema.value.$id);
  verifySchemaNode(schema.value, schema);
}

const semanticCoreV1 = schemas[0].value;
const semanticCoreV2 = schemas[1].value;
const frozenCoreDefinitionNames = [
  "nat", "type", "word256", "unitExpr", "boolExpr", "wordExpr",
  "varExpr", "letExpr", "ifExpr", "value",
];
for (const definitionName of frozenCoreDefinitionNames) {
  assert(
    JSON.stringify(sortedObject(semanticCoreV2.$defs[definitionName])) ===
      JSON.stringify(sortedObject(semanticCoreV1.$defs[definitionName])),
    `Semantic Core v2 changed frozen v1 definition ${definitionName}`,
  );
}
assert(
  JSON.stringify(semanticCoreV2.$defs.unaryExpr.properties.op.enum) ===
    JSON.stringify(["boolNot", "wordNot"]),
  "Semantic Core v2 unary operator enum changed",
);
assert(
  JSON.stringify(semanticCoreV2.$defs.binaryExpr.properties.op.enum) ===
    JSON.stringify([
      "wordAdd", "wordSub", "wordMul", "wordDiv", "wordMod", "wordEq",
      "wordGt", "wordAnd", "wordOr", "wordXor", "wordShl", "wordShr",
    ]),
  "Semantic Core v2 binary operator enum changed",
);

const profileManifest = readJson("profiles/manifest.json");
assert(
  profileManifest.digestAlgorithm === "lean-json-compress-sha256-v1",
  "unknown profile digest algorithm",
);
const registeredProfilePaths = profileManifest.profiles.map((entry) => entry.path).sort();
const profilePaths = readdirSync(join(root, "profiles"))
  .filter((file) => file.endsWith(".json") && file !== "manifest.json")
  .sort()
  .map((file) => `profiles/${file}`);
assert(
  JSON.stringify(registeredProfilePaths) === JSON.stringify(profilePaths),
  "profile manifest and checked-in profile files differ",
);
const profileIds = new Set();
for (const entry of profileManifest.profiles) {
  const profile = readJson(entry.path);
  assert(profile.id === entry.id, `${entry.path}: profile id mismatch`);
  assert(profile.language.id === entry.spec, `${entry.path}: spec id mismatch`);
  assert(!profileIds.has(entry.id), `${entry.path}: duplicate profile id`);
  profileIds.add(entry.id);
  const digest = `sha256:${sha256(JSON.stringify(sortedObject(profile)))}`;
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

console.log("solcore metadata verified");
