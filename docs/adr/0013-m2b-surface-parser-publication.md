# ADR-0013: M2b Surface parser publication boundary

- Status: Accepted
- Decision date: 2026-08-18
- Scope: M2b Surface parser publication

## Context

ADR-0012 fixed the closed M2a lexical and syntactic grammar and introduced a
pure, total lexer and parser. The proof kernel now connects successful execution
to independent lexical and parsing judgments in both directions, proves lexical
uniqueness and relational determinism, connects public lexical failures to
cursor-local rejection judgments, and proves the defensive lexer and parser
fuel failures and the lexer output-validation failure unreachable. The M2b
publication proof layer additionally classifies every unchecked parser result,
proves the parser's defensive invalid-input and invalid-output classifications
unreachable, and proves that every successful parser result projects to the
closed Surface v1 wire language.

M2a deliberately did not publish that kernel. No published profile enables a
normative grammar, Oracle v1 `parse` remains unsupported, and Oracle v2 and v3
accept only their respective closed Semantic Core inputs.
Using the internal `Surface` types directly for differential testing would make
Lean constructor growth an accidental protocol change and would leave source
limits, diagnostics, compatibility, and canonical serialization unspecified.

M2b publishes parsing without publishing resolution, checking, elaboration, or
evaluation. The publication must preserve the exact syntactic information
needed by later phases while keeping every draft.1 through draft.3 artifact
immutable.

## Decision

### Language version and frontend profile

Publish the parser under language version `solcore/0.1.0-draft.4` with these
component versions:

- `grammarVersion = 1`;
- `staticSemanticsVersion = 2`;
- `dynamicSemanticsVersion = 2`;
- `abiVersion = null`; and
- `storageLayoutVersion = null`.

The static and dynamic component versions are carried forward unchanged from
draft.3. Their presence records the monotonic language-version lineage; it does
not enable Core checking or evaluation in the M2b frontend profile. The
canonical standard-library bundle, implementation-baseline pins, and all
previously known feature IDs retain their draft.3 values and order. Only the
new draft.4 `knownFeatures` array appends the new feature, and the global
profile manifest appends the new profile entry; draft.1 through draft.3 arrays
remain byte-for-byte unchanged.

Append one feature ID, `surfaceGrammar`. It is `normative` and `implemented` and
means exactly the lexer, parser, source spans, comments, syntax constructors,
precedence, associativity, fixture envelope, and source diagnostics fixed by
ADR-0012. It does not include name resolution, literal interpretation, type
checking, standard-library identity, Core elaboration, or evaluation.

Publish profile `frontend-m2b-v1` with:

- scope `frontend`;
- only `surfaceGrammar` in `enabledFeatures`;
- observation policy `staticVerdictV1`;
- solver policy `tabled`, retained as the profile-wide canonical policy but not
  consulted by parsing;
- span unit `utf8Byte`;
- source encoding `UTF-8`; and
- no contract runtime.

The profile's `enabledFeatures` and the profile-scoped M2b feature matrix are
new one-element arrays containing only `surfaceGrammar`; they do not extend or
replace an M1 profile or feature matrix. The M2b matrix therefore satisfies
`implemented ⊆ enabled ⊆ normative ⊆ known` without making any Core or
unresolved source-language feature available through Oracle v4. The draft.4
language object's `knownFeatures` array still carries every earlier known
feature before appending `surfaceGrammar`.

### Parse input and source-byte limit

The `parse` query accepts exactly one source file:

```json
{
  "path": "fixture.solc",
  "content": "function main() -> () { return (); }"
}
```

Both fields are required and no additional field is permitted. `path` is a
nonempty opaque UTF-8 source label. It is copied exactly into every returned
source span. M2b does not normalize it, interpret path separators, require a
`.solc` suffix, resolve it against a directory, compare it with a filesystem,
or perform file I/O. An empty path or a non-string field is a protocol error;
the spelling of a nonempty path is not otherwise a language or security
decision. Workspace paths and path safety belong to M2c.

Oracle v4 has one resource field, `sourceBytes`, with a default of `1048576`.
The request carries the selected nonnegative limit explicitly. Before invoking
the lexer, the handler compares the UTF-8 byte length of `content` with that
limit. The path, JSON escapes, object syntax, request envelope, and NDJSON line
terminator do not contribute to `sourceBytes`.

If the content length is at most the limit, parsing proceeds. If it is greater,
the result is `inconclusive` at phase `sourcePreflight`, with resource
`sourceBytes`, the requested limit, and the exact measured content byte length
as `consumed`. It is not `rejected`, and neither lexing nor parsing runs. Thus an
empty source under a zero limit reaches the parser and is rejected as unexpected
end of file, while any nonempty source under that limit is inconclusive.

Invalid NDJSON, invalid JSON string encoding, an unknown or duplicate field, or
an invalid request/profile/schema binding is a `protocolError`, not a source
diagnostic. The preflight limit is an operational bound over an otherwise valid
request and therefore uses the language verdict `inconclusive`.

### Closed Surface wire AST

Publish the strict schema `solcore-surface/v1`. It is a result representation,
not an alternative parser input. All objects are closed: missing fields,
additional fields, unknown tags, invalid tag-specific fields, negative or
non-integral offsets, and invalid lexical payloads fail strict decoding.
Nonnegative integers use the same convention as the Core schemas: equivalent
integral JSON numbers may decode, while the canonical encoder emits ordinary
decimal notation without a fraction or exponent.

The version-local Lean wire layer defines three refined, proof-carrying string
atoms rather than admitting arbitrary `String` values:

- `IdentifierText` matches `[A-Za-z][A-Za-z0-9_]*` and is not `function`,
  `let`, `if`, `else`, or `return`;
- `DecimalDigits` is a nonempty string of ASCII decimal digits; and
- `HexadecimalDigits` is a nonempty string of ASCII decimal digits, `A` through
  `F`, or `a` through `f`.

It also defines `TypeSpelling` as the closed two-case atom `bool | word`. The
strict JSON decoder constructs these atoms only after validating their complete
lexical predicate, and the total encoder can therefore emit every inhabitant
canonically. Wire-to-internal embedding erases the refinements. Internal-to-wire
projection checks them and returns failure for an invalid internal payload as
well as for any future unrepresentable constructor.

The following definitions fix every v1 tag and field. A `span` is:

```text
{ "source": string, "startByte": nat, "endByte": nat }
```

A `name` is `{ "span": span, "text": IdentifierText }`. Every span returned by
Oracle v4 has `source` exactly equal to the request path and is valid for the
request content. Half-open byte ranges and syntax-node containment have the
meaning fixed by ADR-0012.

A type syntax value is one of:

| Tag | Required fields | Meaning |
| --- | --- | --- |
| `unit` | `tag`, `span` | The explicit `()` type |
| `named` | `tag`, `name` | The contextual type spelling `bool` or `word` |

For the `named` variant, the `name` object has the usual `span` field but its
`text` field is a `TypeSpelling`, exactly `bool` or `word`; no other canonical
identifier is valid in this field.

An integer expression records `base` as `decimal` or `hexadecimal`, preserves
the raw `digits`, and has its exact source `span`. Its digits are
`DecimalDigits` for the decimal base and `HexadecimalDigits` for the
hexadecimal base. Hexadecimal digits exclude the `0x` prefix.

Expression values are closed by the following table:

| Tag | Required fields |
| --- | --- |
| `unit` | `tag`, `span` |
| `integer` | `tag`, `span`, `base`, `digits` |
| `name` | `tag`, `name` |
| `group` | `tag`, `span`, `inner` |
| `call` | `tag`, `span`, `callee`, `arguments` |
| `unary` | `tag`, `span`, `operator`, `operand` |
| `binary` | `tag`, `span`, `operator`, `left`, `right` |
| `ifThenElse` | `tag`, `span`, `condition`, `thenBranch`, `elseBranch` |

`callee` is a `name`, and `arguments` is an ordered array of expressions. A
unary operator occurrence is
`{ "span": span, "operator": "not" }`. A binary operator occurrence is
`{ "span": span, "operator": binary-op-v1 }`, where `binary-op-v1` is the
closed string set:

```text
mul, div, mod, add, sub, bitAnd, bitXor, bitOr,
lt, gt, le, ge, eq, ne
```

Statement and declaration objects have no tag because each field position has
one closed kind:

| Value | Required fields |
| --- | --- |
| let statement | `span`, `name`, `type`, `value` |
| return statement | `span`, `value` |
| function declaration | `span`, `name`, `returnType`, `bindings`, `result` |

`bindings` is an ordered array of let statements and `result` is the final
return statement. A retained comment is
`{ "kind": "line" | "block", "span": span }`. The ordered comment array
contains the outer span of each comment and does not expose discarded
whitespace or nested-comment delimiter records.

The top-level Surface file is:

```text
{
  "schema": "solcore-surface/v1",
  "span": span,
  "function": function-declaration,
  "comments": [comment, ...]
}
```

The strict Surface decoder requires two caller-supplied codec bounds,
`maxDepth` and `maxNodes`. `maxDepth` is expression-edge depth: every expression
constructor contributes one, a unit, integer, or name expression has depth 1,
and following a group inner expression, call argument, unary operand, binary
operand, or conditional operand increments depth by one. File, declaration,
statement, type, name, operator, comment, span, and array wrappers do not add
expression depth. The bound applies to every expression tree in the file.

`maxNodes` is global semantic-node count over the complete Surface value. The
file, function declaration, every let and return statement, every type syntax
and expression, every name and located operator, and every retained comment
each contribute one node. Spans, scalar fields, and array wrappers do not
contribute nodes; array elements contribute according to their value kinds.
The decoder rejects before constructing a value whose global node count or any
expression depth would exceed the supplied bound.

These are codec-local bounds for decoding an externally supplied Surface or
parse-result wire value. They are not Oracle v4 request limits, do not appear in
the v4 `limits` object or capability defaults, and do not produce an Oracle
`inconclusive` verdict. M2b defines no normative defaults for them; every
decoder invocation must supply both values explicitly. The Oracle's `parse`
handler receives raw source rather than a Surface AST and therefore uses only
`sourceBytes` on its request path.

A standalone Surface wire decoder checks closed JSON shape, tags, nonnegative
integral offsets, refined lexical atoms, and its codec bounds. It has no request
SourceFile and does not establish span-source equality, span ordering or source
byte bounds, source-slice agreement, or AST containment. The Oracle integration
validator, which has the exact `{path, content}` request, establishes those
request-relative properties before returning an accepted parse result. A
locally decodable but request-inconsistent Surface value is therefore not a
possible accepted Oracle result.

The schema preserves every M2b internal Surface constructor and observable
field: names, source and operator spans, grouping nodes, integer radix and raw
digits, call boundaries and argument order, conditional syntax, declaration
and binding order, and retained comment kind and order. It intentionally does
not publish lexer tokens, discarded whitespace, source contents, resolved
identities, types, or Core nodes.

Implement `solcore-surface/v1` with closed version-local Lean wire types. The
embedding from a decoded v1 wire value into the internal Surface types is total.
Projection from an arbitrary internal Surface value to v1 is partial, even if
all current internal constructors are representable. Encoders are defined over
the v1 wire types, never over the open-ended internal types. The encoder is
total and canonical and has no depth or node precondition. Decoder-after-encoder
round trip holds for a wire value when its defined node count is at most
`maxNodes` and its defined expression depth is at most `maxDepth`;
canonicalization is idempotent under the corresponding sufficient decoder
bounds. For every v1 wire value `wire`, projection after embedding must return
`some wire`. This makes a future internal constructor an explicit projection
failure rather than a silent widening of the frozen schema.

### Parse result and source diagnostics

Publish `solcore-parse-result/v1` using the existing result-payload convention:

```text
{
  "schema": "solcore-parse-result/v1",
  "value": surface-file-v1
}
```

The nested value is the complete `solcore-surface/v1` object described above.
A successful `parse` verdict is `accepted` at phase `surfaceParsing` and carries
exactly this result. There is no parse-success result that omits comments,
spans, grouping, or raw literal spelling.

Lexing and parsing remain fail-fast, so a `rejected` parse verdict contains
exactly one diagnostic. Its verdict phase equals its diagnostic phase. A
Surface diagnostic is the closed object:

```text
{
  "code": string,
  "severity": "error",
  "phase": "surfaceLexing" | "surfaceParsing",
  "primary": span,
  "arguments": object,
  "display": string | null
}
```

`primary.source` echoes the request path exactly. The code, phase, primary
UTF-8 span, and structured arguments are normative. `display` is required but
is nonnormative presentation text; the canonical reference response emits
`null`.

The diagnostic mappings are closed as follows:

| Code | Phase | Primary span | Exact `arguments` object |
| --- | --- | --- | --- |
| `SL0001` | `surfaceLexing` | The lexically invalid Unicode scalar's exact UTF-8 range | `{ "character": <single Unicode-scalar string> }` |
| `SL0002` | `surfaceLexing` | The unmatched outer `/*` through end of file | `{}` |
| `SP0001` | `surfaceParsing` | The unexpected token, or the empty end-of-file span | `{ "expectation": <parse-expectation-v1>, "found": <token-kind-v1 or null> }` |
| `SP0002` | `surfaceParsing` | The second non-associative operator | `{ "operator": <binary-op-v1> }` |

`parse-expectation-v1` is a closed object. A concrete-token expectation is
`{ "kind": "token", "token": token-kind-v1 }`. Every other expectation is an
object containing only `kind`, whose value is one of:

```text
identifier, type, expression, argumentOrRightParen, commaOrRightParen,
bindingOrReturn, endOfFile
```

`token-kind-v1` is a closed object containing a `kind` field. Identifier and
literal variants have these exact additional fields:

| Kind | Additional required field |
| --- | --- |
| `identifier` | `text` |
| `decimal` | `digits` |
| `hexadecimal` | `digits` |

All other variants contain only `kind`, selected from this closed set:

```text
keywordFunction, keywordLet, keywordIf, keywordElse, keywordReturn,
arrow, equal, equalEqual, bang, bangEqual, less, lessEqual,
greater, greaterEqual, plus, minus, star, slash, percent,
ampersand, caret, pipe, leftParen, rightParen, leftBrace,
rightBrace, colon, semicolon, comma
```

The identifier and digit payload restrictions are the same as in the Surface
wire AST: `identifier.text` is `IdentifierText`, `decimal.digits` is
`DecimalDigits`, and `hexadecimal.digits` is `HexadecimalDigits`. A hexadecimal
token's `digits` field excludes `0x`. For `SP0001`, `found` is `null` exactly at
end of file and otherwise preserves the complete found token kind and payload.
English prose, pretty-printing, and diagnostic layout are not normative
observations.

### Oracle v4 and capability publication

Publish `solcore-oracle/v4` and `solcore-capabilities/v4`. An Oracle v4 request
is the closed object with fields `schema`, `id`, `spec`, `profile`, `limits`,
and `query`. Oracle v4 supports exactly these query objects:

- `{ "kind": "capabilities" }`; and
- `{ "kind": "parse", "source": { "path": string, "content": string } }`.

The request envelope is bound to `solcore/0.1.0-draft.4` and the canonical
`frontend-m2b-v1` profile ID and digest. The limits object is closed and contains
only the required `sourceBytes` field. The closed response has fields `schema`,
`id`, `spec`, `profile`, `query`, and `verdict`; it repeats the request ID,
specification ID, profile reference, and query kind as in prior Oracle versions.
The only verdict shapes are accepted capability or parse results, the
single-diagnostic rejected result described above, `sourceBytes` inconclusive,
and the internal errors described below.

Every verdict object is closed. The two accepted forms have exactly the fields
`kind`, `phase`, and `result`:

```text
{
  "kind": "accepted",
  "phase": "protocol",
  "result": {
    "schema": "solcore-capabilities/v4",
    "value": capability-report-v4
  }
}

{
  "kind": "accepted",
  "phase": "surfaceParsing",
  "result": {
    "schema": "solcore-parse-result/v1",
    "value": surface-file-v1
  }
}
```

The rejected form has exactly `kind`, `phase`, and `diagnostics`:

```text
{
  "kind": "rejected",
  "phase": "surfaceLexing" | "surfaceParsing",
  "diagnostics": [surface-diagnostic-v1]
}
```

The `diagnostics` array has both minimum and maximum length 1, and the sole
diagnostic's phase equals the verdict phase. The `sourceBytes` inconclusive form
has exactly `kind`, `phase`, `resource`, `limit`, and `consumed`:

```text
{
  "kind": "inconclusive",
  "phase": "sourcePreflight",
  "resource": "sourceBytes",
  "limit": nat,
  "consumed": nat
}
```

`consumed` is never null in this form; preflight reports the exact UTF-8 byte
length already measured, so it is strictly greater than `limit`. This is exact
demand, not a count of work performed before exhaustion. The Oracle v4 schema
and validator therefore explicitly do not apply the Oracle v2/v3 validation
rule `consumed <= limit` to this verdict. The internal-error form has exactly
`kind`, `phase`, and `code`, and is closed to these combinations:

```text
{ "kind": "internalError",
  "phase": "surfaceLexing" | "surfaceParsing",
  "code": "frontend-invariant" }

{ "kind": "internalError",
  "phase": "surfaceEncoding",
  "code": "surface-wire-projection-failed" }

{ "kind": "internalError",
  "phase": null,
  "code": "oracle-response-invariant" }
```

The closed v4 capability report has exactly these fields:

| Field | Fixed meaning |
| --- | --- |
| `schema` | `solcore-capabilities/v4` |
| `spec` | `solcore/0.1.0-draft.4` |
| `profile` | The complete canonical `frontend-m2b-v1` profile |
| `profileDigest` | The canonical profile digest |
| `surfaceSchema` | `solcore-surface/v1` |
| `parseResultSchema` | `solcore-parse-result/v1` |
| `baselines` | The unchanged implementation baselines |
| `implementedQueries` | `["capabilities", "parse"]` |
| `features` | The complete M2b frontend matrix, containing only the `surfaceGrammar` row |
| `defaultLimits` | `{ "sourceBytes": 1048576 }` |

It does not advertise a Semantic Core input, a check-result schema, a value
observation, or any resolver, checker, elaborator, or evaluator query. The
capability accepted result uses the same `{ "schema", "value" }` payload
convention as prior versions, with schema `solcore-capabilities/v4` and the
report above as its value.

The v4 phase set is closed to:

```text
protocol, sourcePreflight, surfaceLexing, surfaceParsing, surfaceEncoding
```

`capabilities` succeeds at `protocol`; `parse` succeeds at `surfaceParsing`.
Source-byte exhaustion is inconclusive at `sourcePreflight`. Source rejections
occur only at `surfaceLexing` or `surfaceParsing`.

The NDJSON dispatcher selects v1, v2, v3, or v4 solely from the top-level
`schema`. One argument-free stream may mix all four versions. A v4 request
cannot use a v1 through v3 profile or digest, and an older request cannot use
the M2b profile. Unknown v4 query kinds are protocol errors because the v4 query
union is closed; they do not change the meaning of similarly named queries in
older versions.

A protocol failure uses the closed prior-version shape with kind
`protocolError`, schema `solcore-oracle/v4`, nullable request `id`, stable
`code`, JSON-pointer-like `path`, structured `arguments`, and nonnormative
`display`. It is outside the response verdict union. Oracle v4 has no
`unsupported` or `executed` result because its closed query set contains only
the two implemented static queries.

The immutable binding matrix becomes:

| Oracle | Language | Profile | Successful non-capability input |
| --- | --- | --- | --- |
| `solcore-oracle/v1` | draft.1 | `core-v1` | none |
| `solcore-oracle/v2` | draft.2 | `core-m1a-v1` | `solcore-semantic-core/v1` |
| `solcore-oracle/v3` | draft.3 | `core-m1c-v1` | `solcore-semantic-core/v2` |
| `solcore-oracle/v4` | draft.4 | `frontend-m2b-v1` | one raw SourceFile for `parse` |

Oracle v1 `parse` remains unsupported. Oracle v2 and v3 remain Core-only. A
future workspace, resolver, checker, or source-evaluation query requires a new
profile and Oracle version.

### Internal failures and protocol separation

Malformed wire data and profile/version mismatches produce `protocolError`
before language execution. Valid but over-limit source content produces
`inconclusive`. `SL0001`, `SL0002`, `SP0001`, and `SP0002` are the only M2b
source rejection codes.

An internal lexer or parser invariant is an `internalError` with code
`frontend-invariant` and phase `surfaceLexing` or `surfaceParsing`, respectively.
A successful internal AST that cannot be projected to
`solcore-surface/v1` is an `internalError` at `surfaceEncoding` with code
`surface-wire-projection-failed`. A response assembled by the Oracle that fails
its own final validator is an `internalError` with code
`oracle-response-invariant` and a null phase. These conditions are
implementation defects. They must never be converted to `rejected`, assigned
an `SL` or `SP` code, or blamed on source text.

The frontend proofs make lexer fuel exhaustion, lexer invalid output, parser
fuel exhaustion, parser invalid input, and parser invalid output unreachable
for public execution. The publication proofs also show that every successful
parser result projects to v1, making `surface-wire-projection-failed`
unreachable for draft.4. The defensive cases still map to `internalError`,
never to a source rejection, and remain in the protocol so that later internal
growth fails closed if the corresponding proof or mapping is not extended.

### Compatibility and immutability

M2b is additive. It must not alter any draft.1, draft.2, or draft.3 language
object, known-feature array, profile JSON, canonical profile digest, feature
matrix, schema, capability record, CLI output, request or response behavior, or
golden NDJSON byte. Semantic Core v1 and v2 and Oracle v1 through v3 remain
closed under their existing contracts.

The global profile manifest appends `frontend-m2b-v1`, and only the draft.4
`knownFeatures` array appends `surfaceGrammar`; neither operation mutates a
legacy array. The frontend profile's enabled features and feature matrix are
new one-element scoped arrays, not extensions of the M1 arrays.
`solcore-surface/v1`, `solcore-parse-result/v1`, Oracle v4, and the v4 capability
document are independently versioned artifacts. Any later Surface constructor,
grammar rule, diagnostic shape, multi-file input, or query requires a new
compatible version or an explicitly accepted breaking-version decision; it
cannot widen a v1 schema in place.

## Consequences

- Differential fuzzers can obtain a canonical, proof-connected parse result
  for the same raw single-file source supplied to another implementation.
- Parsing becomes normative without assigning meaning to any name, type
  spelling, integer, call, operator, or function envelope.
- UTF-8 spans, comments, grouping, raw literal spelling, and source order remain
  available to later resolution and elaboration stages.
- Source-size exhaustion is distinguishable from invalid syntax, malformed
  protocol data, and an Oracle defect.
- Opaque path labels allow isolated fixtures without prematurely deciding
  workspace identity or filesystem safety.
- Closed wire types and partial internal projection prevent future Lean AST
  growth from changing a published result silently.
- Core differential testing continues through Oracle v2 and v3; Oracle v4 is a
  separate frontend-only boundary.

## Conformance requirements

- Add canonical draft.4 language, `frontend-m2b-v1` profile, feature-matrix,
  manifest, digest, and capability artifacts without changing prior bytes.
- Implement strict, closed decoders and canonical encoders for every
  `solcore-surface/v1` type, parse expectation, token kind, diagnostic, parse
  result, Oracle v4 request, response, and capability value.
- Implement the refined `IdentifierText`, `DecimalDigits`,
  `HexadecimalDigits`, and `TypeSpelling` wire atoms with executable validators,
  proof-carrying constructors, total canonical encoders, positive round trips,
  and negative lexical-payload tests.
- Define executable Surface node-count and depth measures with the scope fixed
  above. Require explicit `maxDepth` and `maxNodes` on every Surface and parse
  result decode path, and test exact-at-limit and one-over-limit behavior.
- Prove decoder-after-encoder round trips for all closed v1 wire types whenever
  the selected decoder limits contain the encoded value, and prove bounded
  canonicalization idempotent. Keep encoding total and canonical without a
  resource premise. Test every constructor, operator, token kind, expectation,
  comment kind, and nullable field.
- Provide a total v1-wire-to-internal embedding and a partial
  internal-to-v1 projection. Prove projection after embedding is identity and
  prove every successful draft.4 parser result projects successfully.
- Connect every accepted Oracle v4 parse result to the existing
  `LexicalGrammar.Lexes`, `FileParses`, source validity, grammar validity, and
  exact token-correspondence results. Retain reverse executor completeness,
  lexical uniqueness, determinism, failure reachability, and fuel sufficiency.
- Test one source at 1048575, 1048576, and 1048577 UTF-8 bytes, plus a
  multibyte source whose scalar count and UTF-8 byte count differ. Verify that
  the path and JSON envelope bytes are excluded from `sourceBytes`. For the
  over-limit case, verify `consumed` is the exact demand, is greater than the
  limit, and is accepted by the v4 response validator independently of the
  v2/v3 consumed-count rule.
- Test a zero limit with empty and nonempty content and verify that preflight
  exhaustion is `inconclusive`, never `rejected`.
- Test exact code, phase, span, and structured arguments for a lexically invalid
  ASCII character, a lexically invalid multibyte scalar, an unterminated nested
  block comment, an unexpected token, unexpected end of file, and a repeated
  equality and relational operator.
- Test opaque nonempty path labels, including absolute-looking, dot-segment,
  separator-containing, and Unicode spellings, and verify exact echoing without
  normalization. Reject an empty path as a protocol error.
- Reject unknown and extra fields, missing fields, unknown tags, invalid
  tag-specific fields, negative or non-integral offsets, invalid lexical
  payloads, wrong profile digests, and cross-version schema/profile bindings.
- Add positive, source-negative, malformed-record, resource, cross-version, and
  mixed v1/v2/v3/v4 NDJSON golden cases. Continue processing records after a
  malformed record.
- Classify every unchecked parser failure and prove that public parser
  invalid-input and invalid-output classifications are unreachable, in addition
  to the existing lexer fuel, lexer invalid-output, and parser fuel theorems.
- Prove, and test, that public draft.4 requests cannot produce
  `frontend-invariant` or `surface-wire-projection-failed`; retain both mappings
  as defensive `internalError` cases.
- Keep the semantic kernel free of `sorry`, `admit`, `partial`, `unsafe`, IO,
  host parser libraries, and undeclared axioms.
- Verify that every existing draft.1 through draft.3 profile, schema,
  capability, CLI output, and golden-manifest byte remains unchanged.
