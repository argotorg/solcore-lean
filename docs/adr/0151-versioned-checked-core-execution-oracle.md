# ADR-0151: Versioned Checked-Core Execution Oracle

- Status: Accepted
- Decision date: 2026-08-30
- Scope: syntax-independent Core checking and contract execution
- Implementation: Planned

## Context

ADR-0145 through ADR-0149 complete the internal executable lifecycle from an
explicit `WorldState`: root commit and rollback, depth-one checked calls,
checked balance transfer, checked creation, rollback-aware logs, exact state
queries, and fuel-only resumption. ADR-0150 adds a complete Static Word ABI and
routes raw calldata through that same lifecycle.

These APIs are proof-indexed Lean values. They cannot yet be used by an
independent implementation for semantic differential testing. Existing Oracle
v1 through v3 publish older closed Semantic Core profiles, and Oracle v4
publishes the frozen Surface parser. Extending any of those schemas would break
their closed-algebra guarantees.

Concrete Solcore syntax and source storage layout remain intentionally frozen.
They are not prerequisites for publishing the checker and executor that already
operate over syntax-independent Core programs and exact Word storage slots.

## Decision

Add two new, additive publication boundaries:

1. Semantic Core Wire v3, a closed representation of the current internal Core;
2. Oracle v5, with `capabilities`, `coreCheck`, and `execute` queries.

Oracle v5 decodes untrusted JSON into finite wire values, reconstructs ordinary
Core programs, obtains checked contracts only through the executable checker or
ADR-0150 admission, materializes an explicit finite world and immutable
execution environment, and delegates execution to
`BalancedTopLevelExecution.runWithEnvironment`.

There is no second evaluator, ABI dispatcher, state-transition function, or
rollback policy in the Oracle layer. Every response is a finite observation of
the existing total result.

## Semantic Core Wire v3

Wire v3 is a new closed algebra. It represents exactly the current internal:

- Core types, including products, functions, sums, cells, and named data;
- data-definition and constructor identities;
- unit, Boolean, Word, variable, product, function, sum, cell, named-data,
  unary, binary, ternary, binding, and conditional expressions; and
- every current unary, binary, and ternary operator.

The type tags are `unit`, `bool`, `word`, `product`, `function`, `sum`, `cell`,
and `namedData`. Expression tags are `unit`, `bool`, `word`, `var`, `pair`,
`first`, `second`, `lambda`, `apply`, `inLeft`, `inRight`, `case`, `newCell`,
`loadCell`, `storeCell`, `construct`, `matchData`, `unary`, `binary`, `ternary`,
`let`, and `if`. Operator names are the existing three unary, nineteen binary,
and two ternary Core constructor names. Primitive types retain the v2 string
form; composite types and expressions use tagged objects. A Program has exactly
`schema`, `resultType`, `dataDefinitions`, and `body`. The complete field and
operator catalog is frozen in [Core Wire v3](../CORE_WIRE_V3.md).

Host capabilities are not a special wire expression. Wire v3 owns this exact
index order: `storageRead`, `storageWrite`, `storageAddress`, `codeAddress`,
`callValue`, `callerAddress`, `inputDataByte`, `inputDataSize`,
`inputDataWordBE`, `currentAddress`, `callContractWord`,
`callContractWordWithValue`, `createContractWord`, and `emitLogWord`. It freezes
their parameter/result types and matching runtime host values, not merely the
number 14. Binders prepend locals, so host indices shift beneath a lambda, let,
case, or match branch in the ordinary de Bruijn way.

Admission proves that the frozen typed context and runtime values are the
corresponding prefix of the current append-only host tables, then transports
accepted typing into the current checker. It must not simply call
`Program.checkHost` on unbounded wire input: a later appended host function
would otherwise become silently usable by the published v3 schema. At the
program root, free index 14 is rejected; under binders, the checker rejects the
correspondingly shifted free index outside the frozen 14-entry suffix.

The wire-to-Core conversion is total. The Core-to-wire projection returns
`Option`, so a future internal constructor or operator is rejected until a new
wire decision assigns it meaning. Prove wire/Core round trips for every covered
type, definition, operator, expression, and program.

Canonical JSON uses explicit tags, `0x` plus exactly 64 lowercase Word digits,
`0x` plus exactly 40 lowercase Address digits, `0x`-prefixed even-width
lowercase Bytes, and arrays in semantic order. Natural-number decoding retains
`Foundation.jsonNatural?` mathematical semantics; encoding emits an integer.
Structural decoding rejects unknown or missing fields, invalid tags, and invalid
scalars with an exact JSON-pointer path.

Oracle limits are `jsonDepth`, `jsonNodes`, `coreDepth`, `coreNodes`,
`scenarioEntries`, `identifierBytes`, `calldataBytes`, and `evaluationSteps`,
with defaults 2048, 2000000, 1024, 1000000, 100000, 256, 1048576, and 1000000.
JSON limits apply to the complete parsed request, including unknown subtrees.
Core limits independently aggregate every Wire v3 program in one request;
scenario entries aggregate all non-byte finite lists;
more precisely, scenario entries count lists outside Core Programs, whose inner
lists are already counted as Core nodes. The identifier limit applies separately
to each UTF-8 request ID, ASCII contract ID, and ASCII method name. Zero is a
valid budget. Limit validation requires `calldataBytes < 2^256`; together with
the actual-size preflight this constructs `InputData` without a fallback.

Exceeding a declared budget is `inconclusive`, not a protocol error. After the
existing strict JSON parser identifies v5, validation first recovers and checks
the shallow schema, request ID, profile, and complete limits object. Generic
JSON depth and node traversal then counts even unknown subtrees, so they cannot
bypass declared JSON budgets. Exact Oracle structure and scalar decoding comes
next. The Core decoder consumes one typed depth/node unit before validating each
expected Program, DataDefinition, Type, or Expression node. If counting that
node would make demand exceed the limit, `inconclusive` precedes validation of
the node; demand equal to the limit still validates it and may produce a
protocol error.
Scenario-entry, identifier-byte, and calldata-byte measurements follow complete
structural decoding and precede semantic admission. This ADR does not change the
raw NDJSON transport behavior of older versions. Capabilities reports every
limit and count rule.

A fixed shallow envelope decoder reads and validates the complete `limits`
object before budgeted traversal. A missing, malformed, or out-of-range limit is
a protocol error; there is no attacker-selected fallback to the defaults.

Wire v1 and v2 remain unchanged and must continue to reject every constructor or
operator outside their frozen profiles.

## Oracle v5 queries

The schema discriminator is `solcore-oracle/v5`. Its query kinds are:

- `capabilities`: report the exact v5 query set, Core Wire v3 identifier,
  contract profiles, ABI profile, limits, execution depth, and observation
  kinds;
- `coreCheck`: decode one Wire v3 program and run the host-aware Core checker;
- `execute`: admit a finite contract package and explicit runtime scenario,
  then run one top-level invocation.

The complete request, response, diagnostic, and observation field catalog is
frozen in [Oracle v5 wire catalog](../ORACLE_V5_WIRE.md).

`coreCheck` accepts any checker-valid host-aware Core program, including a
`word -> word` method implementation that is not itself a contract entry. A
rejection carries the existing detailed checker path and reason. Acceptance
reports the exact declared result type; it does not execute the program.

Implement a context-parameterized detailed Program checker and specialize it to
the frozen v3 host context. Its success is equivalent to the frozen Boolean
check and promotes to current `Program.checkHost = true`. Host-aware failures
therefore preserve the existing detailed path and reason rather than collapsing
to a generic ill-typed error.

An `execute` query always performs the same checking again while admitting its
contract package. A client cannot assert that an unchecked program is checked,
and no proof or `Bool` witness crosses the wire.

## Contract package and admission

Every contract definition has a unique validated opaque identifier and one of
two specifications:

- `checkedCore`: one Wire v3 program whose checked result type is exactly
  `word` (`returnWord`) or `sum(word, sum(word, word))` (`wordOutcomeV1`);
- `staticWordAbi`: a nonempty list of validated method names and Wire v3
  implementations, admitted by ADR-0150 as `uint256 -> uint256` methods.

Static Word method input contains only its name and implementation. Input type,
output type, canonical signature, and selector are derived by ADR-0150 and are
never accepted as redundant caller-controlled fields.

Both variants first use the Wire v3 frozen-host checker and its proved promotion
to `CheckedHostCoreProgram`. For `checkedCore`, v5 owns the closed two-entry
profile table above and constructs `CheckedCoreContract.returnWord` or
`CheckedCoreContract.wordOutcomeV1` directly. It must not delegate profile
selection to the future-growing `CheckedCoreContract.ofCode?` recognizer.
`staticWordAbi` delegates to
`WordImplementation.ofCode?` and `StaticWordContract.admit`. Unsupported entry
result types, ill-typed method implementations, a method result other than
`word -> word`, nonempty method data definitions, empty tables, duplicate
signatures, and selector collisions are distinct structured admission
rejections. No runnable contract is produced on rejection.

All later references use contract identifiers and resolve only against the
admitted package. Duplicate identifiers and dangling references are rejected
before materializing a world. After admission, underlying checked code Programs
must also be pairwise distinct, including across raw and generated ABI variants;
aliases are rejected so every installed code endpoint has one canonical package
identifier.

## Finite world and immutable environment

The request represents an initial `WorldState` as a finite list of unique
accounts. Each account contains:

- an exact Address;
- an exact Word balance and nonce;
- unique sparse `(slot, value)` entries, with stored zero rejected; and
- an optional admitted contract identifier for checked code.

Materialization starts from `WorldState.empty`, builds each Account only through
the existing public operations, and inserts it with `putAccount`. Prove exact
lookup, balance, nonce, storage, and code provenance for every admitted entry,
plus absence for addresses outside the finite input.

The immutable `ExecutionEnvironment` is built from three finite inputs:

- unique address-to-contract bindings for checked nested-call resolution;
- unique Word identifiers mapped to admitted initializer/runtime pairs; and
- an explicit total creation-address policy.

The creation policy is a finite set of unique `(creator, nonce) -> address`
routes plus one required default Address. This publishes the exact injected
policy without pretending that the current semantics implements an
EVM-revision-specific creation hash. Registry resolution still checks that the
selected contract's exact code is installed in the current world, so an absent,
stale, or mismatched binding remains an ordinary semantic `unavailable` result.

## Invocation and bounded execution

One invocation supplies target, caller, call value, arbitrary raw calldata, and
state probes. `limits.evaluationSteps` is the sole execution-fuel budget. The
root contract is derived from the target Account's
contract identifier rather than repeated in the invocation. Admission requires
an exact installed-code witness for that contract. Root-installation rejection
is exactly `targetAbsent` or `targetCodeAbsent`; materialization makes a present
reference's code exact by construction. This is pre-execution input rejection,
not a trap or balance preflight failure.

Raw calldata deliberately covers valid ABI calls, suffixes, short input, unknown
selectors, and non-ABI checked contracts. Static Word convenience encoding
remains available in the Lean API; the public execution request does not need a
second method selector language.

The handler invokes `BalancedTopLevelExecution.runWithEnvironment` exactly once.
A top-level balance preflight failure is an executed terminal status with an
identity committed state, distinct from malformed input or failed contract
admission. Return, revert, and trap retain their existing meanings. Fuel
exhaustion is the outer `inconclusive` verdict at contract-execution phase with
resource `evaluationSteps`, and limit and consumed both equal to the supplied
limit. It is not a terminal execution observation. V5 publishes no resumable
machine token. A client may repeat the immutable request with a larger budget,
while the internal exact resumption laws remain the specification evidence.

## Public execution observation

Every terminal execution observation is one tagged value:

- preflight rejection with its exact `BalanceTransferFailure`;
- returned with canonical returndata bytes;
- reverted with canonical revertdata bytes; or
- trapped with its exact Word reason.

Terminal and preflight results include the committed ordered Word logs and
successfully created Addresses. Revert, trap, and preflight rejection therefore
publish the empty committed journal selected by the existing root policy. The
separate inconclusive fuel result has no journal or final state and must not
fabricate an identity transition.

`WorldState` and `WorldStateDelta` are function-valued, so v5 does not claim to
enumerate an unknowable global change set. Instead, the request carries a finite
ordered list of exact probes:

- account presence;
- storage at one Address and slot;
- balance at one Address;
- nonce at one Address; and
- checked code at one Address.

For every terminal or preflight result, the response returns each probe's exact
initial and committed endpoint. Account presence is Boolean; storage, balance,
and nonce use nullable Words; code uses the nullable canonical contract ID
established by package code uniqueness, so replacement is distinguishable from
presence alone. These values delegate
to the existing `WorldStateDelta` queries. This is the public finite form of the
current exact, pointwise state-difference contract. Probe order is preserved;
duplicate probes are rejected to keep one canonical observation per point.

Committed logs are encoded in chronological order as exact `emitter` Address,
`topic` Word, and `payload` Word triples. Created Addresses are likewise
chronological. Both arrays preserve duplicates.

## Profile identity

Add `checkedCoreStateV1` to `ObservationPolicy` and allow it only for contract
scope with `contractRuntime = none`. Oracle v5 binds language
`solcore/0.1.0-draft.5` to profile `contract-m3a-v1`, with static and dynamic
semantics version 3, ABI version 1, and no grammar or storage-layout version.
Core Wire, capability, check-result, execution, and state schemas are
respectively `solcore-semantic-core/v3`, `solcore-capabilities/v5`,
`solcore-core-check-result/v3`, `solcore-contract-execution/v1`, and
`solcore-world-state-observation/v1`.

Append exactly these v5-only normative Feature values: `coreProductsV1`,
`coreFunctionsV1`, `coreSumsV1`, `coreLocalCellsV1`, `coreNamedDataV1`,
`coreExtendedWordOperationsV1`, `checkedContractExecutionV1`, and
`staticWordAbiV1`. Do not change the maturity or rows of the older generic
`functions`, `contracts`, `externalAbi`, or `storage` features. Define a v5-only
feature matrix. `knownFeatures` is `m1cAll` followed by those eight values;
`enabledFeatures` is the nine existing normative M1c Core values followed by
those eight values, in that order. The fixed digest covers the complete
`SpecProfile` JSON using the existing `lean-json-compress-sha256-v1` manifest
algorithm. All older profile values and digest constants remain byte-for-byte
unchanged.

## Strict protocol and compatibility

Request and response codecs are canonical and total. Decode failures are
protocol errors with recoverable request identifiers where possible. Well-formed
requests that fail Core checking, ABI admission, identifier resolution, finite
world validation, or root installation return typed rejected verdicts. The
handler must not turn any of these into `internalError`.

The outer result partition is closed: malformed shape or scalar is
`ProtocolError`; declared decode/preflight budget excess is `inconclusive`;
Core, ABI, package, world, or root-install failure is `rejected`; an admitted
terminal run is `executed`; and an admitted fuel-exhausted run is
`inconclusive`. Only `executed` carries the terminal observation.

Contract IDs are byte-exact ASCII labels matching
`[A-Za-z_][A-Za-z0-9_.-]*`; method names retain ADR-0150's stricter grammar.
After scalar decoding, keyed input arrays are sorted by their full key before
duplicate and reference validation, and the encoder emits that canonical order.
Logs, created Addresses, and probes retain semantic/request order instead.

Validation selects the first failure in this order: strict transport and
shallow schema/ID/profile/limits recovery; whole-tree JSON budgets; exact Oracle
structure and scalars; budgeted Core wire decoding; scenario, identifier, and
calldata measurements; contract identifiers and admission; account and
sparse-storage validation; registry, template, and creation-policy validation;
probe validation; root installation; then execution. This order is part of
deterministic diagnostics.

The NDJSON dispatcher selects v5 only by its exact schema discriminator. Add a
`capabilities-v5` CLI command without changing the meaning or encoding of any
v1-v4 request, response, capability report, profile digest, or existing CLI
command. Help gains only the additive `capabilities-v5` line.

## Required proofs and executable regressions

Implementation is complete when external consumers and runtime tests cover:

- complete Wire v3 conversion and canonical JSON round trips;
- every tag, scalar, unknown-field, depth, node, and collection boundary;
- host checker acceptance/rejection with detailed diagnostic preservation;
- raw and Static Word contract admission and exact admitted-code provenance;
- duplicate/dangling package, account, storage, registry, template, route, and
  probe rejection before execution;
- exact finite WorldState and ExecutionEnvironment materialization;
- root installation success and every failure class;
- raw ABI return, short-input revert, and unknown-selector revert;
- storage, balance, nested call, creation, logs, returndata, and exact probe
  endpoints on commit and rollback;
- preflight rejection and zero/mid-execution fuel exhaustion;
- deterministic repeated execution at the same budget;
- v1-v4 byte-for-byte regression fixtures and old-wire rejection; and
- full build, executable suite, warnings-as-errors, trust-zero, metadata,
  semantic-kernel, axiom, and diff-hygiene checks.

## Exclusions and next boundary

This decision does not publish Surface syntax, parsing, name resolution, source
typing, source storage layout, or Surface-to-Core elaboration. It does not add
dynamic ABI types, fallback/receive methods, ABI events, multiple call depth,
delegate/static calls, gas accounting, EVM bytecode, an EVM creation-address
formula, or a serialized resumption token.

Oracle v5 is an executable formal-spec interface for the current checked Core
and runtime semantics. It is not a claim of full Solidity or EVM compatibility.
After this vertical milestone is complete, the next implementation direction is
chosen separately; parser work remains paused until explicitly resumed.

Publishing the full current Core algebra is deliberate. A smaller contract-only
subset could exercise the present runtime, but it would not meet the accepted
goal of checking arbitrary Core candidates and executing every admitted
contract profile for differential testing. Wire v3 also gives later synthesis
work a complete target and a checker endpoint; this milestone does not itself
generate programs. Arbitrary checker-valid non-contract result types are checked
but are not executed until a matching execution profile is separately defined.
