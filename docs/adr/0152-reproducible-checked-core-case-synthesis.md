# ADR-0152: Reproducible Checked-Core Case Synthesis

- Status: Accepted
- Decision date: 2026-08-30
- Scope: syntax-independent generation, replay, execution, and shrinking
- Implementation: In progress

## Context

ADR-0151 completed a public syntax-independent boundary for checking Semantic
Core Wire v3 programs and executing admitted checked contracts from an explicit
finite scenario. The next long-term goals are to synthesize well-typed programs
and to use them for semantic differential testing.

Those goals do not require a stable Surface grammar. Core Wire v3 is already a
closed, versioned generation target, its checker is executable and proved
sound, and Oracle v5 already carries every initial condition and total result
needed by a first generated execution case.

Generating arbitrary raw trees and discarding checker failures would be a poor
foundation. It would reject most binder-rich trees, distort coverage toward
easy constructors, and make shrinking routinely destroy typing. Conversely, a
fully dependent generator for the complete current Core would make the first
executable slice unnecessarily large.

## Decision

Add `Solcore.Synthesis.CoreV3`, an additive library for reproducible generated
Core v3 execution cases. The first vertical slice is called G0 and consists of:

1. a fixed pure pseudo-random source;
2. a bounded type-directed Word/Boolean expression generator;
3. a checker-sealed generated Word Program;
4. a deterministic type-preserving shrinker;
5. a minimal valid Oracle v5 execution request; and
6. public-handler replay and coverage regressions.

This library consumes the existing Core v3 and Oracle v5 contracts. It does not
widen or reinterpret either wire version.

## Reproducible choices

G0 owns a versioned 64-bit linear-congruential sequence. Its multiplier,
increment, wrapping arithmetic, draw order, and bounded-choice rule are fixed in
code and covered by exact vectors. A caller supplies the initial 64-bit seed and
a maximum Program-node count of at least three. Three is the exact size of the
fixed Word result type, empty Program wrapper, and one-node body.

The same generator version, seed, and node bound must produce the same:

- final generator state;
- Core Wire v3 Program;
- canonical Program JSON;
- Oracle v5 request; and
- canonical request text.

Generator size and evaluator fuel are separate inputs. A syntax-node limit is
not interpreted as fuel consumed, remaining gas, or an execution-cost formula.

## Initial typed fragment

Every G0 Program has:

- result type `word`;
- no named data definitions;
- a body generated against the frozen Core v3 host context; and
- no generated host-function reference.

The internal target types are Word and Boolean. The fragment contains:

- Word and Boolean literals;
- in-scope Word variables introduced by generated Word `let` bindings;
- Word `let` and Word/Boolean `if` expressions;
- `boolNot`, `wordNot`, and `wordClz`;
- all current Word binary operations, with equality and signed/unsigned
  comparisons producing Boolean results; and
- `wordAddMod` and `wordMulMod`.

The body receives the Program bound minus its two fixed wrapper nodes. Child
node budgets partition the parent's remaining budget. Every recursive call
receives a smaller positive budget, so the generated Program contains no more
nodes than requested. A bound below three is rejected as a configuration error
rather than silently widened.

This fragment is effect-free and non-recursive. Every checker-accepted G0
contract therefore has a normal Word return for sufficient evaluator fuel.

## Checker sealing

Generation first constructs a type-directed Wire candidate and then invokes the
existing frozen v3 checker. A constructor-private `CheckedWordProgram` stores a
Word Program and evidence that `Program.check = true`. A separate
`GeneratedProgram` pairs that checked value with its seed, bounds, and final
generator state.

Checker rejection is a generator invariant failure. It is never ordinary
sampling discard and it never returns an unchecked Program. Separating the
checked value from generation provenance also prevents a shrunk Program from
falsely retaining the seed metadata of its parent. This hybrid keeps the
initial generator executable while allowing later constructor-specific typing
proofs to replace the dynamic invariant check incrementally.

## Shrinking

Shrinking operates on typed expression roles, not raw JSON. It may:

- replace a non-canonical literal with the canonical zero or false literal;
- select an in-scope same-type child when binding scope permits; or
- shrink one child while rebuilding its typed parent.

Every candidate is checked again and sealed through the same private boundary.
Candidates must be strictly smaller under the fixed G0 lexicographic complexity
order, whose primary component is expression-node count and whose secondary
component is the sum of Word literal values plus one for each true Boolean
literal. Candidate order is deterministic. Shrinking does not mutate a scenario
independently of its Program.

## Generated Oracle case

A `GeneratedCase` embeds one `GeneratedProgram` into a fixed minimal Oracle v5
scenario:

- one `checkedCore` contract with a stable identifier;
- one explicitly present target Account containing that contract;
- zero balance, nonce, call value, and calldata;
- empty call and creation registries;
- an explicit inert creation-address default; and
- one stable target-code probe.

The request retains the caller-supplied evaluator-fuel limit and uses all other
Oracle v5 default limits. Public replay encodes canonical request text, invokes
the strict text handler, and returns the existing typed `Response`. A regression
also passes that same line through the public one-record Oracle dispatcher used
by the command-line executable. G0 does not call an internal evaluator directly
as its conformance endpoint.

## Coverage and replay

Coverage is structural and explicit. It records every G0 expression form and
every included unary, binary, and ternary operator. A fixed seed corpus must
cover the complete G0 catalog rather than relying on an unspecified random
distribution.

A replay failure records at least the generator version, seed, node bound,
evaluation fuel, and canonical request text. Persistent corpus packaging and
parallel process scheduling may be added later without moving Core typing rules
outside Lean.

## Required proofs and executable regressions

G0 is complete when tests establish:

- exact pseudo-random vectors and bounded-choice behavior;
- same-input generator and canonical-byte determinism;
- below-minimum-budget rejection and the Program-node bound;
- checker acceptance for every generated Program;
- no unchecked public constructor or fallback Program;
- deterministic, checker-accepted, strictly smaller shrink candidates;
- successful preparation of every generated minimal scenario;
- normal returned execution through the strict public Oracle v5 text handler
  at the declared regression fuel;
- exact response decoding and repeated-response equality;
- zero protocol errors, admission rejections, and internal errors across the
  fixed corpus; and
- complete constructor and operator coverage for the G0 fragment.

Full build, test, metadata, semantic-kernel, axiom, and diff-hygiene checks
remain required.

## Exclusions and next boundary

G0 does not generate functions, products, sums, cells, named data, host effects,
nested calls, creation, logs, malformed Programs, or arbitrary scenarios. Those
features are added to the generator in later vertical slices while preserving
G0 seeds and bytes for its fixed version.

G0 also does not provide an independent implementation. Comparing the Lean
Oracle with itself proves replay and transport consistency, not cross-compiler
semantic agreement. True differential testing requires a Haskell, Rust, or
other independent adapter that consumes the same Core v3 case and returns a
compatible normalized observation.

Surface parsing, name resolution, source typing, source elaboration, and a
Core-to-source printer remain paused. General call-stack semantics, complete
state-footprint discovery, call tracing, dynamic ABI, EVM memory, gas, and fork
rules are separate decisions.
