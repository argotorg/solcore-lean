# ADR-0011: M1c primitive semantics

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M1c Semantic Core

## Reader summary / Current implementation

- **Decision:** Add the closed boolean/word primitive set with exact arithmetic
  edge cases and left-to-right, exactly-once evaluation.
- **Current implementation:** Primitive typing and execution, correspondence
  and safety proofs, and executable tests are complete.
- **Boundary:** Short-circuit source operators, functions, conversions, ADTs,
  source elaboration, and unlisted primitives remain outside M1c.
- **Suggested reading:** Read the primitive signature and operation tables in
  “Decision”, then the conformance requirements.

## Context

M1a and M1b defined a typed and executable Semantic Core containing literals,
immutable bindings, and conditionals. Primitive operations remained outside the
normative fragment because their arithmetic edge cases and operand order had
not been fixed independently of either compiler.

The implementation audit used these pinned witnesses:

- Haskell Solcore at `1d490d8bb5f374356f06e0720655496482eb1fb4`
- Rust Solcore at `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`

The Haskell parser and resolver expose arithmetic, comparison, bitwise, and
boolean operators in
`src/Solcore/Frontend/Parser/Expr.hs:52-113` and
`src/Solcore/Frontend/Syntax/NameResolution.hs:794-882`. The standard-library
definitions in `std/std.solc:232-523` identify the common word basis and derive
`ne`, `lt`, `le`, and `ge` from equality, unsigned greater-than, and boolean
negation. The Rust equivalents are in
`crates/parser/src/parse/expr_pat.rs:256-379`,
`crates/hir/src/ast/function.rs:396-442`, and `std/std.solc:228-519`.

The executable witnesses agree on modular word arithmetic, unsigned
division/comparison, 256-bit bitwise operations, and ordinary eager operand
evaluation. They contain defects or incomplete behavior that must not become
normative merely because it exists:

- both primitive tables give a direct `eqWord` builtin the wrong result type,
  although the standard-library declaration and evaluators return `bool`;
- the Haskell partial evaluator implements only a subset of the operations;
- sufficiently large Haskell shifts can pass through a host `Int`, whereas the
  Rust implementation and EVM rule return zero;
- both standard libraries implement `and` and `or` as eager functions while
  explicitly recording that they should short-circuit.

## Decision

### Primitive signatures

Add two closed operator families to Core.

Unary operations:

| Operation | Signature | Result |
| --- | --- | --- |
| `boolNot` | `bool -> bool` | boolean negation |
| `wordNot` | `word -> word` | complement of all 256 bits |

Binary operations:

| Operation | Signature | Result |
| --- | --- | --- |
| `wordAdd` | `word × word -> word` | sum modulo `2^256` |
| `wordSub` | `word × word -> word` | difference modulo `2^256` |
| `wordMul` | `word × word -> word` | product modulo `2^256` |
| `wordDiv` | `word × word -> word` | unsigned quotient; zero divisor gives zero |
| `wordMod` | `word × word -> word` | unsigned remainder; zero divisor gives zero |
| `wordEq` | `word × word -> bool` | word equality |
| `wordGt` | `word × word -> bool` | unsigned greater-than |
| `wordAnd` | `word × word -> word` | 256-bit conjunction |
| `wordOr` | `word × word -> word` | 256-bit disjunction |
| `wordXor` | `word × word -> word` | 256-bit exclusive disjunction |
| `wordShl` | `word × word -> word` | logical left shift |
| `wordShr` | `word × word -> word` | logical right shift |

For both shifts, the left operand is the value and the right operand is the
shift amount. A shift amount greater than or equal to 256 returns zero. This
Core order is deliberately different from the EVM/Yul helper order
`(shift, value)`. A future elaborator must preserve source argument evaluation
with explicit bindings before reordering an EVM-shaped helper call.

`wordNe`, `wordLt`, `wordLe`, and `wordGe` are derived rather than primitive
Core tags:

```text
wordNe(x, y) = boolNot(wordEq(x, y))
wordLt(x, y) = wordGt(y, x)
wordLe(x, y) = boolNot(wordGt(x, y))
wordGe(x, y) = boolNot(wordGt(y, x))
```

These are value-level equations. The executable `wordLt` and `wordGe`
expression combinators bind `x` and then `y` exactly once before applying the
swapped `wordGt`; they weaken free de Bruijn indices in `y` when introducing
the first binding. They must not be implemented by syntactically swapping
arbitrary operand expressions, because that would reverse observable fault
order in the unchecked machine and would be unsafe for future elaboration.

Every unary operand is evaluated exactly once. Every binary left operand is
evaluated exactly once before the right operand, which is then evaluated exactly
once. Primitive application itself is total for operands having the declared
types. The unchecked CEK machine retains a structured fault for invalid operand
values, and the safety theorem makes that fault unreachable for well-typed
states.

Word input remains range-checked. Modulo reduction applies to operation results;
it does not make an out-of-range wire literal valid.

### Deferred boolean and conversion operations

`boolAnd` and `boolOr` are not eager primitives. A later source elaborator must
give them selected-branch-only behavior:

```text
x && y = if x then y else false
x || y = if x then true else y
```

`frombool`, `tobool`, signed operations, exponentiation, ternary modular
operations, byte selection, arithmetic shift, and count-leading-zero remain
outside M1c.

## Consequences

- Semantic differential fuzzing can compare operation edge cases against a
  proof-connected executable reference rather than an optimizer-specific path.
- Compiler-specific builtin typing, partial-folding coverage, host integer
  conversion, and eager boolean defects are not reproduced.
- Core traces fix operand evaluation order independently of later lowering.

## Conformance requirements

- Prove executable type inference sound and complete for unary and binary forms.
- Prove primitive application total and result-type preserving for declared
  operand types.
- Extend big-step/CEK correspondence, determinism, progress, preservation,
  sufficient-fuel completeness, and fault unreachability.
- Test addition, subtraction, and multiplication wraparound.
- Test unsigned division and modulo, including zero divisors.
- Test equality and unsigned greater-than at word boundaries.
- Test all 256-bit bitwise operations.
- Test left and right shifts at 0, 255, 256, and the maximum word shift amount.
- Test left-to-right operand evaluation and structured operand type errors.
- Keep the semantic kernel free of `sorry`, `admit`, `partial`, `unsafe`, and
  undeclared axioms.
