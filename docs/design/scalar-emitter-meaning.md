# Scalar source emitter meaning preservation

Updated: 2026-10-26. This records priority 5 of the
[next implementation roadmap](next-implementation-roadmap.md): a minimal
meaning-preservation theorem for what the Rust-dialect emitter actually prints.

## Result

The theorems are kernel-checked, contain no `sorry` and use only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The proofs live
in [ScalarMeaning](../../Solcore/Synthesis/Source/ScalarMeaning), which the
semantic-kernel policy check now covers.

| Theorem | Statement |
| --- | --- |
| `emit_source_meaning` | If `emit program = .ok emitted`, then for some Word `w`, `sourceCall emitted.source "run" [] = some w.val` and `CoreReturns program.program.toCore w`. |
| `Input.emit_source_meaning` | If `Input.emit function = .ok emitted`, then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturns (function.instantiate x).toCore w`. |
| `Function.emit_source_meaning` | If `Function.emit graph = .ok emitted` (profile `runtime-functions`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturns (graph.instantiate x).toCore w`. |
| `emit_preserves_meaning`, `Input.emit_preserves_meaning`, `Function.emit_preserves_meaning` | The same results, also exposing the source file `file` with `emitted.source = file.print` and `parseSource emitted.source = some file`. |
| `render_spec` | The induction over the actual `ScalarRenderer.renderWithFunctions`, with or without earlier helpers, described below. |
| `parseSource_print` | The printed text of any file whose names are lexically valid and not reserved parses back to that file. |

`sourceCall` lexes the emitted `String`, parses it and calls the method under
the source semantics below. `CoreReturns core w` states that Core's
`runStateful` returns `.done (.word w) []` for all sufficiently large fuel, and
that every completed run returns exactly that Word and store. This is the Core
machine used as the differential-testing oracle; for the runtime-input and
named-helper profiles it runs the original lambda or binding chain applied to
the input. Unsupported operations remain explicit emitter errors; the theorems
say nothing about failed emissions.

## Independent source meaning

The source side ([Syntax](../../Solcore/Synthesis/Source/ScalarMeaning/Syntax.lean),
[Semantics](../../Solcore/Synthesis/Source/ScalarMeaning/Semantics.lean),
[Print](../../Solcore/Synthesis/Source/ScalarMeaning/Print.lean),
[Lex](../../Solcore/Synthesis/Source/ScalarMeaning/Lex.lean),
[Parse](../../Solcore/Synthesis/Source/ScalarMeaning/Parse.lean) and
[Text](../../Solcore/Synthesis/Source/ScalarMeaning/Text.lean)) does not
import or mention Core.

Syntax. Names, decimal literals, `true` and `false`; parenthesized `!` and `~`
applications; parenthesized infix `+`, `-`, `*`, `&`, `|`, `^`, `==` and `>`;
`Typedef.rep(e)`, `uint256(e)` and calls `f(a)`, `f(a, b)` and `f(a, b, c)`.
Statements are `let x: T = e;` with `T` one of `word` or `bool`, `x = e;`, and
`if (e) { ... } else { ... }`. A file imports `std` and `std.dispatch`,
optionally imports `opcode as alias` pairs from `std.opcodes`, declares free
functions `function f(p: T, ...) returns (T) { ...; return e; }`, and declares
one contract with one public method whose parameters and declared result have
type `uint256`, ending in `return e;`.

Tokens. Spaces and newlines only separate tokens. Identifiers are ASCII
letters, digits and `_`, not starting with a digit; numbers are unsigned
decimal; `==` is one token. Every operator application must be parenthesized,
so the grammar has no precedence rules; a name followed by `(` is a call. Seventeen words are reserved, including
`let`, `if`, `return`, `true`, `false`, `Typedef`, `rep` and `uint256`.

Values. A word is a natural number below `2^256`; there are also Booleans and
`uint256` values wrapping one word. A literal of `2^256` or more has no meaning.

Operators follow the pinned standard library (`std/std.sol` and
`std/opcodes.sol` at solcore-rs `2a745e12974c373c3799fec81b48a53c7dce2ab4`).
The Rust frontend desugars `+` to `Add.add`, `==` to `Eq.eq`, `>` to `Ord.gt`,
`~` to `BitNot.bnot` and `!` to the function `not`.

| Source | `word` instance chain | Meaning |
| --- | --- | --- |
| `a + b` | `Add.add` → `addWord` → `add` (assembly `add`) | `(a + b) mod 2^256` |
| `a - b` | `Sub.sub` → `subWord` → `sub` | `(a + 2^256 - b) mod 2^256` |
| `a * b` | `Mul.mul` → `mulWord` → `mul` | `(a * b) mod 2^256` |
| `a & b`, `a \| b`, `a ^ b` | `band`/`bor`/`bxor` → `bandWord`/`borWord`/`bxorWord` → `and`/`or`/`xor` | bitwise operation |
| `~a` | `BitNot.bnot` → `bnotWord` → `not` | `2^256 - 1 - a` |
| `a == b` | `Eq.eq` → `eqWord` → `tobool(eq(a, b))` | `a = b` |
| `a > b` | `Ord.gt` → `gtWord` → `tobool(gt(a, b))` | `a > b`, unsigned |
| `!c` | `not` | Boolean negation |

Locals live in a stack of lexical scopes. `let` declares in the innermost
scope and its value must have the annotated type; assignment updates the nearest
binding and must keep its type; an `if` condition must be Boolean, and each
branch runs in a fresh scope that is discarded afterwards. A method binds its
`uint256` parameters (each below `2^256`) in a parameter scope, runs its body in
a block scope inside it, and returns the word of a `uint256` result. A failed
lookup, type mismatch or non-Boolean condition has no meaning (`none`).

Calls evaluate their arguments left to right. A callee resolves to a free
function declared earlier in the file, then to an imported `std.opcodes`
alias, then to `std.tobool`. A free function runs like a method on its typed
parameters and must return a value of its declared type. Each free function
sees only the functions declared before it; a call to a later or recursive
function has no meaning in this fragment. The emitted helpers call only
earlier helpers, matching the Core binding chain. The `std.opcodes` wrappers
pass their arguments in order to the EVM instruction of the same name; their
meanings (division, signed operations, shifts, byte selection, sign
extension, exponentiation, leading-zero count and modular arithmetic) are
defined from the EVM specification, but no proved emitter uses them yet.

## Connection to the actual emitter

[RendererEquations](../../Solcore/Synthesis/Source/ScalarMeaning/RendererEquations.lean)
unfolds the real `ScalarRenderer.render`, including its private helpers, by
definitional equality. It states each rendered case with the source syntax and
printer; no second renderer is defined.

`render_spec`, in [RendererPreservation](../../Solcore/Synthesis/Source/ScalarMeaning/RendererPreservation.lean),
covers every Core expression admitted by `acceptsAt` that the renderer accepts:
literals, locals, `let`, `if`, `!`, `~` and the eight binary operators. For
temporaries numbered from `first`, the rendered lines are the printing of
source statements. Executing them from frames that agree with a Core
environment evaluates the expression by Core's big-step `Evaluates` relation.
The result is bound to the rendered value name. Only temporaries in
`[first, nextId)` are declared or changed, and enclosing scopes keep their
declared names. The Core environment holds the Word locals followed by the
helper closures; `FunctionsAgree` states that each rendered helper name
denotes, in the source call context, the Word function of the corresponding
closure. A rendered call `sc_fn<k>(x)` then evaluates as Core applies that
closure. Each `if` result is declared with zero or `false` and assigned
at the end of both branch blocks. Freshness rests on the injectivity of
`sc_v<n>` names, derived from Lean's `Nat.toDigits`. Core Word operations are
related to the EVM formulas above.

[Emitter](../../Solcore/Synthesis/Source/ScalarMeaning/Emitter.lean) connects
the wrappers. `emit` prints `run()` returning `uint256(value)`. `Input.emit`
prints `run(input: uint256)` and first binds `sc_input` to
`Typedef.rep(input)`, matching Core's application of the lambda to the input.
[FunctionEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/FunctionEmitter.lean)
restates the emitter's helper loop by structural recursion, proves it equal to
the actual `for` loop, and shows by induction that each printed
`sc_fn<k>(sc_arg: word)` agrees with the closure Core builds for helper `k`.
Core machine results follow from `runStateful_evaluation_sound`,
`evaluation_runStateful_complete_with_sufficient_fuel` and determinism of
`Evaluates`.

[Text](../../Solcore/Synthesis/Source/ScalarMeaning/Text.lean) proves that the
printed text lexes to exactly the file's tokens and that `parseFile` inverts
them (`parseSource_print`). The meaning is therefore a function of the emitted
`String`, not of an internal printer argument.

## Assumptions outside the theorem

The theorem relates emitted text to Core. The following steps of the actual
Rust pipeline are assumed, and are exercised only by the existing tests:

1. Parsing. The pinned Rust parser reads the emitted text as the same
   structure as this grammar, including identifier, numeral and `==`
   tokenization and the parenthesized operator forms.
2. Name resolution and typing. The imports bring `word`, `bool`, `uint256` and
   `Typedef` into scope; the operators resolve to the cited `word` instances
   and `!` to `std.not`; decimal literals elaborate at `word`; the frontend
   accepts every emitted program. Rust acceptance is not proved.
3. Standard library meaning. The instance chains and opcode wrappers behave as
   transcribed in the table. The transcription is manual and cites the pinned
   files; it is not derived from the Rust frontend.
4. Compilation and execution. Specialization, lowering, Sonatina or Yul code
   generation, optimization, EVM execution and `std.dispatch` are assumed.
   This includes selector dispatch, `uint256` ABI decoding and 32-byte result
   encoding. Gas and EVM resource limits are not modeled; the source meaning
   has no fuel.

Differential agreement remains evidence for these steps, not a proof. Agreement
in a corpus also does not replace this theorem for the printer.

## Scope

The theorems cover `ScalarRenderer.renderWithFunctions` and three actual
emitters: closed G0 (`closed-g0`), runtime input (`runtime-word`) and named
helpers (`runtime-functions`). They do not yet cover raw primitive aliases
(`PrimitiveRenderer`, `runtime-primitives`), call graphs (`CallGraphRenderer`),
aggregates, mutation, loops, storage, contract calls, closures, generic,
comptime or module emitters. The planned order is primitive aliases, then call
graphs, then mutation, aggregates and loops.

## Executable checks

[SourceScalarMeaning](../../Solcore/Test/SourceScalarMeaning.lean) is registered
in the test driver. It runs actual emitter output through `sourceCall` and
compares the result with Core's `runStateful`. It covers all fifteen closed
fixtures, also against hand-known Words, twelve runtime-input fixtures and the
four named-helper graphs (single, chain, diamond and branch locals) at eight
boundary inputs. Twenty programs from the first 96 G0 generator seeds
with a 40-node budget are emitted; the others are generator or emitter
exclusions. Each accepted text must reparse and print back to itself. Extra or
missing arguments, an undeclared method, `= =` in place of `==`, an
unparenthesized operator, an undeclared local, a mistyped declaration, a call
to an undeclared helper and a literal of `2^256` are all rejected rather than
given a value.
