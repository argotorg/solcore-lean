# Source emitter meaning preservation

Updated: 2026-10-27. This records priority 5 of the
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
| `Primitive.emit_source_meaning` | If `Primitive.emit function = .ok emitted` (profile `runtime-primitives`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturns (function.instantiate x).toCore w`. |
| `CallGraph.emit_source_meaning` | If `CallGraph.emit graph = .ok emitted` (profile `runtime-call-graphs`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturns (graph.instantiate x).toCore w`. |
| `Mutation.emit_source_meaning` | If `Mutation.emit graph = .ok emitted` (profile `runtime-mutation`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturnsWithStore (graph.instantiate x).toCore w`. |
| `Aggregate.emit_source_meaning` | If `Aggregate.emit graph = .ok emitted` (profile `runtime-aggregates`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturnsWithStore (graph.instantiate x).toCore w`. |
| `AggregateCallGraph.emit_source_meaning` | If `AggregateCallGraph.emit graph = .ok emitted` (profile `runtime-aggregate-call-graphs`), then for every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturnsWithStore (graph.instantiate x).toCore w`. |
| `CallGraphLoop.emit_source_meaning` | If `CallGraphLoop.emit plan = .ok emitted` (profile `runtime-call-graph-loops`), then for every Word input `x` there is `w` with `loopSourceCall fuel emitted.source "run" [x.val] = some w.val` for every `fuel > plan.mask`, and `CoreReturnsWithStore (plan.instantiate x).toCore w`. |
| `Loop.emit_source_meaning` | If `Loop.emit plan = .ok emitted` (profile `runtime-loops`), then for every Word input `x` there is `w` with `loopSourceCall fuel emitted.source "run" [x.val] = some w.val` for every `fuel > plan.mask`, and `CoreReturnsWithStore (plan.instantiate x).toCore w`. |
| `emit_preserves_meaning`, `Input.emit_preserves_meaning`, `Function.emit_preserves_meaning`, `Primitive.emit_preserves_meaning`, `CallGraph.emit_preserves_meaning`, `Mutation.emit_preserves_meaning`, `Aggregate.emit_preserves_meaning`, `AggregateCallGraph.emit_preserves_meaning` | The same results, also exposing the source file `file` with `emitted.source = file.print` and `parseSource emitted.source = some file`. |
| `CallGraphLoop.emit_preserves_meaning`, `Loop.emit_preserves_meaning` | The same results, exposing the loop file `file` with `emitted.source = file.print`, `parseLoopSource emitted.source = some file` and `file.call fuel "run" [x.val] = some w.val` for every `fuel > plan.mask`. |
| `render_spec`, `primitive_render_spec`, `callGraph_render_spec`, `mutation_render_spec`, `aggregate_render_spec`, `aggregateCallGraph_render_spec` | The inductions over the actual `ScalarRenderer.renderWithFunctions` (with or without earlier helpers), `PrimitiveRenderer.render`, `CallGraphRenderer.renderWithFunctions`, `MutationRenderer.render`, `AggregateRenderer.render` and `AggregateCallGraphRenderer.render`, described below. |
| `parseSource_print` | The printed text of any file whose names are lexically valid and not reserved parses back to that file. |
| `parseLoopSource_print` | The same for loop files under the loop grammar. |
| `loopSourceCall_of_parseSource` | On every text that `parseSource` accepts, `loopSourceCall fuel` is `sourceCall`, for every fuel. |
| `loopSourceCall_mono`, `loopSourceCall_unique` | More fuel keeps the result of a completed loop call, so all completed calls of a text return the same word. |

`sourceCall` lexes the emitted `String`, parses it and calls the method under
the source semantics below. `CoreReturns core w` states that Core's
`runStateful` returns `.done (.word w) []` for all sufficiently large fuel, and
that every completed run returns exactly that Word and store. This is the Core
machine used as the differential-testing oracle; for the runtime-input,
named-helper, raw-primitive, call-graph, private-mutation, aggregate and
aggregate call-graph profiles it runs the original lambda or binding chain
applied to the input. For the two loop profiles it runs the original
bounded-loop reference, applied to the input. A Core program with mutable
locals ends with its cells in the store, so `CoreReturnsWithStore` states the
same for some final store that every completed run reaches. The aggregate
call-graph renderer refuses cells, and the executable checks observe an empty
final store, but its theorem states only `CoreReturnsWithStore`: the proof
reuses the store-aware aggregate invariant, which does not track that no cell
is allocated. The bounded-loop reference keeps its accumulator in a cell, and
both loop theorems state `CoreReturnsWithStore`. The executable checks observe
that the final store starts with that cell, holding the result. For the
call-graph loop it is the only cell; for the aggregate loop the cells that the
step's calls allocated follow it.

`loopSourceCall fuel` reads a text with the loop grammar below and calls the
method under the loop meaning, in which each `while` loop may evaluate its
condition at most `fuel` times. A loop that runs out of fuel has no meaning, so
`CallGraphLoop.emit_source_meaning` and `Loop.emit_source_meaning` state
termination: every fuel above the mask, which is at most seven, completes the
call.
Unsupported operations remain explicit emitter errors; the theorems say
nothing about failed emissions.

## Independent source meaning

The source side ([Syntax](../../Solcore/Synthesis/Source/ScalarMeaning/Syntax.lean),
[Semantics](../../Solcore/Synthesis/Source/ScalarMeaning/Semantics.lean),
[Print](../../Solcore/Synthesis/Source/ScalarMeaning/Print.lean),
[Lex](../../Solcore/Synthesis/Source/ScalarMeaning/Lex.lean),
[Parse](../../Solcore/Synthesis/Source/ScalarMeaning/Parse.lean),
[Text](../../Solcore/Synthesis/Source/ScalarMeaning/Text.lean) and, for loops,
[LoopSemantics](../../Solcore/Synthesis/Source/ScalarMeaning/LoopSemantics.lean)
and [LoopText](../../Solcore/Synthesis/Source/ScalarMeaning/LoopText.lean)) does
not import or mention Core.

Syntax. Names, decimal literals, `true` and `false`; parenthesized `!` and `~`
applications; parenthesized infix `+`, `-`, `*`, `&`, `|`, `^`, `==` and `>`;
`Typedef.rep(e)`, `uint256(e)`, calls `f(a)`, `f(a, b)` and `f(a, b, c)`, pairs
`(a, b)` and the sum constructors `inl(e)` and `inr(e)`. Statements are
`let x: T = e;` with `T` one of `word`, `bool`, `(word, word)` or
`sum<word, word>`, `x = e;`, `if (e) { ... } else { ... }`, the pair match
`match (e) { case (x, y) { ... } }` and the sum match
`match (e) { case inl(x) { ... } case inr(y) { ... } }`. A file imports `std`
and `std.dispatch`,
optionally imports `opcode as alias` pairs from `std.opcodes`, declares free
functions `function f(p: T, ...) returns (T) { ...; return e; }`, and declares
one contract with one public method whose parameters and declared result have
type `uint256`, ending in `return e;`.

Tokens. Spaces and newlines only separate tokens. Identifiers are ASCII
letters, digits and `_`, not starting with a digit; numbers are unsigned
decimal; `==` is one token. Every operator application must be parenthesized,
so the grammar has no precedence rules; a parenthesized pair has a comma where
an infix operator would be, and a name followed by `(` is a call. Twenty-one
words are reserved, including `let`, `if`, `return`, `true`, `false`,
`Typedef`, `rep`, `uint256`, `match`, `case`, `inl` and `inr`.

Values. A word is a natural number below `2^256`; there are also Booleans,
`uint256` values wrapping one word, pairs of two words, and the tags `inl` and
`inr` of `sum<word, word>`, each with one word payload. A literal of `2^256` or
more has no meaning.

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

Pairs, `sum`, `inl` and `inr` are builtins of the pinned frontend
(`crates/hir/src/nameres/builtins.rs` at the same revision), not
standard-library definitions. A pair evaluates its components left to right
and must hold two words; `inl(e)` and `inr(e)` tag a word. Both tags have type
`sum<word, word>`, so an assignment may replace one tag by the other. A `match`
evaluates its scrutinee once. The pair case runs its body in a fresh scope that
binds its two pattern variables to the components; the sum match runs the
`inl` or `inr` case, by the scrutinee's tag, in a fresh scope that binds its
pattern variable to the payload. The case scope is discarded afterwards, so a
case body changes enclosing locals only by assignment. A scrutinee of another
shape has no meaning.

Calls evaluate their arguments left to right. A callee resolves to a free
function declared earlier in the file, then to an imported `std.opcodes`
alias, then to `std.tobool`. A free function runs like a method on its typed
parameters and must return a value of its declared type. Each free function
sees only the functions declared before it; a call to a later or recursive
function has no meaning in this fragment. The emitted helpers call only
earlier helpers, matching the Core binding chain. An alias means only the
opcode its import names, and a call to a name that is neither declared nor
imported has no meaning. The `std.opcodes` wrappers pass their `word`
arguments, in order, to the EVM instruction of the same name; the source
semantics defines these instructions from the EVM specification. Signed
operands are read in two's complement.

| Opcode | Meaning |
| --- | --- |
| `div(a, b)`, `mod(a, b)` | unsigned quotient or remainder; zero for `b = 0` |
| `sdiv(a, b)`, `smod(a, b)` | quotient truncated toward zero, or remainder with the sign of `a`; zero for `b = 0` |
| `sgt(a, b)` | one if `a > b` as signed words, else zero |
| `shl(s, v)`, `shr(s, v)` | `v * 2^s mod 2^256` or `v / 2^s`; zero for `s ≥ 256` |
| `sar(s, v)` | floor of the signed `v / 2^s`; for `s ≥ 256`, all ones if `v` is negative, else zero |
| `addmod(a, b, m)`, `mulmod(a, b, m)` | `(a + b) mod m` or `(a * b) mod m` without truncation; zero for `m = 0` |
| `clz(v)` | leading zero bits; `256` for zero |
| `byte(i, v)` | byte `i` from the most significant end; zero for `i ≥ 32` |
| `signextend(i, v)` | sign-extends the low `i + 1` bytes; `v` for `i ≥ 31` |
| `exp(a, b)` | `a^b mod 2^256` |

Loops. [LoopSemantics](../../Solcore/Synthesis/Source/ScalarMeaning/LoopSemantics.lean)
and [LoopText](../../Solcore/Synthesis/Source/ScalarMeaning/LoopText.lean)
extend the fragment for the bounded-loop wrappers as a separate grammar and
meaning, so `parseSource`, `sourceCall` and every result above are unchanged. A
method body may also contain `while (a op b) { ... }` at its top level, where
`a op b` is one infix operation and the body is a block of loop-free
statements. As in the pinned frontend (`crates/parser/src/parse/stmt.rs`), the
parentheses belong to the loop; the printer reuses those of the infix
operation, so the header reads `while (sc_limit > sc_counter) {`.
`parseLoopSource` lexes as `parseSource` does and parses the same grammar,
reading a statement that starts with `while (` as a loop. No loop-free
statement starts that way, since an assignment to a name `while` continues
with `=`. Every evaluation of the condition must give a Boolean. While it is
`true`, the body runs in a fresh scope that is discarded afterwards, so a `let`
in the body ends with its iteration and only assignments change enclosing
locals. A loop need not terminate, so `LoopFile.call fuel` lets each loop
evaluate its condition at most `fuel` times and has no meaning when a loop runs
out. More fuel never changes a result, so all completed calls agree. A text
that `parseSource` accepts parses under the loop grammar to the same file, and
its loop meaning is its `sourceCall` meaning for every fuel.

## Connection to the actual emitter

[RendererEquations](../../Solcore/Synthesis/Source/ScalarMeaning/RendererEquations.lean)
unfolds the real `ScalarRenderer.render`, including its private helpers, by
definitional equality. It states each rendered case with the source syntax and
printer; no second renderer is defined.

`render_spec`, in [RendererPreservation](../../Solcore/Synthesis/Source/ScalarMeaning/RendererPreservation.lean),
covers every Core expression admitted by `functionAcceptsAt` that the renderer accepts:
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

The per-constructor lemmas are generic. Each assumes only how a renderer
prints its constructor (an inversion property), a predicate on the call
context, and the fixed callee names the renderer may print. The scalar
renderer instantiates them with every context and no fixed callees.
[PrimitiveEquations](../../Solcore/Synthesis/Source/ScalarMeaning/PrimitiveEquations.lean)
unfolds the actual `PrimitiveRenderer.render` in the same way, and
[PrimitivePreservation](../../Solcore/Synthesis/Source/ScalarMeaning/PrimitivePreservation.lean)
proves `primitive_render_spec`. The primitive renderer copies each raw opcode
operand into a fresh `word` temporary, left to right, before the call. A copy
is another rendering of the same operand, so the operand cases are reused.
Shifts pass the shift amount first, as `sar(shift, value)` expects, and the
signed comparison is printed as `tobool(sc_sgt(a, b))`. The call context must
satisfy `PrimitiveContext`: each of the fourteen aliases reaches its opcode and
`tobool` reaches the standard library function.
[PrimitiveAgreement](../../Solcore/Synthesis/Source/ScalarMeaning/PrimitiveAgreement.lean)
proves that each Core Word operation (`udiv`, `sdiv`, `shiftArithmeticRight`,
`signExtend`, `pow`, `addMod` and the others) agrees with its formula in the
table above.

[Emitter](../../Solcore/Synthesis/Source/ScalarMeaning/Emitter.lean) connects
the wrappers. `emit` prints `run()` returning `uint256(value)`. `Input.emit`
prints `run(input: uint256)` and first binds `sc_input` to
`Typedef.rep(input)`, matching Core's application of the lambda to the input.
[FunctionEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/FunctionEmitter.lean)
restates the emitter's helper loop by structural recursion, proves it equal to
the actual `for` loop, and shows by induction that each printed
`sc_fn<k>(sc_arg: word)` agrees with the closure Core builds for helper `k`.
[PrimitiveEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/PrimitiveEmitter.lean)
proves that the actual import line of `Primitive.emit` is the printing of the
fourteen `opcode as alias` pairs, so the file's call context satisfies
`PrimitiveContext`. The helper loop proof is generic over the renderer and the
call context. [CallGraphEquations](../../Solcore/Synthesis/Source/ScalarMeaning/CallGraphEquations.lean)
and [CallGraphPreservation](../../Solcore/Synthesis/Source/ScalarMeaning/CallGraphPreservation.lean)
prove `callGraph_render_spec` for `CallGraphRenderer.renderWithFunctions`. It
prints raw opcodes as the primitive renderer does, and copies a helper call's
argument into a fresh temporary before the call.
[CallGraphEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/CallGraphEmitter.lean)
shows that the helper names `sc_fn<k>` never shadow an opcode alias or
`tobool`, so every helper body runs in a primitive call context.

[MutationSpec](../../Solcore/Synthesis/Source/ScalarMeaning/MutationSpec.lean),
[MutationEquations](../../Solcore/Synthesis/Source/ScalarMeaning/MutationEquations.lean)
and [MutationPreservation](../../Solcore/Synthesis/Source/ScalarMeaning/MutationPreservation.lean)
prove `mutation_render_spec` for `MutationRenderer.render`. Core keeps each
mutable Word local in its store and binds a cell reference; the source keeps it
in an ordinary local `sc_c<n>` that `x = e;` assigns. The invariant relates
every binding, a Word, a Boolean, a Unit value without a source name, or a
cell, to the Core environment, the Core store and the source frames. Distinct
cells hold distinct locations and distinct bindings have distinct names, so
writing one cell changes no other binding. Evaluation may append cells and
write the cells of the bindings; every other existing location is unchanged.
Every read of a cell is copied to a fresh immutable temporary, so a later
operand that writes the cell cannot change an earlier value. A helper cannot
reach its caller's cells, and the proof shows that its evaluation keeps every
existing location. The proofs inspect the profile's acceptance check through
its public `initializerKind?`, without naming its private helpers.
[MutationEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/MutationEmitter.lean)
connects the actual helper loop and wrapper. Core machine results follow from
`runStateful_evaluation_sound`,
`evaluation_runStateful_complete_with_sufficient_fuel` and determinism of
`Evaluates`.

[AggregateSpec](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateSpec.lean),
[AggregateEquations](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateEquations.lean),
[AggregatePreservation](../../Solcore/Synthesis/Source/ScalarMeaning/AggregatePreservation.lean)
and [AggregateControl](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateControl.lean)
prove `aggregate_render_spec` for `AggregateRenderer.render`. The invariant is
the mutation invariant with two more kinds of binding. A pair binding holds the
source pair of its two Core Words. A sum binding holds `inl` or `inr` of the
Core payload; Core also tags a sum with the type of its other side, which the
source sum does not carry. A pair or sum binding is never a cell, so a later
cell write cannot change it. A projection is printed as a zero `word` result
followed by a pair match whose single case assigns the picked component; the
match evaluates the operand's value name once, as Core evaluates `first` or
`second` once. A Core `case` binds its payload before every existing local.
The source binds it, under a fresh `sc_p<n>` name, in the scope of the
selected case, which is discarded afterwards. The same two lemmas, for Unit
and for value results, cover `if` branches and `case` bodies: the body runs in
a block scope that may start with a pattern binding, and a value body ends by
assigning the result declared before the `if` or `match`. That result starts
as `0`, `false`, `(0, 0)` or `inl(0)`. Raw operations use the call-graph
formatting: each raw opcode operand is copied first, and a copy is one more
rendering of the operand. The equations restate the renderer's private
helpers, such as its scalar-operand conversion, by definitional equality. The
alias call context is required only for an expression whose rendering prints
an alias (`usesOpcodeAliases`).
[AggregateEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateEmitter.lean)
connects the actual helper loop and wrapper. When some rendered body uses an
alias, the actual import line is the printing of the fourteen aliases and every
helper and the entry run in a primitive call context. Otherwise the file
imports no aliases, and no body needs the alias context.

[AggregateCallGraphEquations](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateCallGraphEquations.lean)
and [AggregateCallGraphPreservation](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateCallGraphPreservation.lean)
prove `aggregateCallGraph_render_spec` for `AggregateCallGraphRenderer.render`.
That renderer prints pairs, sums, projections and case payloads as the
aggregate renderer does, and scalar operations, raw opcodes and helper calls as
the call-graph renderer does. It refuses cells, Unit, integers, lambdas and
data constructors, so every accepted expression has a value. Its bindings are
Words, Booleans, pairs and sums; the proof maps each to the aggregate binding
of the same kind, so the aggregate invariant and its lemmas apply unchanged.
The value cases of `let`, `if` and `case` are separate lemmas of
[AggregateControl](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateControl.lean)
that both renderers use. Every body runs in a primitive call context.
[AggregateCallGraphEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/AggregateCallGraphEmitter.lean)
connects the actual helper loop and wrapper. As in the call-graph emitter, the
file always imports the fourteen aliases, and its import line is their
printing.

[CallGraphLoopEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/CallGraphLoopEmitter.lean)
connects the actual `CallGraphLoop.emit`. Its helpers come from the call-graph
emitter's helper loop. Its entry is printed by the same renderer as one more
free function, `sc_step(sc_arg: word)`, and `callGraph_render_spec` applies to
it as to a helper. The method declares `sc_input`, `sc_limit` as
`(sc_input & mask)`, `sc_acc` and `sc_counter = 0`. While
`sc_limit > sc_counter`, it assigns `sc_step(sc_acc)` to the accumulator and
increments the counter. The Core reference (`BoundedLoop.canonicalProgram`)
has no counter. It allocates the accumulator in a cell and, for each literal
ordinal `i` below the mask, applies the entry closure to the cell when the
bound exceeds `i`. These guards are private to their module, so the proof
restates them (`loopGuards`) and shows that the applied program reduces to the
restatement for each of the four admitted masks. An induction on the steps
left before the bound (`boundedLoop_agrees`) shows that the guards and the
source loop apply the step equally often. While the bound exceeds the ordinal,
both apply the step: Core's application leaves the store unchanged, and
`sc_step` returns the same Word. From the bound on, the guards skip and the
loop exits. The bound `input & mask` is at most the mask, so every fuel above
the mask suffices.

[LoopEmitter](../../Solcore/Synthesis/Source/ScalarMeaning/LoopEmitter.lean)
connects the actual `Loop.emit` (profile `runtime-loops`). Its helpers come
from the aggregate emitter's helper loop. Its entry is printed by
`AggregateRenderer.render` as `sc_step`, and `aggregate_render_spec` applies to
it as to a helper. The wrapper, the loop grammar and the source half of the
proof are those of the call-graph loop. As for the aggregate emitter, the file
imports the fourteen aliases exactly when a helper or the entry uses one. An
aggregate step may allocate private cells. The source keeps them in `sc_c<n>`
locals of `sc_step`, which end with the call, while Core appends them to its
store, so the store grows from one iteration to the next. The store-aware
helper relation states that each call keeps every existing location, so the
accumulator stays in the first location. `storeLoop_agrees` repeats the
induction of `boundedLoop_agrees` over such stores: an applied step writes its
result to the accumulator cell after appending its own cells, and a skipped
guard keeps the store.

[Text](../../Solcore/Synthesis/Source/ScalarMeaning/Text.lean) proves that the
printed text lexes to exactly the file's tokens and that `parseFile` inverts
them (`parseSource_print`);
[LoopText](../../Solcore/Synthesis/Source/ScalarMeaning/LoopText.lean) proves
the same for loop files (`parseLoopSource_print`). The meaning is therefore a
function of the emitted `String`, not of an internal printer argument.

## Assumptions outside the theorem

The theorem relates emitted text to Core. The following steps of the actual
Rust pipeline are assumed, and are exercised only by the existing tests:

1. Parsing. The pinned Rust parser reads the emitted text as the same
   structure as this grammar, including identifier, numeral and `==`
   tokenization, the parenthesized operator forms, pairs, the types
   `(word, word)` and `sum<word, word>`, and the two `match` forms with their
   case patterns.
2. Name resolution and typing. The imports bring `word`, `bool`, `uint256` and
   `Typedef` into scope; the operators resolve to the cited `word` instances
   and `!` to `std.not`; pairs, `sum`, `inl` and `inr` resolve to the frontend
   builtins; decimal literals elaborate at `word`, also inside pairs and in
   `inl(0)`; the frontend accepts every emitted program. Rust acceptance is not
   proved.
3. Standard library and builtin meaning. The instance chains and opcode
   wrappers behave as transcribed in the tables, and pairs, sums and `match`
   behave as described above. The transcription is manual and cites the
   pinned files; it is not derived from the Rust frontend. In particular, the
   raw `std.opcodes` wrappers do not revert for a zero modulus, unlike the
   public `std.addmod` and `std.mulmod`, and the target EVM provides `CLZ`.
4. Compilation and execution. Specialization, lowering (including the lowering
   of pairs, sums and matches), Sonatina or Yul code generation, optimization,
   EVM execution and `std.dispatch` are assumed. This includes selector
   dispatch, `uint256` ABI decoding and 32-byte result encoding. Gas and EVM
   resource limits are not modeled; the fuel of the loop meaning bounds loop
   iterations, not gas.

The aggregate call-graph emitter adds no assumption to these four. Its text
uses only the forms above. That the frontend accepts helper calls inside `if`
branches and `match` cases is part of assumption 2, and their lowering is part
of assumption 4.

The call-graph loop emitter adds its `while` loop to these assumptions. Under
assumption 1, the pinned parser reads `while (sc_limit > sc_counter) { ... }`
as a loop whose condition is the expression inside the parentheses and whose
body is the braced block; `while` is a contextual keyword there. The frontend
then lowers the loop to a `For` statement without initializer or post
statements; both steps are in `crates/parser/src/parse/stmt.rs`. Under
assumption 3, that statement evaluates its Boolean condition before every
iteration, runs the body as a block scope and stops when the condition is
false. That the frontend accepts the loop and its `word` counter is part of
assumption 2, and its lowering and execution are part of assumption 4.

The aggregate loop emitter adds no further assumption. Its step uses only the
forms above, and its wrapper is the same `while` loop.

Differential agreement remains evidence for these steps, not a proof. Agreement
in a corpus also does not replace this theorem for the printer.

## Scope

The theorems cover `ScalarRenderer.renderWithFunctions`, `PrimitiveRenderer.render`,
`CallGraphRenderer.renderWithFunctions`, `MutationRenderer.render`,
`AggregateRenderer.render`, `AggregateCallGraphRenderer.render` and ten
actual emitters: closed G0 (`closed-g0`), runtime input (`runtime-word`),
named helpers (`runtime-functions`), raw primitive aliases
(`runtime-primitives`), call graphs (`runtime-call-graphs`), private mutable
locals (`runtime-mutation`), Word aggregates (`runtime-aggregates`), aggregate
call graphs (`runtime-aggregate-call-graphs`), call-graph loops
(`runtime-call-graph-loops`) and aggregate loops (`runtime-loops`). They do not
yet cover the other emitters that render with `AggregateRenderer` (generic,
closures, comptime, modules, storage, storage rollback, keyed storage, dynamic
arrays, dynamic bytes, event logs, call value and contract calls). Their texts
use forms outside these fragments, such as storage access, external calls,
lambdas, generic functions and multi-file module bundles. The loop grammar
admits loops only at the top level of a method body, with a loop-free body and
an infix condition.

## Executable checks

[SourceScalarMeaning](../../Solcore/Test/SourceScalarMeaning.lean) is registered
in the test driver. It runs actual emitter output through `sourceCall` and
compares the result with Core's `runStateful`. It covers all fifteen closed
fixtures, also against hand-known Words, twelve runtime-input fixtures and the
four named-helper graphs (single, chain, diamond and branch locals) at eight
boundary inputs. The fourteen raw primitive fixtures and 25 boundary bodies
use the same eight inputs and their own boundary values. They cover zero
divisors and moduli, shifts of 256 or more, negative signed operands, byte and
sign positions and large exponents. Thirty-three primitive results are also
checked against hand-known Words. A call to an alias that is not imported is
rejected; swapping two aliases in the import line swaps their meanings. The
call-graph emitter runs on twenty graphs at the same inputs. These are the
mixed and branch-call graphs of its regression, fourteen opcodes applied to
helper results, and the four named-helper graphs. Twenty-one of their results
also match hand-known Words. The six mutation graphs of the mutation emitter's
regression run at the same inputs. Their Core results also match the
regression's hand-known formulas, and a write to an undeclared cell is
rejected.
Twenty programs from the first 96 G0 generator seeds
with a 40-node budget are emitted; the others are generator or emitter
exclusions. Each accepted text must reparse and print back to itself. Extra or
missing arguments, an undeclared method, `= =` in place of `==`, an
unparenthesized operator, an undeclared local, a mistyped declaration, a call
to an undeclared helper and a literal of `2^256` are all rejected rather than
given a value.

[SourceAggregateMeaning](../../Solcore/Test/SourceAggregateMeaning.lean) is
registered as well. It runs actual `Aggregate.emit` output through `sourceCall`
at the same eight boundary inputs and compares it with Core. It covers the six
graphs of the aggregate emitter's regression, the ten `if` and `case` joins at
Word, Boolean, Unit, pair and sum targets, the four aggregate case templates,
eighteen raw primitive bodies inside and around pairs, sums and cells, and the
first 24 generated aggregate graphs with a 256-node budget. The regression
graphs, joins and templates also match hand-known formulas. Each text must
reparse, print back to itself and import the aliases exactly when a body uses
one. A sum match with two `inr` cases, a payload used after its case, a sum
match on a word, a pair with a Boolean component, a pair assigned to a word, a
call to an alias that is not imported, and a primitive text without its import
line are all rejected.

[SourceAggregateCallGraphMeaning](../../Solcore/Test/SourceAggregateCallGraphMeaning.lean)
is registered as well. It runs actual `AggregateCallGraph.emit` output through
`sourceCall` at the same eight boundary inputs and compares it with Core. It
covers the regression graph that composes all nine composition shapes, which
must also give `(8x + 4) mod 2^256` above five and `4x + 1` otherwise. It
covers the regression's nine minimal shape graphs and its scalar, adjacent and
outer-local graphs, with hand-known formulas, and three helper-call graphs:
the projected call pair, the payload helper call and the call-graph emitter's
mixed graph, with hand-known Words. The fourteen opcodes applied to helper
results run inside a projected pair and as a sum payload, each with a
hand-known Word. Twenty-four generated graphs, eight seeds at each of the 96,
192 and 256-node budgets, together cover every composition shape. Every Core
run must end with an empty store. Each text must reparse, print back to
itself, import the fourteen aliases and declare one function per helper. A sum
match with two `inr` cases, a payload used after its case, a helper applied to
a pair, a helper that returns a pair for a `word`, a helper that calls a later
helper and a primitive text without its import line are all rejected.

[SourceCallGraphLoopMeaning](../../Solcore/Test/SourceCallGraphLoopMeaning.lean)
is registered as well. It runs actual `CallGraphLoop.emit` output through
`loopSourceCall` at the eight boundary inputs and the inputs three, six and
seven, and compares it with Core. Each call must agree with Core at one more
unit of fuel than its iterations, at fuel above the mask and at fuel 64, and
must have no meaning at fuel equal to its iterations. It covers `2x + 1` under
mask seven and `(2x) >> 4` under mask three, with hand-known formulas and
Words, the identity step under each of the four admitted masks, and the
call-graph emitter's mixed graph under masks one and seven. It also covers the
fourteen opcodes applied to a helper result under mask one, with hand-known
Words, and 24 generated plans, eight seeds at each of the 128, 256 and
512-node budgets, which together use every generated mask. Every Core run must
end with one cell, which holds the result. Each text must reparse under the
loop grammar, print back to itself, import the fourteen aliases and declare
`sc_step` after one function per helper, and `parseSource` must reject it.
Two loop-free call-graph texts parse to the same file under the loop grammar
and keep their `sourceCall` meaning at fuel 0, 1 and 64. A loop condition in
two pairs of parentheses is rejected. A loop without its counter step has no
meaning once it iterates, a `let` in the body leaves the accumulator unchanged,
and a reversed condition never iterates. A `word` condition and an assignment
to an undeclared name have no meaning, and counting by two changes the result.

[SourceLoopMeaning](../../Solcore/Test/SourceLoopMeaning.lean) is registered as
well. It runs actual `Loop.emit` output through `loopSourceCall` in the same
way, with the same fuel checks at the same inputs. It covers the six
regression steps of the loop emitter's test (increment, an arbitrary entry, a
step that allocates one private cell per call, a mixed step, and identity and
constant entries) and two steps through a projected pair and a sum payload,
each under the four admitted masks with hand-known formulas. It also covers the
private-cell step seven times over with hand-known Words, the fourteen opcodes
applied to a
helper result under mask one, with hand-known Words, and 23 generated plans
from 24 seeds at the 256 and 512-node budgets, which together use every
generated mask. Every Core run must end with the accumulator cell, holding the
result, followed only by Word cells. For these fixed steps, the store must hold
the accumulator cell and one cell per call of the private-cell step. Each text
must reparse under
the loop grammar, print back to itself, import the aliases exactly when a step
body uses one and declare `sc_step` after one function per helper, and
`parseSource` must reject it. Two loop-free aggregate texts, with private
cells, a sum and its match, keep their `sourceCall` meaning at fuel 0, 1 and
64. A loop condition in two pairs of parentheses is rejected. A loop without
its counter step has no meaning once it iterates, a `let` in the body leaves
the accumulator unchanged, and a step that assigns a cell it never declared has
no meaning.
