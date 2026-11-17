# Source emitter meaning preservation

Updated: 2026-11-17. This records priority 5 of the
[next implementation roadmap](next-implementation-roadmap.md): a minimal meaning-preservation
theorem for what the Rust-dialect emitter actually prints, not for a substitute native Lean syntax.

The note gives the theorems, the independent source meaning they use, how the proofs reach the
actual emitters, the steps of the Rust pipeline that stay assumed, and the emitters still open.

## Result

The theorems are kernel-checked, contain no `sorry` and use only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The proofs live in
[ScalarMeaning](../../Solcore/Synthesis/Source/ScalarMeaning), which the semantic-kernel policy
check covers.

### Theorems

Each theorem assumes that emission succeeded, `E.emit p = .ok emitted`, and relates the emitted
text to the original Core reference. In the second and third rows `p` is the emitted function or
graph.

| Theorem | Profile | Conclusion |
| --- | --- | --- |
| `emit_source_meaning` | `closed-g0` | For some Word `w`, `sourceCall emitted.source "run" [] = some w.val` and `CoreReturns program.program.toCore w`. |
| `Input.emit_source_meaning`, `Function.emit_source_meaning`, `Primitive.emit_source_meaning`, `CallGraph.emit_source_meaning` | `runtime-word`, `runtime-functions`, `runtime-primitives`, `runtime-call-graphs` | For every Word input `x` there is `w` with `sourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturns (p.instantiate x).toCore w`. |
| `Mutation.emit_source_meaning`, `Aggregate.emit_source_meaning`, `AggregateCallGraph.emit_source_meaning` | `runtime-mutation`, `runtime-aggregates`, `runtime-aggregate-call-graphs` | The same with `CoreReturnsWithStore (p.instantiate x).toCore w`. |
| `CallGraphLoop.emit_source_meaning`, `Loop.emit_source_meaning` | `runtime-call-graph-loops`, `runtime-loops` | For every Word input `x` there is `w` with `loopSourceCall fuel emitted.source "run" [x.val] = some w.val` for every `fuel > plan.mask`, and `CoreReturnsWithStore (plan.instantiate x).toCore w`. |
| `Generic.emit_source_meaning` | `runtime-generics` | For every Word input `x` there is `w` with `genericSourceCall emitted.source "run" [x.val] = some w.val` and `CoreReturnsWithStore (plan.instantiate x).toCore w`. |
| `Storage.emit_source_meaning` | `stateful-storage` | For every world in which `plan.contract` is installed at the invocation's target account `a` (`installed`), and every invocation whose calldata holds the Word `x` at offset 4, there are a Word `w` and a storage `s` with `storageSourceCall emitted.source (accountStorage a) "run" [x.val] = some (w.val, s)` and `CoreCommits plan.contract invocation installed w s`. |
| `StorageRollback.emit_source_meaning` | `stateful-storage-rollback` | For every such world, installed account `a` and invocation, there is an outcome `o` with `rollbackSourceCall emitted.source (accountStorage a) "run" [x.val] = some o`; `o` is a revert exactly when `x` is odd, and `CoreSettles plan.contract invocation installed o`. |
| `KeyedStorage.emit_source_meaning` | `stateful-keyed-storage` | For every such world, installed account `a` and invocation whose calldata holds the Words `k` and `x` at offsets 4 and 36, there is an outcome `o` with `keyedSourceCall emitted.source (accountStorage a) "run" [k.val, x.val] = some o`; `o` is a revert exactly when `x` is odd, and `CoreSettles plan.contract invocation installed o`. |
| `EventLog.emit_source_meaning` | `stateful-logs` | For every such world, installed account `a`, invocation whose calldata holds the Words `f` and `x` at offsets 4 and 36, and memory `m` with `m 64 = some p` and `p + 64 ≤ 2^256`, there is an outcome `o` with `logSourceCall emitted.source (accountStorage a) m "run" [f.val, x.val] = some o`; `o` is a revert exactly when `f` is odd, and `CoreLogs plan.contract invocation installed o`. |

Each namespace above also has `emit_preserves_meaning`, with the same result and the parsed file
`file` exposed: `emitted.source = file.print`, the fragment's parser gives `some file`, and for the
loop, generic and stateful fragments `file.call` with the same arguments gives the same result.

| Theorem | Statement |
| --- | --- |
| `render_spec`, `primitive_render_spec`, `callGraph_render_spec`, `mutation_render_spec`, `aggregate_render_spec`, `aggregateCallGraph_render_spec` | The inductions over the actual `ScalarRenderer.renderWithFunctions`, `PrimitiveRenderer.render`, `CallGraphRenderer.renderWithFunctions`, `MutationRenderer.render`, `AggregateRenderer.render` and `AggregateCallGraphRenderer.render`. |
| `parseSource_print`, `parseLoopSource_print`, `parseGenericSource_print`, `parseStorageSource_print`, `parseRollbackSource_print`, `parseKeyedSource_print`, `parseLogSource_print` | The printed text of any file whose names are lexically valid and not reserved parses back to that file under the fragment's grammar: for generic files when every generic function has a type parameter and every method-body `match` is in the generic form the parser produces, and for log files when no logger is named `mstore`. |
| `loopSourceCall_of_parseSource` | On every text that `parseSource` accepts, `loopSourceCall fuel` is `sourceCall`, for every fuel. |
| `genericSourceCall_print_loopFree` | On the printing of every loop-free file whose names are lexically valid and not reserved, `genericSourceCall` is `sourceCall`. |
| `loopSourceCall_mono`, `loopSourceCall_unique` | More fuel keeps the result of a completed loop call, so all completed calls of a text return the same word. |

Unsupported operations remain explicit emitter errors; the theorems say nothing about failed
emissions.

### What the conclusions say

- **`sourceCall`** lexes the emitted `String`, parses it and calls the method under the source
  semantics below.
- **`CoreReturns core w`**: Core's `runStateful` returns `.done (.word w) []` for all sufficiently
  large fuel, and every completed run returns exactly that Word and store. This is the Core
  machine of the differential-testing oracle. For the runtime-input, named-helper, raw-primitive,
  call-graph, private-mutation, aggregate and aggregate call-graph profiles it runs the original
  lambda or binding chain applied to the input; for the two loop profiles, the original
  bounded-loop reference; for the generic profile, the original generic reference, which selects
  between two step results with a monomorphic curried selector closure.
- **`CoreReturnsWithStore`** states the same for some final store that every completed run
  reaches, since a Core program with mutable locals ends with its cells in the store. The aggregate
  call-graph renderer refuses cells, and the checks observe an empty final store, but its theorem
  states only `CoreReturnsWithStore`: the proof reuses the store-aware aggregate invariant, which
  does not track that no cell is allocated. The bounded-loop reference keeps its accumulator in the
  store's first cell, and the generic reference's final store holds the cells of its two step calls.
- **`loopSourceCall fuel`** reads a text with the loop grammar and lets each `while` loop evaluate
  its condition at most `fuel` times. A loop that runs out of fuel has no meaning, so the two loop
  theorems state termination: every fuel above the mask, which is at most seven, completes the
  call. **`genericSourceCall`** needs no fuel, since the generic fragment has no loops or
  recursion.
- **`storageSourceCall source s`** calls the method from the storage `s`, which maps each slot to a
  word, and returns the method's word and final storage. The reference
  `StorageContract.canonicalProgram` is a host-runtime contract that reads its input from calldata
  at offset 4 and reaches storage through host requests. So the theorem observes one top-level
  transaction, `TopLevelExecution.run`, the runner of the storage oracle
  (`StorageExecution.observe`), on a world in which the contract is installed.
  `CoreCommits contract invocation installed w s`: with enough fuel the transaction completes, and
  every completed run returns the ABI encoding of `w`, with Core result `w`, and commits a world
  whose target account holds `s` at every slot (`StorageAgrees`). The source call starts from the
  installed account's storage (`accountStorage`), whatever it is, so the theorem applies to each
  transaction of a history in turn. The canonical `run(uint256)` calldata has the input at offset 4;
  the theorem says nothing about other calldata.
- **`rollbackSourceCall source s`** either returns the word with the final storage
  (`RollbackOutcome.returned`) or reverts with the word whose 32-byte big-endian encoding is the
  revert data (`RollbackOutcome.reverted`), keeping none of its storage writes. The reference
  `StorageRollback.canonicalProgram` has the three-way Word outcome profile `wordOutcomeV1`.
  `CoreSettles contract invocation installed o`: with enough fuel the transaction completes, and
  every completed run settles as `o`. A returned outcome returns the word's ABI encoding and
  commits the returned storage. A reverted one reverts with the word's 32-byte encoding and commits
  the world the transaction started from.
- **`keyedSourceCall source s`** calls the two-parameter method with the rollback call's outcomes.
  The reference `KeyedStorage.canonicalProgram` reads its key and input from calldata at offsets 4
  and 36, as the canonical `run(uint256,uint256)` calldata has them.
- **`logSourceCall source s m`** calls the method from the storage `s` and the memory `m` that the
  dispatcher leaves. It returns the word with the final storage and the logs it emitted, in order
  (`LogOutcome.returned`), or reverts (`LogOutcome.reverted`), keeping neither storage writes nor
  logs.
  - The reference `EventLog.canonicalProgram` writes each log as a frame of word logs under
    `EventLog.framingVersion`: a header naming the topic count and the data length with payload
    zero, then the data Words and the topics, each numbered from one. `logFrame emitter l` is that
    framing of a source log `l`.
  - `CoreLogs contract invocation installed o` adds the committed journal to `CoreSettles`. For a
    returned outcome with logs `ls`, its word logs are `ls.flatMap (logFrame invocation.target)`;
    for a reverted one, it is empty.

## Independent source meaning

The source side does not import or mention Core. It is in
[Syntax](../../Solcore/Synthesis/Source/ScalarMeaning/Syntax.lean),
[Semantics](../../Solcore/Synthesis/Source/ScalarMeaning/Semantics.lean),
[Grammar](../../Solcore/Synthesis/Source/ScalarMeaning/Grammar.lean) (printing, lexing, parsing
and the text theorems), and, for the fragments,
[FragmentSemantics](../../Solcore/Synthesis/Source/ScalarMeaning/FragmentSemantics.lean),
[LogSemantics](../../Solcore/Synthesis/Source/ScalarMeaning/LogSemantics.lean),
[LoopGrammar](../../Solcore/Synthesis/Source/ScalarMeaning/LoopGrammar.lean) and
[StorageGrammar](../../Solcore/Synthesis/Source/ScalarMeaning/StorageGrammar.lean).

**Syntax.**

- Expressions: names, decimal literals, `true` and `false`; parenthesized `!` and `~`
  applications; parenthesized infix `+`, `-`, `*`, `&`, `|`, `^`, `==` and `>`; `Typedef.rep(e)`,
  `uint256(e)`, calls `f(a)`, `f(a, b)` and `f(a, b, c)`, pairs `(a, b)`, and the sum constructors
  `inl(e)` and `inr(e)`.
- Statements: `let x: T = e;` with `T` one of `word`, `bool`, `(word, word)` or `sum<word, word>`;
  `x = e;`; `if (e) { ... } else { ... }`; the pair match `match (e) { case (x, y) { ... } }`; and
  the sum match `match (e) { case inl(x) { ... } case inr(y) { ... } }`.
- A file starts with `pragma solcore;`, imports `std` and `std.dispatch`, optionally imports
  `opcode as alias` pairs from `std.opcodes`, declares free functions
  `function f(p: T, ...) returns (T) { ...; return e; }`, and declares one contract with one public
  method whose parameters and result have type `uint256`, ending in `return e;`.

**Tokens.** Spaces and newlines only separate tokens. Identifiers are ASCII letters, digits and
`_`, not starting with a digit; numbers are unsigned decimal; `==` is one token. Every operator
application is parenthesized, so the grammar has no precedence rules; a parenthesized pair has a
comma where an infix operator would be, and a name followed by `(` is a call. Twenty-one words are
reserved, including `let`, `if`, `return`, `true`, `false`, `Typedef`, `rep`, `uint256`, `match`,
`case`, `inl` and `inr`.

**Values.** A word is a natural number below `2^256`. There are also Booleans, `uint256` values
wrapping one word, pairs of two words, and the tags `inl` and `inr` of `sum<word, word>`, each with
one word payload. A literal of `2^256` or more has no meaning.

**Operators** follow the pinned standard library (`std/std.sol` and `std/opcodes.sol` at
solcore-rs `e2eef19409fc8879cd4a9cc342ed60e3152f72c0`). The Rust frontend desugars `+` to
`Add.add`, `==` to `Eq.eq`, `>` to `Ord.gt`, `~` to `BitNot.bnot` and `!` to the function `not`.

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

**Scopes.** Locals live in a stack of lexical scopes. `let` declares in the innermost scope, and
its value must have the annotated type; assignment updates the nearest binding and must keep its
type. An `if` condition must be Boolean, and each branch runs in a fresh scope that is discarded
afterwards. A method binds its `uint256` parameters (each below `2^256`) in a parameter scope, runs
its body in a block scope inside it, and returns the word of a `uint256` result. A failed lookup,
type mismatch or non-Boolean condition has no meaning (`none`).

**Pairs and sums** are builtins of the pinned frontend (`crates/hir/src/nameres/builtins.rs`), not
standard-library definitions. A pair evaluates its components left to right and must hold two
words. `inl(e)` and `inr(e)` tag a word, and both tags have type `sum<word, word>`, so an assignment
may replace one tag by the other. A `match` evaluates its scrutinee once and runs the pair case, or
the `inl` or `inr` case by the scrutinee's tag, in a fresh scope that binds its pattern variables.
The case scope is discarded afterwards, so a case body changes enclosing locals only by assignment.
A scrutinee of another shape has no meaning.

**Calls** evaluate their arguments left to right. A callee resolves to a free function declared
earlier in the file, then to an imported `std.opcodes` alias, then to `std.tobool`. A free function
runs like a method on its typed parameters and must return a value of its declared type. Each free
function sees only the functions declared before it, so a call to a later or recursive function
has no meaning; the emitted helpers call only earlier helpers, matching the Core binding chain. An
alias means only the opcode its import names. The `std.opcodes` wrappers pass their `word`
arguments, in order, to the EVM instruction of the same name, which the source semantics defines
from the EVM specification. Signed operands are read in two's complement.

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

### Fragments

Each fragment has its own grammar and meaning, so `parseSource`, `sourceCall` and the loop-free
results are unchanged by it. Each parser lexes as `parseSource` does. It recognizes an extension by
its first tokens, or by an infix operator where a statement of the smaller grammar would end.

- **Loops** (`parseLoopSource`). A method body may also contain `while (a op b) { ... }` at its top
  level: one infix operation as the condition and a block of loop-free statements as the body. As
  in the pinned frontend (`crates/parser/src/parse/stmt.rs`), the parentheses belong to the loop, so
  the header reads `while (sc_limit > sc_counter) {`. Each evaluation of the condition must give a
  Boolean. While it is `true`, the body runs in a fresh scope, so a `let` in the body ends with its
  iteration. `LoopFile.call fuel` lets each loop evaluate its condition at most `fuel` times and
  has no meaning when a loop runs out; more fuel never changes a result. A text that `parseSource`
  accepts parses under the loop grammar to the same file, with its `sourceCall` meaning for every
  fuel.
- **Generics** (`parseGenericSource`). After its imports, a file may declare generic free functions
  `function f<a, ...>(p: T, ...) returns (T) { ...; return e; }`, where each `T` is a type of the
  fragment or a type parameter. A generic body may contain `if (c) { return e; }`, with no `else`,
  on a local `c`. A method-body statement may be `let x: T = a op b;` or `x = a op b;` with one
  unparenthesized infix operation, also in the cases of a `match`. As in the pinned frontend, type
  parameters follow the name in angle brackets, an `if` needs no `else`, `return` is a statement,
  and an infix operation needs no parentheses. The meaning is dynamic: a type parameter admits
  every value. A guard's local must hold a Boolean; when it is `true`, the guard returns its value.
  Generic functions enter the call context before the ordinary ones. A loop-free file is a generic
  file with the same printing and, when its names are valid and not reserved, the same meaning.
- **Storage** (`parseStorageSource`). A storage file imports
  `{sload, sstore, opcode as alias, ...}` from `std.opcodes`, the aliases optional. Its method body
  may also contain `sstore(slot, value);` and `let x: T = f(a op b);`, and the method returns
  `uint256(e)` or `uint256(a op b)`. Storage maps each slot to a word. The method's statements
  evaluate in the call context extended by `sload`, which returns the current storage's word at its
  slot. `sstore` evaluates its slot, then its value, both words, and replaces that slot's word.
  Free functions see no storage: one that calls `sload` has no meaning, and no expression can call
  `sstore`. The wrappers pass their `word` arguments to the EVM `SLOAD` and `SSTORE`.
- **Rollback** (`parseRollbackSource`). A rollback file imports `sload`, `sstore`, `mstore` and
  `revert_`, optionally followed by aliases. Its method body may contain the storage statements,
  `let x: T = a op b;`, and the revert block
  `if (a op b) { mstore(offset, value); revert_(offset', size); }`. When the block's Boolean
  condition is `true`, the call reverts with `value` exactly when the revert reads the 32 bytes just
  written: `offset' = offset` and `size = 32`. Any other offset or size reads memory that the
  fragment does not model and has no meaning. A revert discards the call's storage writes.
- **Keyed storage** (`parseKeyedSource`). `sload` and `sstore` take any word as their slot, so
  keyed slots need no new form. The one new statement is `let x: T = a + b + c;`, which means
  `let x: T = ((a + b) + c);`, as the pinned frontend folds additive operators to the left
  (`crates/parser/src/parse/expr_pat.rs`). A slot is a word, so the key's successor wraps from
  `2^256 - 1` to 0. Writes to aliased slots replace one another in program order.
- **Logs** (`parseLogSource`). The import adds `mload` after `sstore`, and an alias of `log0` to
  `log4` names that wrapper. The method body may also contain the store `mstore(offset, value);`
  and the log block
  `if (a op b) { let x: T = f(c op' d); mstore(o, v); ... logger(offset, size, t1, ..., tn); }`,
  which binds one call `let` in its own scope, writes memory and emits one log.
  - Memory is known word by word: a byte offset maps to the word whose 32-byte big-endian encoding
    starts there, when the fragment knows it. `mstore` makes its word known and forgets every known
    word whose bytes overlap it. `mload` and a log read only known words, and every access must lie
    below `2^256`.
  - A log's topics are its topic operands, and its data the `size / 32` known words from its
    offset. Its logger must reach the wrapper `logN` for its `N ≤ 4` topics through an import alias,
    and its size must be a multiple of 32; anything else has no meaning.
  - The revert block is the rollback one, which does not read memory. A revert discards the call's
    storage writes and its logs.

## Connection to the actual emitter

The proofs unfold the actual renderers, private helpers included, by definitional equality; no
second renderer is defined. Where an emitter or a Core reference keeps a definition private, the
proof restates it and shows that the actual one reduces to, or equals, the restatement. The
renderer proofs are in
[Internal](../../Solcore/Synthesis/Source/ScalarMeaning/Internal), the emitter proofs in
[PureTheorems](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean),
[LoopTheorems](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean) and
[StatefulTheorems](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean).

- **Scalar.** `render_spec` covers every Core expression that `functionAcceptsAt` admits and the
  renderer accepts: literals, locals, `let`, `if`, `!`, `~` and the eight binary operators. The
  rendered lines, run from frames that agree with a Core environment, evaluate the expression as
  Core's big-step `Evaluates` does and bind the result to the rendered value name. Only temporaries
  in `[first, nextId)` change. `FunctionsAgree` states that each rendered helper name denotes the
  Word function of its closure. Freshness rests on the injectivity of `sc_v<n>` names, from Lean's
  `Nat.toDigits`. The per-constructor lemmas are generic: each assumes only how a renderer prints
  its constructor, a predicate on the call context and the fixed callee names the renderer may
  print. The scalar renderer instantiates them with every context and no fixed callees.
- **Primitives and call graphs.** The primitive renderer copies each raw opcode operand into a
  fresh `word` temporary, left to right, before the call. Shifts pass the amount first, as
  `sar(shift, value)` expects, and the signed comparison prints as `tobool(sc_sgt(a, b))`. The call
  context must satisfy `PrimitiveContext`: each of the fourteen aliases reaches its opcode, and
  `tobool` the standard library function. Each Core Word operation (`udiv`, `sdiv`,
  `shiftArithmeticRight`, `signExtend`, `pow`, `addMod` and the others) agrees with its formula in
  the opcode table. The call-graph renderer also copies a helper call's argument first, and the
  helper names `sc_fn<k>` never shadow an alias or `tobool`.
- **Wrappers.** `emit` prints `run()` returning `uint256(value)`. `Input.emit` prints
  `run(input: uint256)` and binds `sc_input` to `Typedef.rep(input)`, as Core applies the lambda to
  the input. The emitter's helper loop is restated by structural recursion and proved equal to the
  actual `for` loop, and an induction shows that each printed `sc_fn<k>(sc_arg: word)` agrees with
  the closure Core builds for helper `k`.
- **Mutation.** Core keeps each mutable Word local in its store; the source keeps it in an ordinary
  local `sc_c<n>`. Distinct cells hold distinct locations and distinct bindings have distinct
  names, so writing one cell changes no other binding, and every read of a cell is copied to a fresh
  temporary first. A helper cannot
  reach its caller's cells. Core machine results follow from `runStateful_evaluation_sound`,
  `evaluation_runStateful_complete_with_sufficient_fuel` and the determinism of `Evaluates`.
- **Aggregates.** Pair and sum bindings are never cells. A projection prints as a pair match whose
  one case assigns the picked component, so the operand is evaluated once, as Core's `first` or
  `second` is. A Core `case` binds its payload before every existing local; the source binds it
  under a fresh `sc_p<n>` in the selected case's scope. The alias call context is needed only where
  a rendering prints an alias (`usesOpcodeAliases`). The aggregate call-graph proof maps each
  binding to the aggregate binding of the same kind, so the aggregate invariant applies unchanged.
- **Loops.** The entry is printed as `sc_step(sc_arg: word)`. The method sets `sc_limit` to
  `(sc_input & mask)` and, while `sc_limit > sc_counter`, assigns `sc_step(sc_acc)` and counts. The
  Core reference (`BoundedLoop.canonicalProgram`) has no counter: for each literal ordinal below the
  mask, it applies the entry to the accumulator cell when the bound exceeds the ordinal. Its private
  guards are restated (`loopGuards`), and an induction on the steps left (`boundedLoop_agrees`)
  shows that both apply the step equally often; `storeLoop_agrees` repeats it over stores that the
  aggregate steps extend.
- **Generics.** The file declares `sc_select<a>(flag: bool, left: a, right: a)`. The method applies
  `sc_step` to `sc_input` and `sc_input + 1` and selects between the results by the input's low bit,
  at `word`, `(word, word)` or `sum<word, word>`. The proof restates the reference's private
  definitions and shows that the applied program reduces to the restatement
  (`genericApplied_body`). `aggregateLoop_spec_named` adds that each helper is named
  `sc_fn<k>`, so no helper shadows `sc_select`.
- **Storage.** The method reads slots 0 and 1, stores `sc_step(input + slot 0)` in slot 0 and slot 1
  plus one in slot 1, reads both back and returns their sum (`storageMethod_run`). The restated Core
  wrapper runs on the host-aware Core machine, which suspends at every host request.
  `storage_handled` builds the run through its seven requests as a `HostDriver.HandledSteps` path,
  and `HostDriver.run_done_complete` turns it into the raw run of every fuel at least its length.
  `topLevel_run_completed` completes the transaction, and the handler's read-after-write laws give
  the word and the committed account (`storageAgrees_writes`). By
  `TopLevelExecution.resumeWithFuel_run`, every completed run has the same result.
- **Rollback.** For an odd input the method stores the sum at memory offset 0 and reverts with those
  32 bytes (`rollbackMethod_run`), as the reference's completion does by the input's low bit
  (`rollbackCompletion_evaluates`). `topLevel_run_settled` commits the working world for a return
  and the starting world for a revert, and `rollback_parity` turns the low bit into parity.
- **Keyed storage.** The method writes the key slot, the key's wrapping successor and slot zero, in
  that order, and reads them back (`keyedMethod_run`), through ten host requests (`keyed_handled`).
  `storageAgrees_write` keeps the account in agreement after each write, whether or not the slots
  alias, so the result holds for every key, zero and `2^256 - 1` included.
- **Logs.** The method also reserves 64 bytes from the free-memory pointer at offset 64. Each site
  reads only the words it has just stored (`siteStmt_run`). `log_handled` runs the sites by
  induction (`sites_handled`), and the final working journal is the framing of the source logs in
  order (`sitesContext_logList`). `topLevel_run_logged` extends `topLevel_run_settled`: a returned
  transaction commits its working journal, and a reverted one the empty checkpoint journal.
- **Text.** The text theorems show that the printed text lexes to exactly the file's tokens and that
  each fragment's parser inverts them. The meaning is therefore a function of the emitted `String`,
  not of an internal printer argument.

## Assumptions outside the theorem

The theorem relates emitted text to Core. These steps of the actual Rust pipeline are assumed, and
only the existing tests exercise them:

1. **Parsing.** The pinned Rust parser reads the emitted text as the same structure as this
   grammar: tokens, the parenthesized operator forms, pairs, the types `(word, word)` and
   `sum<word, word>`, and the two `match` forms with their case patterns.
2. **Name resolution and typing.** The imports bring `word`, `bool`, `uint256` and `Typedef` into
   scope; the operators resolve to the cited `word` instances and `!` to `std.not`; pairs, `sum`,
   `inl` and `inr` resolve to the frontend builtins; decimal literals elaborate at `word`, also
   inside pairs and in `inl(0)`; and the frontend accepts every emitted program. Rust acceptance is
   not proved.
3. **Standard library and builtin meaning.** The instance chains and opcode wrappers behave as the
   tables say, and pairs, sums and `match` as described above. The transcription is manual and
   cites the pinned files; it is not derived from the Rust frontend. In particular, the raw
   `std.opcodes` wrappers do not revert for a zero modulus, unlike the public `std.addmod` and
   `std.mulmod`, and the target EVM provides `CLZ`.
4. **Compilation and execution.** Specialization, lowering (of pairs, sums and matches too),
   Sonatina or Yul code generation, optimization, EVM execution and `std.dispatch`, including
   selector dispatch, `uint256` ABI decoding and 32-byte result encoding. Gas and EVM resource
   limits are not modeled; the loop meaning's fuel bounds iterations, not gas.

What each later emitter adds, under these four:

- **Aggregate call graphs:** nothing. That the frontend accepts helper calls inside `if` branches
  and `match` cases is part of 2, and their lowering of 4.
- **Call-graph loops:** the `while` loop. The parser reads `while (...) { ... }` as a loop, `while`
  being a contextual keyword, and the frontend lowers it to a `For` statement without initializer or
  post statements (`crates/parser/src/parse/stmt.rs`), which evaluates its Boolean condition before
  every iteration and runs the body as a block scope.
- **Aggregate loops:** nothing further. The step uses only the forms above, and the wrapper is the
  same `while` loop.
- **Generics:** the selector and the unparenthesized infix statements. The parser reads
  `function sc_select<a>(flag: bool, left: a, right: a) returns (a)` as a function with the type
  parameter `a`, and `sc_input + 1` as the same `Add.add` as its parenthesized form. The frontend
  instantiates `a` consistently at `word`, `(word, word)` and `sum<word, word>`, which the source
  meaning does not check, and specialization keeps the dynamic meaning: each call returns `left`
  when `flag` holds and `right` otherwise.
- **Storage:** the parser reads the import as the selection of those names and `sstore(...)` as an
  expression statement; `sload` and `sstore` mean the EVM `SLOAD` and `SSTORE` of the contract's own
  storage. At the start of a call the deployed contract's storage is the committed storage that the
  Core reference reads, a returning transaction commits its writes, and `std.dispatch` decodes the
  word at offset 4 as the argument. Gas, including `SSTORE` costs and refunds, is not modeled.
- **Rollback:** `mstore` and `revert_` mean the EVM `MSTORE` and `REVERT`. The revert returns the
  32-byte encoding of `sc_result`, and a reverting call discards its storage writes. Memory at
  offset 0 is written only just before the revert. Gas, including memory expansion, is not modeled.
- **Keyed storage:** the parser folds the three-term sum to the left; `SLOAD` and `SSTORE` address
  any word slot; `std.dispatch` decodes the words at offsets 4 and 36 as `key` and `input`.
- **Logs:** `mload`, `mstore` and the `logN` aliases mean the EVM `MLOAD`, `MSTORE` and `LOG0` to
  `LOG4`, so a log's data are the bytes from its offset and its topics are its last arguments.
  `std.dispatch` leaves the free-memory pointer at offset 64 (`mstore(0x40, memoryguard(128))` in
  `std/dispatch.sol`); the theorem assumes only that this word is known and its 64-byte buffer
  lies below `2^256`, and dirty bytes past the pointer do not matter. A reverting transaction
  discards its logs with its storage writes. Reading committed frames as multi-topic logs is the
  observer's convention (`EventLogExecution.decodeJournal`), which the executable checks exercise
  and the theorem does not restate. Gas, including memory expansion and log costs, is not modeled.

Differential agreement remains evidence for these steps, not a proof. Agreement in a corpus also
does not replace this theorem for the printer.

## Scope and what remains

The theorems cover `ScalarRenderer.renderWithFunctions`, `PrimitiveRenderer.render`,
`CallGraphRenderer.renderWithFunctions`, `MutationRenderer.render`, `AggregateRenderer.render`,
`AggregateCallGraphRenderer.render` and fifteen actual emitters: closed G0 (`closed-g0`), runtime
input (`runtime-word`), named helpers (`runtime-functions`), raw primitive aliases
(`runtime-primitives`), call graphs (`runtime-call-graphs`), private mutable locals
(`runtime-mutation`), Word aggregates (`runtime-aggregates`), aggregate call graphs
(`runtime-aggregate-call-graphs`), call-graph loops (`runtime-call-graph-loops`), aggregate loops
(`runtime-loops`), generic selection (`runtime-generics`), two-slot storage (`stateful-storage`),
two-slot rollback (`stateful-storage-rollback`), keyed storage (`stateful-keyed-storage`) and event
logs (`stateful-logs`).

**Not covered.** The other emitters that render with `AggregateRenderer`: closures, comptime,
modules, storage mappings, sender-keyed ledgers, dynamic arrays, dynamic bytes, long bytes, call
value, contract calls and forwarded value. Their texts use forms outside these fragments, such as
hashed storage access, dynamically sized memory, calldata reads, external calls, lambdas and
multi-file module bundles.

**Limits of the fragments.** The grammars admit only the forms listed under
[Fragments](#fragments). The storage grammar admits `sload` only in the method and `sstore` only as
a statement of the method body, and unparenthesized infix operations only as the argument of a call
`let`, a store operand and in the returned `uint256(...)`. The stateful theorems cover:

- storage: one transaction of an installed contract with calldata whose word at offset 4 is the
  input. Deployment, other accounts, balances, logs, reverts and gas are outside it.
- rollback: both outcomes of one transaction under the same hypotheses. The transaction's other
  effects, memory beyond the one word and gas are outside it.
- keyed storage: both outcomes of one transaction for every key, with calldata whose words at
  offsets 4 and 36 are the key and the input.
- logs: both outcomes of one transaction, with the logs a returned transaction commits, for every
  memory whose pointer word at offset 64 is known with its buffer below `2^256`. Memory the fragment
  does not know, memory expansion and gas are outside it.

## Executable checks

The checks in [SourceMeaning](../../Solcore/Test/Synthesis/SourceMeaning.lean), registered in the
test driver, run actual emitter output through the source meaning and compare it with Core. Each
text must also reparse under its grammar and print back to itself. A fragment's text must be
rejected by `parseSource`, and a stateful fragment's also by the stateful grammars before it.

| Check | Emitters | Compared with Core, and also checked |
| --- | --- | --- |
| `SourceScalarMeaning` | closed, runtime input, named helpers, raw primitives, call graphs, mutation | `sourceCall` at eight boundary inputs, and hand-known Words. An alias that is not imported is rejected, and swapping two aliases swaps their meanings. Extra or missing arguments, an undeclared method, `= =`, an unparenthesized operator, an undeclared local, a mistyped declaration, an undeclared helper and a literal of `2^256` are rejected. |
| `SourceAggregateMeaning` | `Aggregate.emit` | The same inputs, with the `if` and `case` joins at Word, Boolean, Unit, pair and sum targets, raw primitives inside and around pairs, sums and cells, and generated graphs. The aliases are imported exactly when a body uses one. |
| `SourceAggregateCallGraphMeaning` | `AggregateCallGraph.emit` | Every composition shape, and an empty final Core store. |
| `SourceCallGraphLoopMeaning` | `CallGraphLoop.emit` | `loopSourceCall`: agreement at one more unit of fuel than the iterations and above the mask, and no meaning at fuel equal to the iterations. A final store of one cell, holding the result. |
| `SourceLoopMeaning` | `Loop.emit` | The same fuel checks; the accumulator cell first in the store, then Word cells. |
| `SourceGenericMeaning` | `Generic.emit` | `genericSourceCall` at each variant; Word cells only in the final store. |
| `SourceStorageMeaning` | `Storage.emit` | `storageSourceCall` transaction by transaction against `TopLevelExecution.run`: the returned word, its ABI bytes and committed slots, from empty and nonempty storages. |
| `SourceRollbackMeaning` | `StorageRollback.emit` | Returned and reverted bytes and committed slots; odd inputs revert. |
| `SourceKeyedMeaning` | `KeyedStorage.emit` | The key slot, its successor and fixed slots, including keys that alias the counter. |
| `SourceLogMeaning` | `EventLog.emit` | The committed journal, which must be the framing of the source logs and decode to them with `EventLogExecution.decodeJournal`; reverted transactions commit no log. |

Each check also runs altered texts, such as a store to another slot or a flipped condition, and
checks that each keeps, changes or loses its meaning as expected.
