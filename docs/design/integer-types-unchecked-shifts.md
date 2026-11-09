# Integer types, `unchecked` blocks and shifts

Updated: 2026-11-04. Module paths and file counts below predate the layout
refactor of f820cc25f; the marker `-- leanmerge: from <old module>` finds each
old module's current file
([following older notes](../guide/conventions.md#following-older-notes)).

Rows 1 to 3 of the roadmap table "Following upstream's semantics: the next
units" bring three solcore-rs changes to Lean's source language:

- checked integer types and literal defaulting (#95);
- `unchecked` blocks (#119);
- the shift operators (#129).

Lane E's generator side already compares the compiled paths with Core
references for these rows (roadmap, "Checked arithmetic, `unchecked` blocks
and shifts: probe and definitions"). This note covers the Lean side: the
parser, typing, the source semantics and the lowering to Core.

It records:

- how Lean's frontend handles integers today;
- upstream's semantics at the pin, with a probe of the pinned Rust paths;
- the design for each layer, with the alternatives;
- the order of implementation.

## Lean today

Lean's source language has these features neither as upstream's std modules
nor as builtins of its own.

- **Types.** The builtin types are `word` (also spelled `Word`), `bool`,
  `unit` and the unbounded `integer` (`TypeSystem.BuiltinType`). No `uint8`
  to `int256` exists.
- **No std.** There is no prelude and no `std`: `import * from std;` fails
  with `unknownModule`, because a raw workspace has only main and external
  libraries.
- **No upstream std syntax.** There is no `struct`. Trait-qualified calls
  such as `Typedef.abs(x)` and field places such as `x.value` are not typed.
  Upstream's std is written with all three.
- **Operators.**
  - On `word` they are builtin primitives that wrap. `/` and `%` by zero give 0.
  - On `integer` they are accepted only next to an open literal.
  - On a declared type they dispatch to a one-parameter trait that the program
    declares itself (`trait Add<T>`, `impl Add<Token>`).
  - Compound assignment is `word`-only.
  - There is no unary minus.
  - `<<` lexes as two `<` tokens and does not parse.
  - There is no `unchecked`.
- **Literals.** Each integer literal gets a fresh type variable with a builtin
  `Int` requirement. Context decides its type. A literal still open after
  inference defaults to `word`. Targets other than `word` and `integer` are
  rejected. A `word` literal wraps modulo 2^256 without a range check.
- **Failures.** A source program fails through a Core language failure whose
  `word` reason the fault-site table maps to a `RuntimeError` diagnostic
  (fall-through, uninitialized read, escaped control, assignment and
  data-place sites). The public API returns `.failed reason session`, and
  `session.diagnostic key reason` decodes it. Nothing in the source pipeline
  produces revert data, and the source semantics has no revert: its outcomes
  are values and structural faults.
- **ABI.** The public API calls functions with typed values, not calldata.
  Source contracts are only catalogued.

Upstream defines `uint8` … `int256` in std as structs wrapping a `word`.
Operators are trait impls, and literals go through `Int.fromInteger(comptime
x: integer)`. To read that std, Lean would need structs, trait-qualified
calls, a bundled std, compile-time evaluation of `fromInteger`, a `panic`
builtin, trait-dispatched compound assignment and two-parameter operator
traits. Each of these is a frontend feature with its own proofs.

## Upstream's semantics at `e2eef194`

The summary below comes from std (`std/std.sol`, `std/unsigned.sol`,
`std/signed.sol`, `std/unchecked/*.sol`), the compiler (`crates/parser`,
`crates/hir-ty`, `crates/specialize`) and the fixtures `checked-arith`,
`int-ops`, `issue92-checked-defaults`, `unchecked-scope` and
`shift-operators`. The probe below confirms every behaviour this design relies
on.

**Types.** `uintN` has the range `[0, 2^N − 1]` and `intN` the range
`[−2^(N−1), 2^(N−1) − 1]`, for N in 8, 16, 32, 64, 128 and 256. The
representation is a `word`: an unsigned value as it is, a signed one in two's
complement sign-extended from bit N − 1.

**Checked arithmetic**, outside `unchecked` blocks:

| Operation | Result | Panic |
| --- | --- | --- |
| `a + b`, `a - b`, `a * b` | the exact result | `0x11` when it leaves the type |
| `a / b` | the quotient rounded toward zero | `0x12` when `b = 0`; `0x11` for `MIN / −1` |
| `a % b` | the remainder, with the dividend's sign | `0x12` when `b = 0`; `MIN % −1` is 0 |
| `-a` | `0 − a` | `0x11` for any nonzero unsigned value and for `MIN` |

A panic reverts with 36 bytes: the selector `0x4e487b71`, then the code as a
32-byte big-endian word.

**`unchecked { … }` blocks.**

- **Wrapping.** Inside a block, `+ - * / %`, unary `-` and the compound
  assignments `+= -= *= /= %=` wrap the exact result to the type's width. `MIN
  / −1` gives `MIN`. Division and remainder by zero still panic with `0x12`.
- **Lexical scope.**
  - A block reaches the statements written in it, including nested blocks,
    `if`, loops and `match` arms.
  - It does not reach lambda bodies written in it, functions or lambdas called
    from it, or anything after it.
  - A lambda body may contain its own block.
  - A block directly inside another block is rejected (`SC0001`).
- **Unaffected operators.** Shifts, bitwise operators and comparisons are the
  same in both contexts.
- **Syntax.** The block is a statement, not an expression. `unchecked` is a
  contextual keyword and stays a valid identifier.
- **`word`.** `+ - *` and unary `-` wrap in both contexts. But `/ 0` and `% 0`
  give 0 outside a block (raw EVM division) and panic with `0x12` inside one.
  This is because std's `UncheckedDiv<word>` checks the divisor.
- **Imports.** Upstream requires `std.unchecked.unsigned` or
  `std.unchecked.signed` to be imported (`SC0207` otherwise).

**Shifts.**

- **Syntax.** `<<` and `>>` are two adjacent `<` or `>` tokens. `<<=` is `<`
  followed by `<=`, and `>>=` is `>` followed by `>=`. The tokens must be
  adjacent.
- **Precedence.** From tightest to loosest: unary, `* / %`, `+ -`, then `<<
  >>` (left-associative), `&`, `^`, `|`, comparisons, equality, `&&`, `||`.
- **Types.** The result has the left operand's type. The amount is a `word` or
  an unsigned type (`Shl<T, n> where n: ShiftAmount`). A signed amount is
  rejected (`SC0207`).
- **Semantics.** A shift never panics.
  - `v << s` is 0 when `s` is at least the type's width, and otherwise `v ·
    2^s` wrapped to the type.
  - `v >> s` is the floor quotient by `2^s`: logical for unsigned types and
    `word`, arithmetic for signed types. It is 0 or −1 when `s ≥ 256`.

**Bitwise operators and comparisons** on the integer types operate on the
values. Bitwise operators use two's complement within the type: unsigned
results are masked and signed ones sign-extended. Comparisons are signed for
`intN`.

**Literals.**

- **Typing.** Context types a literal: an annotation, a parameter, a return
  type, or the other operand.
- **Defaulting.** A literal still open after inference defaults to `uint256`
  when its type occurs in an operator or comparison obligation, or when it is
  a numeric pattern. Otherwise it is rejected as ambiguous (`SC0299`), for
  example `let y = 7;` when `y` is never used. It never defaults to `word`.
- **Range.** At an integer type, an out-of-range literal is a compile error
  (`SC0409` or `SC0411`). This includes any negative literal at an unsigned
  type. A `word` literal wraps modulo 2^256, so `-1` is `2^256 − 1`, and an
  `integer` literal is exact.
- **Negative literals.** A `-` applied directly to a literal is part of the
  literal, through parentheses and repeated. So `-128`, `-(128)` and
  `- -5` are literals, and `-128` is accepted at `int8`.
- **Numeric patterns** are allowed only on `word`, `integer` and `uint256`
  scrutinees.

**ABI.** std's decoder rejects an argument whose word is not the canonical
representation of a value of its type. It reverts with
`DirtyHigherBitsForInteger()` (`0x6cc54a63`) before the body runs. The
encoder masks or sign-extends results.

## Probe of the pinned Rust paths

Lane D's probe compiled hand-written contracts through checked Hull export,
Sonatina O0 and O2, and Yul (`export-rust-yul.py` with solc 0.8.35). It ran
them on Anvil and in the Lean Hull runner on the O0 export, against lane E's
Python model of the semantics above. Every call matched on every path.

| Probe | What it covers | Calls per path |
| --- | --- | --- |
| Contexts, for `uint8`, `uint256`, `int8` and `int256` | Checked and unchecked `+ - * / %` and unary `-` at extreme operands, including `MIN / −1`, `MIN % −1` and every sign of `/` and `%`. A block around an `if`, an `else`, a `for` loop and a `while` loop. A lambda written inside a block, with and without its own block. A lambda with its own block called from checked code, and a lambda value held outside a block. A checked helper called from a block, and a helper with its own block called from checked code. Compound assignments inside and outside a block, and checked code after a block. All six comparisons, `& \| ^ ~`. `<< >> <<= >>=` by amounts from 0 to `2^256 − 1`, inside and outside a block. For `uint256`: defaulted literals, checked and in a block, with a defaulted zero divisor; the precedence of shifts against `+`, `*`, `&`, `^`, `\|` and comparisons; `word` shifts | 2,312, 2,411, 5,512 and 5,512 |
| Words and literals | `let w: word = -1`; `-w` on `word` inside and outside a block; `-0` at `uint8`; `-128`, `-(128)` and `- -5` at `int8`; a variable shadowed inside a block; `unchecked` as a variable name; a `return` inside a block; a literal typed `word` or `uint8` by its later uses | 90 |
| Division of words | `word / 0` and `% 0` outside a block, inside one, in a compound `/=`, in a lambda written in a block, and in a helper called from a block. `-a * b` as `(0 − a) * b`. Numeric patterns on `uint256` | 710 |
| ABI | For all twelve types, a function returning its argument and one adding two arguments: canonical and non-canonical arguments | 598 |

A compile probe of 59 sources through checked Hull export recorded which
programs the frontend accepts.

- **Literals.**
  - Accepted: `255`, `0xff` and `-0` at `uint8`; `127`, `-128`, `(-128)`,
    `-(128)` and `- -5` at `int8`; `−2^255` at `int256`; `2^256 − 1` defaulted;
    `-1` at `word`.
  - Rejected with `SC0411`: `256`, `0x100` and `-1` at `uint8`; `128` and
    `-129` at `int8`; `−2^255 − 1` at `int256`; `2^256` defaulted; `let k = -1;`;
    `a + 300` and `a < 300` with `a: uint8`; `a << (-1)`.
- **Defaulting.**
  - Rejected as ambiguous (`SC0299`): `let y = 7;` unused, `let y = 7; let z = y;`,
    `sc_id(7)` with an unused result, and `lam () { return 7; }` never called.
  - Accepted: `7 == 7`, `7 + 1` unused, `return sc_id(7);`, `1 << 3` and a
    `match` on an open literal.
- **Types and shifts.**
  - Rejected: `uint8 + uint16` (`SC0201`), `uint256 << int8` (`SC0207`), and
    numeric patterns on `uint8` and `int8` (`SC0201`).
- **Blocks.**
  - Rejected: a nested block (`SC0001`), `unchecked { … }` as an expression
    (parse error), and a block without an unchecked import, even with only
    `word` operators (`SC0207`).
  - Importing both unchecked modules with `*` is ambiguous (`SC0120`), because
    the signed one re-exports the unsigned traits.

Lane E's own probe of these rows matched 94,860 outcomes on the same paths
(roadmap, "Checked arithmetic, `unchecked` blocks and shifts: probe and
definitions"). No path departed from the model in either probe, so no
upstream defect was recorded.

## Design

**The twelve types are builtins.** Lean gains `uint8` … `uint256` and `int8`
… `int256` as builtin types, resolved before declared types like `word`.
Their operators join the builtin operator path that `word` and `integer`
already use.

A Lean port of upstream's std was the alternative. It would need the seven
frontend features listed above, and every arithmetic operation would become a
trait method call. Lean programs do not import anything for the builtins.
Since they have no std, the import that upstream requires for `unchecked`
blocks has no Lean counterpart.

### Syntax

- **Shifts.** The expression parser gains a shift layer between `+ -` and
  `&`. It reads two adjacent `<` or `>` tokens, as upstream does, so that type
  arguments still close with two `>` tokens (`Option<Option<a>>`).
  - Assignment statements read `<` before an adjacent `<=`, and `>` before an
    adjacent `>=`, as `<<=` and `>>=`.
  - `BinaryOp` gains `shiftLeft` and `shiftRight`, and `ValueAssignOp` gains
    the two compound forms.
  - The lexer is unchanged. The precedence ladder is renumbered: `* / %` 9,
    `+ -` 8 and shifts 7, with the rest as before.
- **Unary minus.** `UnaryOp` gains `negate` for a prefix `-`.
- **Blocks.** `StatementValue` gains `unchecked`, parsed when the contextual
  keyword `unchecked` is followed by `{`. (Implemented without the
  constructor: see [unchecked blocks as
  implemented](#unchecked-blocks-as-implemented-without-division).)
- **Desugaring.** A pass between parsing and inference removes every
  `unchecked` statement:
  - It replaces the block with a plain block.
  - It replaces `+ - * / %`, unary `-` and the five arithmetic compound
    assignments written in it with unchecked operators: five `BinaryOp`
    constructors, one `UnaryOp` constructor and five `ValueAssignOp`
    constructors that the parser itself never produces.
  - It starts each lambda body outside any block, so that a block reaches
    no lambda body written in it, while a lambda body may hold its own
    block. It rejects a block nested in a block.

  The typed IR, the source semantics and the lowering therefore see no new
  statement form.

### Typing

- **Literals.**
  - Accepted targets are `word`, `integer` and the twelve types. At an integer
    type, an out-of-range value is a compile error. A `word` literal wraps and
    an `integer` literal is exact, as now.
  - A `negate` applied to a literal, through groups and repeated, types as one
    literal with a negative value.
  - Open literal targets default to `uint256`, where they defaulted to `word`.
    The conditions are: the literal is an operand of a deferred builtin
    operator (arithmetic, bitwise, comparison or a shift's value or amount),
    it occurs in a pending non-`Int` requirement, or it is a numeric pattern.
    Any other open literal is rejected as ambiguous.
  - Numeric patterns are admitted on `word`, `integer` and `uint256`.
- **Operators on the integer types.**
  - Arithmetic, bitwise operators and comparisons take two operands of the
    same type.
  - A shift's value is a `word` or an integer type, and its amount is a `word`
    or an unsigned type, typed independently of the value.
  - Unary `-` and `~` take one operand.
  - Compound assignment takes the target's type.
  - The checked and unchecked forms type alike.
  - On a declared type, an unchecked operator dispatches to upstream's traits
    `UncheckedAdd`, `UncheckedSub`, `UncheckedMul`, `UncheckedDiv` and
    `UncheckedMod` (methods `add`, `sub`, `mul`, `div` and `mod`).
  - Unary minus on a declared type is rejected: upstream reads it as `0 − e`,
    which needs `Int` of that type, and Lean's `Int` is builtin.
  - Shifts on a declared type are rejected too. Upstream's `Shl<t, n>` and
    `Shr<t, n>` take two parameters, and Lean's operator traits take one
    (`Coerce` is the only two-parameter trait the frontend selects).
    Two-parameter operator traits are left for later.

### Source semantics

- **Values.** `Dynamic.Value` gains a constructor for an integer-type value
  holding its exact `Int`, in range by typing. The primitive relations
  dispatch on value shapes, so the new constructor lets the existing rules
  tell `word` and `uint8` apart, as `.integer` already does for `integer`.
- **Primitive rules.**
  - Checked and unchecked arithmetic, negation, bitwise operators,
    comparisons and shifts, defined on the exact values as in the table
    above.
  - Quotients and remainders round toward zero (`Int.tdiv` and `Int.tmod`).
    The `/` and `%` of Lean's `Int` are Euclidean.
  - `word` gains shifts, and unchecked `/` and `%` that panic on a zero
    divisor.
- **Panics.** `SemanticFault` gains `panic (code)`. A primitive operation that
  panics is a new base case of the operator and assignment fault relations,
  so the existing fault propagation carries it out of every enclosing
  construct.
- **Literals.** A literal at an integer type constructs its value. A negative
  `word` literal wraps.

### Lowering

- **Representation.** Integer-type values are Core words in two's
  complement.
- **Operations.** The lowering chooses the operation from the operands'
  source types, because their Core type is `word` for every integer type.
  - A checked operation converts its operands to Core integers, computes the
    exact result, and either returns a language failure or converts the
    result back to a `word`.
  - An unchecked operation wraps.
  - Shifts use `wordShl`, `wordShr` and `wordSar`, then mask or sign-extend.

  These Core expressions compute what the semantics defines, and the lowering
  proofs relate them directly.
- **Panic sites.** Each panic site has its own failure reason. The fault-site
  table maps it to a new `RuntimeError.panic` diagnostic carrying the code and
  the operator's span.
- **No Core change.** Core's syntax and semantics, the Hull importer and the
  shared contract runtime are unchanged.

### Public API

- **Values.** An integer-type argument or result is a `.word` holding the
  representation, with the integer type as its source type.
- **Non-canonical arguments.** An argument whose word is not the canonical
  representation of a value of its type is rejected before the body runs, as
  a data-conversion error. This is the Lean counterpart of std's
  `DirtyHigherBitsForInteger()` revert; Lean's API has no calldata.
- **Panics.**
  - A run that panics ends with `.failed reason session`, and
    `session.diagnostic key reason` gives the panic, its code and its site.
  - A function of the diagnostic gives upstream's 36 bytes of revert data.
  - How a panic is presented is a choice about Lean's API, which has no
    revert channel. Which programs panic, and with which code, follows
    upstream.

## Alternatives

- **A Lean std.** A port of `std.unsigned`, `std.signed` and
  `std.unchecked.*` to Lean's dialect, as described above. It is rejected for
  the frontend features it needs and the call per operation.
- **Values as words.** Integer-type values would be `.word` values in the
  semantics, with primitive rules indexed by the operands' static types. It is
  rejected because every binary, unary and assignment evaluation rule, and
  every fault rule, would then need the operand's static type as a premise.
- **A typed `unchecked` statement.** A statement form kept through the typed
  IR to the semantics. It is rejected because about 32 SourceSemantics
  modules match the typed statement forms exhaustively, against 5 that match
  `BinaryOp`.
- **`<<` and `>>` tokens.** It is rejected because a `>>` token would break
  nested type arguments unless the type parser split it, and upstream joins
  adjacent tokens too.
- **A panic outcome.** A new control outcome beside values and faults. It is
  rejected because every sequencing rule would have to propagate it, while a
  fault reason reuses the fault propagation.

## Order and commits

The rows are implemented in the order 3, 2, 1, one commit each. Each commit
has runtime tests through the public API whose expectations come from the
probe and from the upstream fixtures.

1. **Shifts (row 3).** `<<`, `>>`, `<<=` and `>>=` on `word`: parsing,
   precedence, typing and the Core shifts.
2. **`unchecked` blocks (row 2).** Parsing, desugaring and unchecked
   operators. On `word` they differ from checked ones only for a zero divisor,
   so this row also brings panics: the fault reason, the failure reasons, the
   `panic` diagnostic and revert data. Its tests observe the lexical scope
   through `word` division, inside a block, in a lambda written in a block,
   and in a helper called from one.
3. **Integer types (row 1).**
   - the twelve types and their values, literals, range checks and the
     `uint256` default;
   - unary minus;
   - checked arithmetic;
   - the integer types' shifts, unchecked operators, bitwise operators and
     comparisons;
   - the API's canonical-argument check;
   - ports of `checked-arith`, `unchecked-scope`, `shift-operators` and the
     parts of `issue92-checked-defaults` and `int-ops` that need no
     conversion between `word` and the integer types.

The roadmap orders the rows 1, 2, 3, because unchecked blocks change nothing
without checked types. With panics brought in by `word` division, rows 3 and
2 are observable on their own and smaller than row 1, so this order builds
the operator and panic plumbing first.

### Shifts as implemented

- **Parsing.** One decoder reads an operator from one token or from two
  adjacent ones (`BinaryOp.at?`, `ValueAssignOp.at?`), and the parser and its
  declarative grammar both use it.
- **Typing.** Inference types a shift before any dispatch: the value and then
  the amount unify with `word`, so an open literal operand is a `word` at
  once. The dispatch map gives shifts no trait.
- **Semantics.** `BinaryPrimitiveApplies` gains the two `word` shifts, and
  the compound forms apply them. A shift of any other value is an operand
  fault.
- **Lowering.** Shifts lower to `wordShl` and `wordShr`. A compound shift of
  a local uses a frontend copy of Core's compound-assignment shape, so Core is
  unchanged.
- **Integer targets.** The data-place lowering already refused compound
  assignment outside `word` and `integer`. It now also refuses shifts at
  `integer`, which typing never produces. The assignment profile shared by its
  theorems says the same: `T = .integer ∧ operator.isShift = false` (now
  `wordOnly`, below).
- **Legacy fragments.** The older strict-`word` evaluators leave the shifts
  out.

### Unchecked blocks as implemented, without division

- **No statement form.** Inference reads `Syntax.Statement` itself, and its
  functional-induction proofs name 514 numbered cases in 25 files, so a
  `StatementValue` constructor would reach them even though no typed program
  keeps it. `Syntax.Unchecked` works around the parser instead:
  - it records each `unchecked` at a statement start (after `{`, `}` or `;`)
    that is followed by `{`;
  - it replaces the keyword's bytes with spaces, so the parser reads a plain
    block statement and every span stays the same;
  - after parsing, `mark` gives each recorded block's arithmetic its unchecked
    operators. `ProgramLoading` runs both steps.

  A block written in another block, or a recorded `{` that starts no block
  statement, is a load error.
- **Operators.** `BinaryOp` and `ValueAssignOp` gain `uncheckedAdd`,
  `uncheckedSubtract` and `uncheckedMultiply`, which only the pass produces.
  - On `word` they type, run and lower as the checked operators.
  - On a declared type they dispatch to `UncheckedAdd`, `UncheckedSub` and
    `UncheckedMul`.
  - On `integer` inference rejects them, since upstream defines no unchecked
    instance for it.
  - A literal operand is a `word` at once rather than deferred: with `integer`
    excluded, `word` is the only literal target left.
- **Division and remainder.** `/`, `%`, `/=` and `%=` written in a block are a
  load error (`Syntax.Unchecked.Error.division`). Upstream's unchecked division
  and remainder panic with `0x12` on a zero divisor, and Lean has no panics
  yet, so no typing rule, semantic rule or lowering theorem mentions them.
- **Word-only compound assignment.** `ValueAssignOp.wordOnly` (the shifts and
  the unchecked arithmetic) replaces row 3's `isShift`. The data-place lowering
  refuses these operators at `integer` leaves, and the assignment profile its
  theorems share reads `T = .integer ∧ operator.wordOnly = false`.

**Out of scope:**

- conversions between `word` and the integer types: upstream's are std
  functions, and none of these rows needs them;
- conversions between two integer types;
- `pragma solcore;` (row 5);
- reads of uninitialized locals, which Lean keeps faulting on by decision
  ([closure capture by value](../guide/source-semantics.md#closures-capture-by-value)).

## Consequences for existing programs

Open literals that defaulted to `word` now default to `uint256`:

- Their arithmetic becomes checked, so results differ only where a value
  leaves `uint256`.
- Literals that nothing constrains are rejected, for example an unused
  `let skipped = 99;`.
- Golden outputs that print literal types change.

The tests these changes affect are adjusted in the row-1 commit and listed in
the hand-over note, with every theorem statement that each commit changes.

## Resume point

The unit is required, and it is paused after row 3 and part of row 2
(2026-11-04).

**Done.**
- Row 3, shifts: [shifts as implemented](#shifts-as-implemented).
- Row 2 without division and remainder:
  [unchecked blocks as implemented](#unchecked-blocks-as-implemented-without-division).

The public-API tests are `Tests.SourceCoreShiftExecution` and
`Tests.SourceCoreUncheckedExecution` in
`Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean`.

**Remaining, in order.**

1. **Panics**, designed once for every unit that needs them: unchecked `/` and
   `%`, row 1's checked arithmetic, and row 4's array panics. They need:
   - the fault reason `SemanticFault.panic code` and its fault rules;
   - a Core failure reason per panic site, with a `RuntimeError.panic`
     diagnostic;
   - upstream's 36 bytes of revert data.

   Then the load error on unchecked `/` and `%` is lifted: they become
   `BinaryOp` and `ValueAssignOp` constructors with their typing, semantics and
   lowering.
2. **Row 1**: the twelve types, their literals and the `uint256` default,
   unary minus, checked arithmetic, the integer types' shifts, unchecked and
   bitwise operators and comparisons, and the API's canonical-argument check.

**Measured costs.**

- **Panics.** The lowering proofs relate each expression fault to its Core
  failure token through hypotheses such as `uninitialized : ∀ id location,
  faults (.uninitializedLocation location) (reasonAt id)`. That hypothesis
  appears about 300 times as a premise or field (405 occurrences counting the
  places it is supplied), in some of the 543 files under
  `Solcore/SourceSemantics/CoreLowering` that mention it. A panic needs the
  same for `.panic code`.
- **Row 1's values.** A new exact `Dynamic.Value` constructor reaches every
  proof that matches on values. 62 files under `Solcore/SourceSemantics` name
  the `integer` value constructor in a case, and the lowering's value
  representation would gain a matching case.

**Decide first when resuming.**

1. **Panic threading.** Thread `.panic` the way `uninitialized` is threaded,
   or generalize the fault-to-token hypothesis once, so that later fault
   reasons and panic codes need no new threading. Pick whichever is cheaper
   over unchecked division, row 1 and row 4.
2. **Row 1's values.** Compare an exact `Value` constructor with
   integer-typed values held as `.word`, where typed operations do the range
   checks, as upstream's Hull and lane E's Core reference do. Core needs no
   change either way. If both give upstream's results, prefer the one that
   touches fewer proofs, and record the choice and the reason here.

Theorem statements that change keep being listed in the lane's hand-over
note.
