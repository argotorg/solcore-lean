# Integer types, `unchecked` blocks and shifts

Updated: 2026-11-10. Module paths and file counts below predate the layout
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
- **Defaulting.** After the solve loop, upstream's
  `crates/hir-ty/src/infer/obligations.rs` defaults open literals to `uint256`
  in three passes, in this order:
  - `default_integer_literals_with_non_int_obligations`: a literal or numeric
    pattern whose variable occurs in an unresolved obligation of any class
    other than the builtin `Int`. Operators are such obligations (`Sub`,
    `Ord`, …), and so is a generic call's bound, such as a `Mark` bound.
  - `default_integer_literal_patterns`: every numeric pattern still open.
    It then checks the range of every `uint256` pattern, defaulted or
    declared (`check_integer_literal_pattern_range` in `pattern.rs`).
  - `default_root_integer_literals`: a literal whose variables all occur in
    the root body's own type.

  The obligations are then attempted again, so a bound with no `uint256`
  implementation is an error. Any other open literal is rejected as ambiguous
  (`SC0299`), for example `let y = 7;` when `y` is never used, or
  `let y = poly(7);` when `poly`'s only bound is `Int`, which the first pass
  skips (the uitest `crates/uitest/tests/fixtures/solver/poly_int_defaulting`).
  No literal defaults to `word`. The hir-ty tests in
  `crates/hir-ty/src/infer/tests/integer_defaulting.rs` cover the passes:
  `arithmetic_literals_default_to_canonical_uint256` for operators,
  `implicit_literal_pattern_uses_checked_default` and
  `uint256_numeric_patterns_reject_values_outside_the_range` for patterns,
  and `unconstrained_root_literal_uses_checked_type_without_name_lookup` for
  the root rule.
- **Compound assignments.** Upstream's parser rewrites `lhs op= rhs` into
  `lhs = lhs op rhs` before typing (`assign_stmt_kind` in
  `crates/parser/src/parse/stmt.rs`), "so type-class resolution and backend
  specialization stay identical". Only storage-index compounds keep an
  `AssignOp` (`crates/hir-ty/src/infer/stmt.rs`). So an open local target
  types as `x = x op e` does: the target and the operand share one type, which
  carries the operator's obligation and comes from a later use or else
  defaults to `uint256`. Lean types an open target the same way since step 7b,
  and still evaluates the place once.
- **Closures.** Upstream keeps a closure monomorphic: its parameters take their
  types from its calls, or their literals default to `uint256`. Lean
  generalizes a local lambda's type at its `let`, and a type variable that no
  literal or requirement holds is quantified. So since step 7b a compound
  assignment on an unannotated lambda parameter that nothing in the body types,
  as in `lam(acc, step) { acc += step; return acc; }`, is rejected at
  finalization (`compoundTargetNotSupported`), as `acc + step` already was
  (`operatorNotSupported`). A captured `Word` operand, a declared `acc: Word`,
  or a literal operand, which keeps the parameter monomorphic, types it. Like
  the `where`-clause gap below, the difference predates row 1.
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
  implemented](#unchecked-blocks-as-implemented).)
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
  (Superseded: integer-typed values are words; see [decisions on
  resuming](#decisions-on-resuming).)
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
  the operator's span. (Superseded: one reason per panic code; see [decisions
  on resuming](#decisions-on-resuming).)
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
  semantics, with primitive rules indexed by the operands' static types. It was
  rejected because every binary, unary and assignment evaluation rule, and
  every fault rule, would then need the operand's static type as a premise.
  Chosen on resuming, with typed operators in place of those premises; see
  [decisions on resuming](#decisions-on-resuming).
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
- **Typing.** Inference types a shift before any dispatch, and the dispatch
  map gives shifts no trait. Row 3 unified the value and then the amount with
  `word`, so an open literal operand was a `word` at once. Since row 1's step
  8d the value and the amount take their own types and an open literal waits
  ([row 1's
  shifts](#row-1s-shifts-on-the-twelve-types-the-amount-takes-its-own-type)).
- **Semantics.** `BinaryPrimitiveApplies` gains the two `word` shifts, and
  the compound forms apply them. A shift of any other value is an operand
  fault. Since step 8d the twelve types have their own shifts, binary and
  compound.
- **Lowering.** Shifts lower to `wordShl` and `wordShr`, and since step 8d,
  on the twelve types, through the type's shift bodies. A compound shift of
  a local uses a frontend copy of Core's compound-assignment shape, so Core is
  unchanged.
- **Integer targets.** The data-place lowering already refused compound
  assignment outside `word` and `integer`. It now also refuses shifts at
  `integer`, which typing never produces. The assignment profile shared by its
  theorems says the same: `T = .integer ∧ operator.isShift = false` (now
  `wordOnly`, below).
- **Legacy fragments.** The older strict-`word` evaluators leave the shifts
  out.

### Unchecked blocks as implemented

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
  `uncheckedSubtract`, `uncheckedMultiply`, `uncheckedDivide` and
  `uncheckedModulo`, which only the pass produces.
  - On `word` they type, run and lower as the checked operators.
  - On a declared type they dispatch to `UncheckedAdd`, `UncheckedSub`,
    `UncheckedMul`, `UncheckedDiv` and `UncheckedMod`.
  - On `integer` inference rejects them, since upstream defines no unchecked
    instance for it.
  - A literal operand was a `word` at once rather than deferred, while `word`
    was the only literal target left. Since row 1's step 8c it waits for its
    type as a checked operator's does, and finalization rejects one that
    becomes `integer` ([row 1's unchecked literal
    operands](#row-1s-unchecked-literal-operands-they-wait-and-never-take-integer)).
  - Since row 1's step 8a they are builtins on the twelve types too, where they
    wrap to the type's width ([row 1's unchecked
    arithmetic](#row-1s-unchecked-arithmetic-wrapped-to-the-types-width)).
- **Division and remainder.** `/`, `%`, `/=` and `%=` in a block panic with
  `0x12` on a zero divisor: see [panics as implemented](#panics-as-implemented).
  Until panics existed they were a load error.
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

### Panics as implemented

Unchecked `/` and `%` and their compound forms `/=` and `%=` panic with
`Panic(0x12)` on a zero divisor, as upstream does. Row 2 is complete.

**Frontend.**
- `SourceCorePanics` gives panic code `c` the Core reason `2^256 − 2^8 + c`,
  decodes a reason in that range back to its code (`code?`), and gives
  upstream's revert data, `0x4e487b71` followed by the code as a 32-byte word
  (`revertData`).
- `RuntimeError.panic code` is the diagnostic. `Table.diagnostic?` tries the
  table's rows first; a reason in the panic range then decodes to
  `.panic code` at the function's declaration site.
- Program preparation fails with `Error.panicRange` unless every reason that a
  fault-site table issues lies below the panic range. `Compiled.panicFree`
  records the check, and `Table.panic_diagnostic` proves that a checked table
  decodes every panic.
- A binary `/` or `%` in a block lowers to `panickingBody`: it compares the
  right operand with zero and fails with the panic's reason, or applies Core's
  `wordDiv` or `wordMod`. The legacy primitive lowerer, used only by tests,
  rejects the two operators.
- A compound `/=` or `%=` keeps Core's total modifier and checks the divisor in
  `guard`, after the setter has rebuilt the latest root and before the write.
  So a structural fault on the latest root still wins over the panic, as the
  source rule requires. Bit-not assignments pass `.equal`, whose modifier never
  checks.

**Source semantics.**
- `SemanticFault.panic code`. `BinaryPrimitivePanics` is the panicking case of
  a primitive application, and `BinaryPrimitiveApplies` has no zero divisor for
  the unchecked operators. `EvaluatesRightOperand.panicking` evaluates the right
  operand of a panicking operator.
- `AssignmentOperandsPanic` and `SourcePlaceAssignmentFaults.panic`: a compound
  assignment panics only after the latest root has been traversed, beside the
  `operands` rule.
- The staged semantics gains `Expression.binaryPanic`,
  `StatementsIn.assignBarePanic`, `ForItems.assignmentPanic` and
  `WriteFault.panic`, with their sized forms, erasure and preservation.

**Proofs.**
- `FunctionCalls.FaultTokens faults` holds the panic law: `faults (.panic code)
  (reason code)`. `RecursiveStageMeaning.FaultTokens` is its staged form.
  Theorems that need it take it as an instance argument. The decoded relation
  of an issued table has it through `issued_panicFree` and `tokens`, and a
  staged law gives the law of its semantic failures (`semanticTokens`).
- `CompositionJoins.panic` and the reached-fault paths give a panic its origin
  (`PrimitiveOrigin.panic`, `ExpressionPath.panic`).
- `DataPlaceGuard` relates `guard` to its write (`agreement`, `inv_sized`,
  `panic_of_selected`), and each place pipeline's success, fault and
  reflection theorems use it. The panic preservation theorems run the setter
  on the readable latest root (`setter_preserves`) and then fail at the check.

**Tests.** `Tests.SourceCoreUncheckedExecution` runs `/`, `%`, `/=` and `%=` in
a block, also at a mapping element, with and without a zero divisor, and
checks the panic's reason, its diagnostic and its revert data. Checked `/` and
`%` still give 0.

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

The unit is required. It was paused after row 3 and part of row 2 on
2026-11-04, and resumed on 2026-11-09 from main `99b37ca61`.

**Done.**
- Row 3, shifts: [shifts as implemented](#shifts-as-implemented).
- Row 2: [unchecked blocks as implemented](#unchecked-blocks-as-implemented),
  with division and remainder through [panics as
  implemented](#panics-as-implemented).

The public-API tests are `Tests.SourceCoreShiftExecution` and
`Tests.SourceCoreUncheckedExecution` in
`Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean`.

**Remaining.**

- **Row 1**: the twelve types, their literals and the `uint256` default,
  unary minus, checked arithmetic, the integer types' shifts, unchecked and
  bitwise operators and comparisons, and the API's canonical-argument check.
  Its checked `0x11` and `0x12` panics reuse the panic law, as row 4's array
  panics will.

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

**Decide first when resuming.** Both are decided in [decisions on
resuming](#decisions-on-resuming).

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

## Decisions on resuming

Made on 2026-11-09, before any code of the resumed unit.

### Panics: one generalized fault law, one reason per panic code

**Compared.**
- **Per-reason threading.** A hypothesis tying `.panic code` to its token
  would sit beside each `uninitialized` hypothesis. That is about 414
  declarations in 206 files under `Solcore/SourceSemantics/CoreLowering`, in
  a dozen quantifier shapes. Every call that passes `uninitialized` on would
  pass it too, and each of the 15 places that prove `uninitialized` would
  prove it as well. A later fault family would need the same again.
- **One generalized hypothesis.** A class of fault-to-token laws that hold at
  every site, threaded once.

**Chosen: the generalized hypothesis, as an instance argument.**
- `FaultTokens faults` is a `Prop` class. Its first law states that the fault
  `.panic code` fails with that code's reason.
- Theorems that need it take `[FaultTokens faults]`. Lean finds the instance
  at each call site from the caller's own binder, so the threading changes
  declarations and leaves calls alone. The binder goes beside each
  `uninitialized` hypothesis or section variable.
- One instance, for the decoded fault relation of the public results, serves
  the places that prove `uninitialized`.
- Row 1's checked arithmetic (`0x11`, `0x12`) and row 4's array panics
  (`0x31`, `0x32`, `0x41`) are panics too, so they need no more threading. A
  later family whose token does not depend on its site adds a field.
- Per-reason threading would cost the same declarations, plus every call site,
  and would cost them again for each later family.

**Panic reasons.**
- Panic code `c` fails with the Core reason `2^256 − 2^8 + c`, the same in
  every function. The design above planned one reason per site instead. A
  site's token would depend on that site's `reasonAt`, which varies by header
  and method under binders, so no single instance could carry it.
- Decoding tries the fault-site tables first and then the panic range, so the
  existing decoding theorems keep their statements.
- Program preparation checks that no table reason lies in the panic range.
  That check proves the panic law for the decoded relation.
- The panic diagnostic names the code and the function, not the operator's
  span. Upstream's revert data, `0x4e487b71` followed by the code, carries no
  site either, and it is computed from the reason alone.

### Row 1's values: integer-typed values are words

**Compared.**
- **An exact constructor.** `Dynamic.Value` gains a case holding the type and
  the exact integer, and every relation that matches values gains a case:
  - about 126 arms in 37 files under `Solcore/SourceSemantics/CoreLowering`,
    where each pipeline's value representation gains a constructor;
  - 13 arms in five files under `Solcore/SourceSemantics/Dynamic`;
  - the frontend's runtime value conversions and staged values.
- **Words with typed operations.** An integer-typed value is the `.word` that
  is its canonical two's complement representation. The typed operations
  check the ranges, as upstream's Hull and lane E's Core reference do.

**Chosen: words.** Both give upstream's results: a value's word is its
canonical representation, and each typed operation computes the exact result
and then wraps or panics as upstream does. Words touch fewer proofs:
- The twelve types have Core type `word`. The lowering's value representation
  already relates their values, because its word case takes any source type
  whose runtime type is `word`, so no representation gains a constructor.
- `ValueHasType` gains one case: a word that is canonical for an integer type.
  Matches on a fixed expected type, such as `.word`, are unaffected.
- The typed operations are operators, as the unchecked ones are, and
  inference selects them once the operands' types are known. The evaluation
  rules therefore keep their shape, and no rule takes an operand's static type
  as a premise. That removes the reason the alternative above was rejected.

### Row 1's operators: chosen from the operand's static type

Made on 2026-11-10, before row 1's operators. It revises the last point
above, which planned to rewrite each operator into a typed one once its
operands' types are known.

**Compared.**
- **Rewriting the typed IR after finalization.** The inference soundness
  proofs rest on one equation: the final source is the inferred node table
  under the final substitution (`Detail.finalize_typedSource`). About 70
  rewrites in about 25 inference files use it, as do the
  `TypingSourceExtends` premises of 11 more and the `finalize_*` lemmas. A
  rewritten node falsifies all of them, so a rewrite would need a transport of
  every typing judgment and resource, comparable in size to the substitution
  laws (`Internal/Substitution/StructuralLaws.lean`).
- **Choosing by the operand's static type.** The binary and unary rules look up
  their left (or only) operand's node, and apply the twelve types' operations
  when its type is one of them.

**Chosen: the static type.**
- About ten rule constructors gain the lookup: binary and unary evaluation and
  faults in the source semantics, the staged rules, and their sized forms.
  The inference proofs are unaffected.
- The other operand types keep their primitive relations, restricted to
  operands that are not of a fixed-width type, so the semantics stays
  deterministic.
- CoreLowering already chooses its lowering mode from the same type
  (`Tree.binary` and `BinaryProfile`).
- The operators that are Word's on canonical words (step 2 below) need no
  lookup: the word rules give their result at every one of the twelve types.
  Only the operators whose meaning differs (signed order, `~` on the narrower
  unsigned types, checked arithmetic) take the lookup, and only those restrict
  the primitive rules.
- Compound assignment needs no lookup, because its form holds the target's
  type.
- Preservation needs the looked-up type to be the operand's typed type where
  the primitive result would leave the type's range: Word's `~` on a `uint8`
  word, and the wrapping `+ - *`. The typing names the operand's node, and the
  source's unique node occurrences make the lookup find it
  (`Dynamic.operandType?_of_typing`). The signed orderings give a Boolean either
  way, so the binary rules need this only from checked arithmetic on.

### Row 1's runtime types: the shape erases the twelve types

Made on 2026-11-10, during row 1's types step. It corrects the second point of
"Row 1's values" above: there are three runtime-type views, and the lowering's
own view keeps the twelve types.

- **The shape views erase them.** `Dynamic.runtimeType` and
  `SourceTypedRuntime.runtimeType` map each of the twelve types to `word`, as
  they erase `comptime`. These views only compare value shapes: the mapping
  key guard (`ValueRuntimeTypeMatches`), the shared runtime's `Value.type?`
  checks, and the result check of the unified API. A `uint8` value is a word,
  so it passes them.
- **The metadata view keeps them.** `SourceCoreRawMetadata.runtimeType` is
  unchanged. The lowering's operator profiles test `runtimeType leaf = .word`,
  and compound assignment and bit-not on places choose word operations from
  that test. Erasing the twelve types there would apply wrapping word
  operations to them.
- **So the representations gain a case.** The value relations keyed by the
  metadata view (`CompatiblePayload.ValueRep`, `DataPayload.ValueRep`, the
  public input and output shapes, the defaults) each gain a `fixed` case:
  the word itself, canonical for the type where the codec must re-encode it.
  The agreement lemmas now say that the shape view is the metadata view
  followed by the erasure.
- **Inputs check the range.** Every encoder (compatible, indexed session,
  general functions, data values) and the shared runtime's input validator
  reject a word that is not canonical for its type. The validator matches on
  the type with only `comptime` erased (`unstagedType`), so nested values are
  checked too.
- **The legacy lowering rejects them.** `SourceCoreElaboration.lowerType`
  rejects the twelve types, as it rejects `integer`. Its local-cell proofs
  rely on each Core type having one source type. The catalog projections,
  which the public pipelines use, lower the twelve types to `word`.

### Row 1's compound assignments: checked at the guard, outside the meaning proofs

Made on 2026-11-10, during step 3d.

- **Typing.** Compound assignment takes the target's type where its binary
  operator is a builtin there (`Detail.compoundOperandType`): `+= -= *=`
  (checked) and `&= |= ^=` (Word's on canonical words) at the twelve types. So
  `&= |= ^=` come with this step. The other compound forms stay Word's until
  their binary operators are builtins at the twelve types: `/=` and `%=` with
  step 4, the unchecked forms with step 8b and the shifts with step 8d.
  In-place `~` stays Word's.
- **Semantics.** The value-assignment rules apply `CompoundAssignmentApplies`
  at the target's static type: `AssignmentValueApplies` where the meaning is
  Word's, Integer's or plain assignment, and checked `+= -= *=` by
  `FixedBinaryApplies` at a fixed-width target. `AssignmentOperandsPanic` takes
  the target's type, so checked arithmetic outside the range panics with
  `Panic(0x11)`, after the latest root has been traversed, as `/=` and `%=` do.
- **Lowering.** The place lowering chooses the modifier from the target's
  static type (`assignmentModifier`). Checked `+= -= *=` compute Word's
  operation, which in range is the exact result's word, and `guard` checks the
  exact result, read from the snapshot and the right-hand side, against the
  type's range after the setter (`Check.range`). So a structural fault on the
  latest root still wins over the panic. `&= |= ^=` keep Word's modifier.
  `CompatibleBareAssignment.of_lower` states the new choice.
- **Fault sites.** The assignment fault-site table gives a fixed-width target
  its own site (`SourceCoreAssignmentFaultSites.operandTarget`), so an absent
  operand of a compound assignment at the twelve types fails with its own
  `invalidAssignmentOperands` diagnostic, naming the target's type, as at
  Word. No existing table changes: these assignments did not type before.
- **Outside the meaning proofs.** The meaning proofs' operator profiles
  (`operator = .equal ∨ T = .word ∨ T = .integer ∧ operator.wordOnly = false`,
  on the metadata view, which keeps the twelve types) exclude fixed-width
  compound targets, as the receipts' `sourceProfile`
  (`operator = .equal ∨ T = .word`) excludes Integer targets. So these
  assignments are compiled but not covered. Inside the profiles,
  `assignmentModifier_plain` turns the compiler's choice back into
  `binaryOperator`'s, and `CompoundAssignmentApplies.eq_of_plain` the relation
  back into `AssignmentValueApplies`.
- **Bringing them in** would take:
  - a fixed disjunct in the profiles, `T = .fixed t ∧
    FixedCompoundAssignmentOperator operator`, and in the receipts'
    `sourceProfile`;
  - a checked case in `DataPlaceModifier`'s modifier lemmas: in range, Word's
    `+ - *` is the exact result's word (congruence modulo `2^256`), and
    `SourceCorePrimitive.checkedInRange` is `Dynamic.FixedInRange` of
    `checkedResult` by definition;
  - the range check in the place pipelines, through `guard_inRange`,
    `guard_overflow` and `guard_range_inv`, which read the snapshot, the
    guard's fourth binder (`RangePasses`);
  - for `&= |= ^=`, the canonical words of the representation
    (`ValueRep.fixed`) in the modifier's result.

### Row 1's division: before the literals

Made on 2026-11-10, when step 4 (then the literals) began. The integrator
chose to move checked `/ %` ahead of the literals.

- **Why the order changed.** An operator whose operand is an open literal is
  deferred and takes the literal's type. In a program without the `Div` and
  `Mod` traits, `let a = 6 / 2; let b: uint8 = a;` defers `/`, and the second
  `let` gives it `uint8`. With literals at the twelve types and no
  fixed-width rule for `/`, inference would accept the program, and its
  soundness could not be proved for that node. The compilation plan rejected
  such a node, so nothing would have been miscompiled. Every other operator
  that can be deferred already had its rule; shifts and unchecked operators
  never defer.
- **The alternative.** Rejecting a deferred `/ %` whose type ends fixed would
  have kept the order. It needs the operator's own node after finalization in
  the nested soundness proofs, which carry none, and the `/ %` step would have
  removed it again.
- **Semantics.** By a nonzero divisor, `/` gives the quotient rounded toward
  zero (`Int.tdiv`) and `%` the remainder with the dividend's sign
  (`Int.tmod`), as `Dynamic.divisionResult`, when the result lies in the type's
  range (`FixedBinaryApplies.division`). A zero divisor panics with
  `Panic(0x12)` (`FixedBinaryPanics.divisionByZero`), and a result outside the
  range with `Panic(0x11)` (`divisionOverflow`). Only `MIN / -1` on a signed
  type leaves the range; `MIN % -1` is 0. The typing is
  `BinaryOperatorHasType.fixedDivision` (`FixedCheckedDivision`).
- **Lowering.** Core's `integerDiv` and `integerMod` are Euclidean, as the `/`
  and `%` of Lean's `Int` are. So the division body
  (`SourceCorePrimitive.divisionBody`) tests the divisor word against zero
  first, reads both words as Core Integers (`fixedInteger`), divides their
  magnitudes with Core's operations and restores the sign
  (`truncatedDivision`), then checks the type's range and converts back, as
  checked `+ - *` do. The compiler's choice is `checkedArithmetic`, now with
  `/ %`, so they share the checked mode (`Mode.checked`,
  `BinaryProfile.fixedDivision`) inside the meaning proofs.
- **Compound `/= %=`.** They take the target's type and are checked
  (`FixedCheckedCompound`). The modifier's operation is Word's `wordDiv` and
  `wordMod`, or `wordSdiv` and `wordSmod` on the signed types
  (`checkedWordOperation`); by a nonzero divisor, in range, that is the exact
  result's word. For `/ %` the guard's range check tests the divisor against
  zero first (`DivisorPasses`, `guard_rangeZero`), after the setter, so a
  structural fault on the latest root still wins over either panic. Like 3d's
  targets they are compiled but outside the meaning proofs' profiles.

### Row 1's literals: checked by inference and the compiler

Made on 2026-11-10, during step 5.

- **Typing.**
  - A literal whose type resolves to one of the twelve types takes that type
    (`Ty.IntegerLiteralCarrier`, `Detail.supportedIntegerLiteralTarget`).
  - An open literal still defaults to `word`; step 7 changes that.
  - Each type has builtin `Int` evidence (`BuiltinImplId.intFixed`,
    `ProgramSignatures.builtinIntFixedRule`).
  - An operator that waited on an open literal takes the literal's later
    type and that type's rule (`binaryFixed_hasType_of_deferred`). So
    `let a = 6 / 2; let b: uint8 = a;` divides at `uint8`. And
    `let a = 200 + 100; let b: uint8 = a;` panics with `Panic(0x11)`,
    since each operand fits but the sum does not.
- **The range.** Two checks reject a literal above its type's greatest value
  (`FixedInteger.maxNat`):
  - Inference's finalization checks every literal node against its final type
    (`Detail.literalFitsTarget`, `literalNodesFit`). Its diagnostic names the
    type and the value (`Error.integerLiteralOutOfRange`), and
    `finalize_typedSource_integerLiteral_fits` states the check.
  - The compiler checks the range again (`validateFixedIntegerLiteral`,
    `FixedIntegerLiteralCertificate.fits`).

  The signed types get nonnegative literals only, until step 6 brings unary
  minus.
- **Semantics.**
  - The static rule `IntegerLiteralValid.fixed` needs the type and the
    evidence, not the range. The nested inference proofs carry the literal
    origins but no literal node, and a range premise would need such a node at
    about 200 sites.
  - The construction `ResolvedIntegerLiteralConstructs.fixed` needs the
    range, so the literal's word is canonical. Preservation uses it.
- **Lowering.**
  - At one of the twelve types (`Ty.fixedInteger?`), the compiler's numeric
    branch emits the literal's word.
  - The meaning proofs cover it with `Literal.resolvedFixed`,
    `NumericLiteralEvidenceReceipts.fixed` and `literalImplementation`.
  - Numeric patterns at the twelve types stay rejected.

### Row 1's unary minus: folded or read as `0 - e` before inference

Made on 2026-11-11, during step 6.

- **Parser.** `UnaryOp.negate` is a prefix `-`, read by the prefix-unary layer
  with `!` and `~`.
- **No `negate` reaches inference.** `Syntax.Unchecked.mark`, which every
  loaded file goes through, removes each one:
  - A `-` over a numeric literal, through groups and repeated, folds into the
    literal: its spelling gains or loses a leading `-`, and the literal spans
    the negation. So `-128`, `(-128)`, `-(128)` and `- -5` are literals.
  - Any other `-e` reads as `0 - e`, as upstream reads it: `subtract`, or
    `uncheckedSubtract` in a block, with the `0` and the operator at the `-`.

  So the checked `0 - a` of step 3c gives `-a` on the twelve types, with
  `Panic(0x11)` for `MIN` and any nonzero unsigned value, inside the meaning
  proofs. On `word` it wraps. A declared type is rejected: the `0` would need
  `Int` of that type, which is builtin. Inference still rejects a `negate`
  (`operatorNotSupported`), so that its soundness holds for every syntax tree,
  and the primitive lowering refuses one.
- **Negative literals.**
  - The sign is the spelling's (`Frontend.isNegativeLiteral`), and the
    resolution's raw value is the magnitude (`literalMagnitude?`,
    `NegativeLiteralDenotes`).
  - Finalization checks the range with the sign (`signedLiteralFitsTarget`):
    at a fixed-width type the magnitude is at most that of the least value
    (`FixedInteger.minMagnitude`), so only `-0` fits an unsigned type.
    `Error.integerLiteralOutOfRange` names the negative value, and the compiler
    checks the range again.
  - At `word` a negative literal wraps (`negativeLiteralWord`), so
    `let w: word = -1` is `2^256 - 1`; at `integer` it is exact; at a
    fixed-width type it is the canonical word in two's complement.
  - Semantics: `IntegerLiteralValid.negative`, and the constructions
    `negativeWord`, `negativeInteger` and `negativeFixed`.
  - Lowering: the numeric branch chooses by the sign
    (`validateNegativeWordIntegerLiteral`, `validateNegativeNativeIntegerLiteral`,
    `validateNegativeFixedIntegerLiteral`). The meaning proofs cover them with
    `Literal.resolvedNegativeWord`, `resolvedNegativeInteger` and
    `resolvedNegativeFixed`.
- **Choices.**
  - On `integer`, a negated literal is exact, and `-x` is `0 - x`, so it is
    staged as integer subtraction is: typed next to the literal `0` and
    rejected by Core lowering outside staged code.
  - In an unchecked block, `-x` is unchecked `0 - x`: it wraps on `word` and,
    since step 8a, on the twelve types, where `-MIN` is `MIN` and `-x` on
    `uintN` is `2^N - x` for a nonzero `x`. `integer` rejects it as it rejects
    the block's other arithmetic. Negated literals fold in a block too.
  - An open negative literal keeps the `word` default until step 7, so
    `let k = -1;` is `2^256 - 1`. Upstream rejects it (`SC0411`) through the
    `uint256` default, which step 7 brings.

### Row 1's `uint256` default: chosen by the literal's uses

Made on 2026-11-11, during step 7.

- **Defaulting.** After inference, a literal whose type is still a variable
  defaults to `uint256` (`Detail.defaultIntegerLiteralTarget`,
  `literalDefaultsToUint256`) when:
  - its type occurs in an operand type of a unary or binary node
    (`operatorMentions`): a builtin operator deferred on an open literal, or a
    comparison, so `7 == 7` and an unused `7 + 1` are `uint256`;
  - it occurs in a pending requirement other than its own builtin `Int`
    (`requirementMentions`), which is then solved at `uint256`;
  - or its spelling is negative. The `-` is an operator until it folds into
    the literal, so `let k = -1;` defaults and then fails `uint256`'s range
    (`Error.integerLiteralOutOfRange`), as upstream rejects it with `SC0411`
    rather than as ambiguous.

  Any other open literal is rejected as ambiguous
  (`Error.ambiguousIntegerLiteral`, upstream's `SC0299`): `let y = 7;` unused,
  `let y = 7; let z = y;`, `sc_id(7)` with an unused result, and
  `lam () { return 7; }` never called. No literal defaults to `word` any more.
- **Upstream's three passes in Lean.**
  - The non-`Int` obligation pass is `operatorMentions` and
    `requirementMentions`. Lean's builtin operators are deferred nodes, not
    requirements, so they need their own test.
  - The pattern pass is `defaultIntegerPatternTarget`, and the range check is
    `validateIntegerPatternTarget` (below).
  - The root pass has no counterpart for named functions: their parameters
    are always typed, and a missing `returns` clause is unit, so a function's
    root type holds no variable. The one root whose type can be open is
    `SourceInference.inferExpression`, which checks an expression on its own.
    A literal that only that type constrains, such as a lone `7`, is rejected
    as ambiguous there, where upstream's root pass would give it `uint256`.
    Nothing in the repository calls `inferExpression`.
  - The negative-spelling case has no counterpart upstream, which reaches the
    same `SC0411` through the `-`.
- **Numeric patterns.**
  - An open pattern defaults to `uint256` (`defaultIntegerPatternTarget`).
    Patterns default before literals, so a `match` on an open literal makes
    the literal `uint256` too.
  - Patterns are admitted on `word`, `integer` and `uint256`
    (`Ty.IntegerPatternCarrier`, `Detail.supportedIntegerPatternTarget`). The
    other eleven types keep rejecting them (`Error.nonNumericPatternType`), as
    upstream does: its `numeric_literal_pattern_expected` admits only `word`,
    `integer`, `uint256` and an open type, and `infer_lit_pat` reports a
    mismatch otherwise (`crates/hir-ty/src/infer/pattern.rs` at the pin).
  - At `uint256` a pattern compares the scrutinee's word with the literal's.
    Both pattern compilers validate it with `validateFixedIntegerLiteral`,
    and the meaning proofs cover it (`LiteralCode.uint256`).
  - The range is checked twice, as for literals. Finalization checks every
    `uint256` pattern, defaulted or declared, as upstream does
    (`IntegerPatternOrigin.rawValue`, `Error.integerPatternOutOfRange`, which
    names the type and the value), and the compiler's validator checks it
    again.
- **`where` clauses.** A `where` clause cannot name the builtin `Int`: Lean
  reports `unknownTrait "Int"`, and a declared `trait Int` is an ordinary
  source trait. So upstream's `poly_int_defaulting` is rejected at its
  signature in Lean. This frontend gap predates row 1. Without the bound,
  `poly(7)` with an unused result is ambiguous, as upstream has it.
- **Shifts and unchecked operators** made their literal operands `word` at
  once until step 8 ([shifts as implemented](#shifts-as-implemented),
  [unchecked blocks as implemented](#unchecked-blocks-as-implemented)), so
  `1 << 3` was a `word`. On the same words, Word's shifts and wrapping
  arithmetic give what `uint256`'s would, so only the typing differed: such a
  literal could not then flow to `uint256`. Their literals now wait and
  default as the design says: the unchecked operators' since step 8c
  ([row 1's unchecked literal
  operands](#row-1s-unchecked-literal-operands-they-wait-and-never-take-integer))
  and the shifts' since step 8d ([row 1's
  shifts](#row-1s-shifts-on-the-twelve-types-the-amount-takes-its-own-type)).
- **Compound assignments on an open target (step 7b).** `+= -= *= /= %= &=
  |= ^=` (`compoundTakesTargetType`) on a target whose type is still open take
  that open type as their operand's type (`compoundOperandType`), so the
  target and the operand share one type, as upstream's rewrite to
  `x = x op e` types them. The compound counts as an operator use for the
  default (`assignmentMentions`, part of `operatorMentions`). So
  `let x = 0; x -= 1;` is `uint256` and panics with `0x11`, as `x = x - 1`
  does, and a later use can give the type instead:
  `let x = 200; x += 56; return x;` from a function returning `uint8` panics
  too. Finalization then checks every assignment's resolved target type
  (`validateAssignmentTargets`, `compoundTargetFits`): `word`, or for these
  operators one of the twelve types. A target that becomes `integer`, or one
  that nothing fixes, is rejected with `Error.compoundTargetNotSupported`,
  which names the assigned value, the operator and the type. Only the typing
  changes: the place is still evaluated once, and the compound semantics stay
  as they are. Compound shifts and unchecked compounds still make an open
  target `word` at once, until step 8. In the proofs the check reaches the
  statement rules through `FinalInferenceResources.assignment_targets_fit`
  (`SourceAssignmentTargetsFit`), and the `for` items get it from the
  enclosing loop. A lambda parameter that nothing types is the one new
  rejection outside `integer`; see the upstream section's "Closures".
- **Gaps left for step 8.** Two older paths take only `word` and `integer`,
  as since step 1, so a value that now defaults to `uint256` fails there:
  - The monomorphic scalar and function profile
    (`SourceCoreFunctions.lowerExpressionWithReasons`, also behind
    `SourceCoreFunctionEntry`) projects only those types and rejects
    fixed-width literals, so a `uint256` value or pattern fails with
    `typeProjection`.
  - `SourceProgramExecution`'s direct linking (`SourceCoreDirectLinking`)
    rejects a `uint256` binder with `unsupportedType`.

  The public compiler (`SourceCoreExecution`) uses neither path, and its
  general and compatible paths compile `uint256` values and matches.
  Extending the scalar profile would reach its Word and Integer meaning
  proofs, so step 7 types the scrutinees and literals of the tests that use
  these paths `Word` instead.
- **Consequences**, as [consequences for existing
  programs](#consequences-for-existing-programs) expects: arithmetic on a
  defaulted literal is checked at `uint256`, so `2^256 - 1 + 1 == 0` panics
  with `0x11` where it was `true` at `word`; unconstrained literals are
  rejected; and the tests that relied on the `word` default change, as the
  hand-over note lists.

### Row 1's unchecked arithmetic: wrapped to the type's width

Made on 2026-11-12, during step 8a.

- **Typing.** In an `unchecked` block, `+ - * / %` on one of the twelve types,
  with both operands of that type, are builtins without requirements
  (`Detail.fixedBinaryOperator`, `BinaryOperatorHasType.fixedUnchecked`), as
  upstream's `UncheckedAdd` … `UncheckedMod` instances for the twelve types
  are. A literal operand takes the other operand's type, on either side. Two
  open literal operands wait for their type since step 8c ([row 1's unchecked
  literal operands](#row-1s-unchecked-literal-operands-they-wait-and-never-take-integer)).
  `integer` takes none of them, as before.
- **Meaning.** The exact result of the operands' values wrapped to the type's
  width (`Dynamic.fixedWrap`: the residue modulo `2^N`, read in two's
  complement on a signed type), as a canonical word
  (`FixedBinaryApplies.unchecked` and `uncheckedDivision`). `/` rounds toward
  zero and `%` takes the dividend's sign, as checked `/ %` do, so `MIN / -1`
  wraps to `MIN` and `MIN % -1` is 0. A zero divisor panics with `0x12` by
  `BinaryPrimitivePanics`, which applies at any operand type. The five
  operators are in `FixedBinaryOwn` on all twelve types, `uint256` included,
  where the wrapped result is Word's, so the evaluation rules choose the
  meaning from the operands' static type alone, as for checked arithmetic.
  They are not all strict: unchecked `/ %` may panic, so
  `FixedBinaryApplies.strict` became `evaluatesBoth` (strict, or
  `PanickingBinaryOperator`).
- **Lowering.** `BinaryLowering.checked type` is the type's own arithmetic and
  covers the unchecked operators too (`checkedArithmetic`, `checkedBinary`):
  both operands, then `uncheckedBody` (the exact result as a Core Integer,
  wrapped by `fixedWrapInteger`, then `integerToWord`) or
  `uncheckedDivisionBody` (the zero test, `truncatedDivision`, the wrap). The
  meaning proofs cover both (`BinaryProfile.fixedUnchecked` and
  `fixedUncheckedDivision`).
- **Compound forms.** Unchecked `+= -= *= /= %=` came with step 8b
  ([row 1's unchecked compound
  assignments](#row-1s-unchecked-compound-assignments-the-wrap-belongs-to-the-leaf)).

### Row 1's unchecked compound assignments: the wrap belongs to the leaf

Made on 2026-11-12, during step 8b.

- **Typing.** `+= -= *= /= %=` in an `unchecked` block take a fixed-width
  target's type, as the checked forms do (`Detail.compoundOperandConstructor`,
  `FixedCompoundAssignmentOperator`), and an open target's own type
  (`compoundTakesTargetType`), so step 7b's default and finalization check
  cover them: an open target becomes `uint256` unless a later use types it,
  and one that becomes `integer` is rejected with
  `compoundTargetNotSupported`.
- **Semantics.** `CompoundAssignmentApplies.uncheckedAdd` …
  `uncheckedModulo` apply `FixedBinaryApplies` of the binary operator at a
  fixed-width target, so the result wraps as step 8a's binary forms do. A zero
  divisor panics with `0x12` by the primitive panic, as at `word`.
  `FixedCheckedCompound`, the forms whose meaning at a fixed-width target is
  the type's own, gains the unchecked forms and keeps its name, so the meaning
  proofs' profiles exclude them as they exclude step 3d's.
- **Lowering.** `checkedCompound` also returns the unchecked forms at a
  fixed-width target, and `assignmentModifier` gives them Word's operation
  (`checkedWordOperation`: `wordAdd`, `wordSub`, `wordMul`, and `wordDiv` and
  `wordMod`, or `wordSdiv` and `wordSmod` on the signed types) with
  `fixedCheck`: no check for `+= -= *=`, the zero test for `/= %=`, and the
  range check for the checked forms as before. Word's operation keeps the low
  `N` bits of the exact result, so the modified leaf is wrapped before the
  setter writes it: `modified` and `execute` take a new optional last argument
  `wrap` (`none` by default), and `wrapLeaf` masks it (`wordAnd`) on an
  unsigned type or sign-extends it (`wordSignExtend`) on a signed one. `lower`
  passes `placeWrap`: the target's type for the unchecked forms at a
  fixed-width target, `none` otherwise and for in-place `~`.
  `CompatibleBareAssignment.of_lower` states the new choice: its emitted
  `execute` takes `placeWrap`.
- **Rejected: the wrap in the guard's `Check`.** A `Check` constructor that
  wraps would keep `of_lower`'s text, but the wrap belongs to the leaf the
  setter writes, while `Check` is the post-setter guard that decides a panic.
  It would also change `guard_inv`, `inv_sized` and `Passes` and about 40 of
  their callers, with no gain in a public statement.
- **Proofs.** Statements that write `execute …` or `modified …` without the
  argument elaborate with `none` and keep their text. The lemmas over every
  compiled assignment take it: the compiler receipts, the `of_lower`
  inversions, the layout and helper typing inversions, and the present-RHS
  typing (`wrapLeaf_typed`). Under the meaning proofs' profiles
  `placeWrap_plain` gives `none`, next to `assignmentModifier_plain`.
  Fixed-width compound targets stay outside the meaning proofs, as step 3d's
  are.

### Row 1's unchecked literal operands: they wait, and never take `integer`

Made on 2026-11-12, during step 8c.

- **Typing.** An unchecked operator with an open literal operand waits for the
  literal's type, as a checked operator does, instead of making it a `word` at
  once: `inferBinaryOperator` has no unchecked branch any more, and
  `Detail.binaryDefers` lets the operator wait unless its operand is already
  `integer`. The literal then takes its type from a later use or the return
  type, or defaults to `uint256` as an operator use ([row 1's `uint256`
  default](#row-1s-uint256-default-chosen-by-the-literals-uses)), so
  `unchecked { let a = 200 + 100; let b: uint8 = a; return b; }` is 44, and
  `let a = 0 - 1;` in a block wraps at `uint256`. On an `integer` operand the
  operator never waits: it dispatches as on any closed type, to a program's
  own `UncheckedAdd` … `UncheckedMod`, or is rejected with
  `operatorNotSupported`, as before.
- **Finalization.** An operator that waited owns no requirement besides its
  coercions'. Once the defaults are in, one whose left operand became
  `integer` is rejected with `operatorNotSupported` and its trait's name
  (`"UncheckedAdd"` …), the diagnostic of an `integer` operand, in step 7b's
  pass over the nodes (`Detail.validateUncheckedOperand`), so
  `unchecked { let a = 1 + 2; let b: integer = a; }` is rejected.
- **Proofs.** `BinaryOperatorInferenceCase.uncheckedFallback` is the waiting
  case. At `word` and the twelve types it types as the builtin does, and at
  `integer` the finalization fact
  (`FinalInferenceResources.unchecked_operands_fit`) excludes it. The binary
  typing theorems take that fact as `uncheckedFits`, and their callers read it
  at the operator's node in the finalized source. A call may attach coercions
  to that node later, so `ExpressionOperatorSiteRetainedAt` now keeps any own
  requirement prefix, the empty one included, and the node's form.

### Row 1's shifts on the twelve types: the amount takes its own type

Made on 2026-11-12, during step 8d.

- **Typing.** A shift's value is `word` or one of the twelve types, and the
  result takes the value's type. The amount is typed on its own: `word` or an
  unsigned type (`ShiftAmountType`), the types of upstream's `ShiftAmount`
  instances, so `uint8 << uint256` and `int8 >> uint8` are accepted.
  `BinaryOperatorHasType.wordShift` takes any such amount, and `fixedShift`
  is the rule on the twelve types. `ExpressionFormHasRawType.binary` takes
  the two operand types separately (`leftType`, `rightType`); every other
  operator rule keeps one operand type, and
  `BinaryOperatorHasType.result_type_admissible_of_left` gives the result's
  admissibility from the left operand's. User trait shifts are out of scope:
  `BinaryOperatorHasType.trait` keeps one operand type.
- **Open literals.** The shift's branch of `inferBinaryOperator` no longer
  unifies the operands with `word`: it returns the value's type and no
  requirement, so a literal operand waits, as upstream's obligations do. A
  literal value takes the type of the result's use (`return 1 << s;` at
  `uint8`), and an open literal value or amount defaults to `uint256` as an
  operator use ([row 1's `uint256`
  default](#row-1s-uint256-default-chosen-by-the-literals-uses)). So
  `let a = 1 << 256;` is 0 at `uint256`, `x << 300` is 0 at `uint8`, and a
  negative literal amount (`x << -1`) defaults to `uint256` and is out of its
  range, as upstream has it.
- **Finalization.** Once the defaults are in, `Detail.validateShiftOperands`,
  in step 7b's pass over the nodes, rejects a shift whose value is not `word`
  or one of the twelve types, or whose amount is not `word` or unsigned, with
  `operatorNotSupported`, the shift's function (`"shl"`, `"shr"`) and the
  type. This covers a signed amount, as upstream's `shift_by_signed_amount`
  fixture has it, an `integer` or `Bool` operand, and a lambda parameter that
  only a shift's value types, which row 3 made `word`: local generalization
  leaves its type open, as for step 7b's compound targets.
- **Semantics.** `FixedBinaryApplies.shiftLeft` is Word's shift read at the
  type: the low `N` bits, sign-extended from bit `N - 1` on `intN`.
  `shiftRight` is Word's shift on the unsigned types and the arithmetic one
  (`Word.shiftArithmeticRight`) on the signed ones. An amount of at least the
  width gives 0, or -1 for a negative value's `>>`, and no shift panics. The
  results stay canonical (`Dynamic.fixed_canonical_shiftRight`,
  `fixedWrap_inRange`).
- **Lowering.** On the twelve types `checkedBinary` binds both operands and
  runs `shiftLeftBody` (Core's `wordShl`, then the type's wrap) or
  `shiftRightBody` (`wordSar` on the signed types, `wordShr` otherwise). The
  compiler's plan check of a builtin binary node asked for two operands of
  one type, which `w << 3` no longer has; it now takes a shift's value and
  amount as finalization does.
- **Proofs.** `BinaryOperatorInferenceCase.shift` is a shift's inference
  case. The binary typing theorems take `shiftFits` from the finalization fact
  `FinalInferenceResources.shift_operands_fit` (`SourceShiftOperandsFit`),
  which their callers read at the operator's node, as for step 8c's
  `uncheckedFits`. The meaning proofs' binary node takes the right operand's
  own type, and `BinaryProfile` gains `wordShift` (mode `word`) and
  `fixedShift` (mode `checked`). So a Word shift by a literal amount, now a
  `uint256`, stays in the closed subset, and the fixed-width shifts join it,
  as step 8a's unchecked arithmetic did.
- **Compound shifts**, the step's second part. `<<=` and `>>=` type as
  upstream's rewrite of `x <<= n` to `x = x << n` types them: the target is
  the shift's value and keeps its type, `word` or one of the twelve types
  (`ShiftValueType`), and the amount is typed on its own, at `word` or an
  unsigned type. One rule types them, `SourceAssignmentHasType.shiftCompound`;
  `WordCompoundAssignmentOperator` no longer lists them, so no compound
  assignment has two rules. An open target takes its own type and waits, as
  step 7b's compound targets do, and its mention and the amount's count for
  the `uint256` default. Finalization admits a `word` or fixed-width shift
  target (`compoundTargetFits`) and rejects an amount of another type with
  `operatorNotSupported` and `"shl"` or `"shr"` (`Detail.validateShiftAmount`),
  which `FinalInferenceResources.shift_amounts_fit` records for the proofs.
  At a fixed-width target the meaning is the binary shift's
  (`CompoundAssignmentApplies.shiftLeft`, `shiftRight`), written back through
  step 8b's leaf wrap: `wordShl` then the type's wrap for `<<=`, `wordSar` or
  `wordShr` for `>>=`, and no check. Fixed-width targets stay outside the
  meaning proofs (`FixedCheckedCompound` lists the shifts, so `targetPlain`
  excludes them), as step 3d's compound targets do. A `Word` target stays in
  them with an amount of its own type: the statement trees take the
  right-hand side through `AssignedOperandTyped`, and the assignment head's
  `rightView` is an `AssignedRhsView`, at the leaf's runtime type or, for a
  shift, an amount whose word the shift reads (`AssignedRhsView.rep`, as
  `amount_word_fields` reads a binary shift's). The statement checkers that
  compared the right-hand side's type with the target's decide the view
  instead (`AssignedRhsView.decide?`). So `w <<= 3`, whose amount is a
  `uint256` now, `w <<= n` by a `Word` and `w >>= n` by a `uint8` pass the
  statement shape check.

### Row 1's in-place `~`: the target keeps its type

Made on 2026-11-12, during step 9a.

- **Typing.**
  - Upstream's parser rewrites `x ~=` to `x = ~x`
    (`crates/parser/src/parse/stmt.rs:83-97`). So the target keeps its own type and takes that
    type's `BitNot` instance:
    - masked at `uint8` … `uint128` (`std/unsigned.sol:69-73` and the other widths);
    - sign-extended at `int8` … `int128` (`std/signed.sol:79-83` and the others);
    - Word's at `word`, `uint256` and `int256` (`std/std.sol:948-952`, `std/std.sol:1074-1078`,
      `std/signed.sol:951-955`).
  - Inference unifies the target with `Detail.bitNotTargetType`. An open target keeps its type and
    waits, as step 7b's compound targets do. A fixed-width type is its own target type, and any
    other type is `word`'s, as before.
  - The target counts as an operator use for the `uint256` default (`Detail.bitNotMentions`, part
    of `operatorMentions`). So `let x = 0; x ~=;` is `uint256`, and a later use can give the target
    another type.
- **Finalization.**
  - Once the defaults are in, `Detail.validateBitNotTarget`, in step 7b's pass over the nodes,
    rejects a target whose type has no builtin `~` (`Detail.bitNotTargetFits`). The diagnostic is
    `operatorNotSupported` with the trait's name, `"BitNot"`, and the type, as steps 8c and 8d name
    an operator's trait or function.
  - Upstream defines no `BitNot` on `integer` or `bool` (`integer`'s instances are
    `std/std.sol:954-978`). Its solver reports the unsolved constraint (`SC0207`,
    `crates/hir-ty/src/infer/diagnostics.rs:176`). A closed target of such a type keeps Lean's
    unification error.
  - `FinalInferenceResources.assignment_targets_fit` records the check: `StatementAssignmentTargetsFit`
    and `ForItemAssignmentTargetFits` gain the bit-not forms (`BitNotTargetFits`).
  - A lambda parameter that only an in-place `~` types stays open after local generalization. So
    `lam(x) { x ~=; return x; }` is rejected, as step 7b's and step 8d's lambda cases are.
- **Static semantics.** `SourceBitNotAssignmentValid` types the target at a `BitNotTargetType`:
  `word` or one of the twelve types. The step's first part admitted only the types on which `~` is
  Word's (`FixedWordBitNot`), with no change to the meaning; the second part admits the rest.
- **Meaning.**
  - The rules update the place with `BitNotAssignmentApplies` at the target's static type, as
    compound assignment uses `CompoundAssignmentApplies`.
  - On `word`, `uint256`, the signed types and `integer` that is Word's or Integer's `~` on the
    snapshot (`BitNotSnapshot`). On `uint8` … `uint128` it is the narrow `~` of step 3b
    (`FixedUnaryApplies`): Word's `~` masked to the low `N` bits.
  - `eq_of_plain` and `eq_word` give back `BitNotSnapshot` where no narrow type is involved.
  - The results stay canonical (`fixed_canonical_bitNot`, `fixed_canonical_narrowBitNot`,
    `BitNotAssignmentApplies.preserves_target`).
  - The sized copy (`Foundations/SourceExecutionSize`) and the staged semantics' `~=` rules take
    the same relation.
- **Lowering.**
  - `placeWrap` gives in-place `~` its target's `bitNotWrap`: the type at `uint8` … `uint128`, none
    elsewhere.
  - `modified`'s `~` branch passes Word's `~` through `wrapLeaf`, step 8b's leaf wrap, so the leaf
    is masked before the setter writes it. Both place lowerings do this.
  - `placeWrap_plain` now speaks of value assignments (`false`), and `placeWrap_bitNot` of `~`.
- **Proofs.**
  - The bit-not statement and `for`-item soundness takes the final target type's kind from
    finalization's check:
    - the deep statement theorem from its callbacks' `assignmentTargetsFit`;
    - the scoped theorems from `FinalInferenceResources.assignment_targets_fit`, through the
      enclosing statement's containment;
    - the `for`-item certificate (`ActualBitNotForItemCertificate`) carries the kind itself.
  - Fixed-width targets stay outside the meaning proofs, as step 3d's compound targets do. The
    compiler profiles of `~=` (`BitNotAssignable`, `ProjectedBitNotAssignable`) take only a `Word`
    target. So the proofs that read `Word` from the static rule read it from the receipt's
    `sourceProfile` instead (`bitNot_facts`, `projected_bitNot_head`).
  - The bit-not heads carry `targetPlain`, from their `Word` or `integer` profile
    (`CompatiblePlaceModifier.bitNotPlain_of_runtime`). With it the proofs rewrite a trace's
    relation to `BitNotSnapshot` and back (`eq_of_plain`), and the emitted code's wrap is none
    (`bitNotWrap_of_runtime`).
  - The staged inversions, the staged trace builders (`prepend_bitNot`, `prepend_projected_bitNot`)
    and the `for` header's readiness transfer (`SnapshotTransfers.ready`, `after_snapshot`) read
    the write at `BitNotAssignmentApplies`. Word's `~` alone would not keep a narrow target's heap
    well typed.
  - The unary fault-site certificate takes `operandTarget`, as the value assignments' does.
  - `w ~=;` and `m[k] ~=;` stay in the compiler body profile that the meaning proofs take
    (`AcceptedCompilerBodyProfile.validate`), and an `int8` target is outside it
    (`Tests.SourceCoreBitNotSubset`). The invocation body shape (`shape?`), which step 8d part 2
    pinned `w <<= 3` with, has no `~=` form.

### Row 1's conversions: a word becomes a value only when canonical

Made on 2026-11-13, during step 9b, on the user's choice (a). Part 2's rule for `Typedef` is
option B, decided the same day.

- **Upstream.**
  - `uint256` is `enum uint256 { uint256(word) }` (`std/std.sol:1010-1012`). The other eleven are
    one-field structs, `struct uint8 { value: word; }` (`std/unsigned.sol:17-19`,
    `std/signed.sol:17-19`, and the same at each width).
  - `uintN(w)` keeps the raw word. Only the ABI decoders check it, and they revert with
    `DirtyHigherBitsForInteger()` (`revertWithError`, `std/std.sol:272-278`):
    - `std/unsigned.sol:136, 286, 436, 586, 736`: `raw == band(raw, mask)`;
    - `std/signed.sol:154, 329, 503, 678, 852`: `raw == signextend(k, raw)`.
  - Outside std, `x.value` on the eleven struct types is rejected (`SC0205`, "cannot resolve
    field `value`"), and `case uint256(w)` is accepted. A probe of the pinned driver on
    2026-11-13 showed both, so `x.value` is no difference from upstream.
- **Lean.** A conversion checks the word as the decoders do, so a value of the twelve types stays
  canonical. That is the accepted difference: where upstream keeps a dirty word, Lean reverts.
- **The constructors (part 1).**
  - `uint256(w)`, `uintN(w)` and `intN(w)` are builtin functions `word → T`
    (`BuiltinFunctionId.fixedFromWord`), named by the type, after the program's own functions
    (`builtinFunctionNamed?`).
  - The argument is typed by the parameter, so a literal is a word (`uint8(255)`). Any other
    argument type is rejected, as upstream's constructor rejects it.
  - The meaning is `BuiltinApplies.fixedFromWord` on a canonical word, and otherwise
    `BuiltinFaults.fixedFromWord` (`SemanticFault.dirtyHigherBitsForInteger`) through
    `CallableFaults.builtinFaults`. So a direct and an indirect call fail alike.
  - A conversion is no closure: it is not in `BuiltinFunctionId.all`. So every program's globals,
    callable table and closure identities are unchanged.
  - It is lowered where it is called (`SourceCoreInteger.conversion`):
    - the word itself at `uint256` and `int256`, where every word is canonical;
    - otherwise the word if it equals its canonical form, and the dirty reason if not. The
      canonical form (`canonicalForm`) is the mask or sign extension of step 8b's `wrapLeaf`.
  - A conversion used as a function value has no closure, so it is not compiled.
- **`Typedef.abs` and `Typedef.rep` (part 2).**
  - **Upstream.** `trait Typedef<abs, rep>` (`std/std.sol:387-390`) has the identity as
    `default impl<t> Typedef<t, t>` (`std/std.sol:392-399`). Each of the twelve types has an
    instance whose `abs` is its constructor and whose `rep` gives its word (`std/std.sol:1013-1025`,
    `std/unsigned.sol:21-28`, `std/signed.sol:21-29`, and the same at each width). A default is
    admitted only when no other instance head can unify with the goal
    (`crates/hir-ty/src/solver/engine.rs:130-182`, `solver/mod.rs:640-643`). So `abs` takes its
    type from its context, `rep` gives `word` at the twelve types, and both are the identity at
    `word`.
  - **Where they are found.** A qualified call `Typedef.abs(e)` or `Typedef.rep(e)` is a builtin
    call when no local is named `Typedef` and no source namespace is (`qualifiedFunctionsNamed`
    finds none, then `typedefCall?`). A program's own `Typedef` namespace takes the names over.
  - **The rule for "known at the call".** The function is chosen at the call, once its arguments
    are inferred (`typedefFunction`). Arguments are inferred with no expected type, as every call's
    are.
    - `Typedef.abs(e)` takes the expected type the call is inferred against, resolved by the
      substitution so far. An annotated `let`, a `return`, the right side of `=`, and a group or a
      conditional's branch inside one of those give one. A call's argument, an operator's operand
      and an unannotated `let` give none.
    - `Typedef.rep(e)` takes `e`'s inferred type, resolved the same way.
  - **The functions.**
    - At `word`, either is the word itself (`BuiltinFunctionId.wordIdentity`), as the default gives
      it.
    - At one of the twelve types, `Typedef.abs` is part 1's conversion of that type
      (`fixedFromWord`), with its check and revert. So `Typedef.abs` at `uint256` and `int256`
      never fails.
    - At one of the twelve types, `Typedef.rep` is the value's word (`BuiltinFunctionId.fixedToWord`,
      `BuiltinApplies.fixedToWord`), which never fails.
    - Each is recorded under the builtin's own spelling, which part 1's metadata check
      (`validateBuiltinFunctionCall`) requires.
  - **Rejected.** Any other type, and a type still open at the call, is rejected with
    `operatorNotSupported "Typedef" τ`, which names the type, or its variable when it is open. So
    `let a = Typedef.abs(w); let b: uint8 = a;`, `take(Typedef.abs(w))`, `Typedef.rep(5)` and
    `let a = 5; … Typedef.rep(a)` are rejected, as are `Bool` and `integer`. The typing is
    upstream's wherever both accept.
  - **The remaining gap.** A probe of the pinned driver on 2026-11-13 accepts each of those waiting
    cases: its instance resolution waits for later uses, and an open literal takes its default.
    This is a gap, not a permanent difference. Option A, a `Typedef` constraint solved at
    finalization, could lift it as its own unit, which is not scheduled.
  - **Other types.** Upstream's default gives the identity at every other type too: the same probe
    accepts `let c: bool = Typedef.rep(b)`, and rejects `Typedef.abs(w)` at `bool` (`SC0207`,
    "cannot satisfy trait constraint: bool: Typedef<word>"). Lean rejects both. The identity at
    other types is generic code, which row 1 leaves out.
  - **Lowering.** Both are lowered where they are called, as part 1's conversions are
    (`SourceCoreInteger.builtinConversion`): `conversion` at a fixed-width type, and the word
    itself at `word`. Neither is a function value: `Typedef.abs` as a value is no expression Lean
    types.
- **`case uint256(p)` (part 3).**
  - **Upstream.** `case uint256(w)` is `uint256`'s enum constructor pattern (`std/std.sol:1010-1012`), and
    `rep` uses it (`std/std.sol:1018-1024`). A probe of the pinned driver on 2026-11-13 accepted it outside std
    with a binder, a literal (`case uint256(0)`), a wildcard, inside a tuple, and at an open scrutinee, which
    takes `uint256`. It rejected `case uint256(w)` at `word` (`SC0201`, "type mismatch: expected word, found
    uint256"), and `case uint8(w)`, `case int8(w)`, `case uint128(w)` and `case int256(w)` (`SC0107`,
    "invalid pattern syntax"): the other eleven are structs.
  - **Lean.** `uint256(p)`, spelled with no qualifier and no leading dot, at a type that is `uint256` or still
    open (`uint256PatternArgument?`), unifies the type with `uint256` and matches `p` against the value's word
    at `word` (`MatchPatternInstruction.uint256Word`, `MatchPatternResolution.uint256Word`). A `uint256` value
    is its word, so every value matches `uint256(w)`, which binds that word, and `uint256(p)` is irrefutable
    exactly when `p` is.
  - The static rule is `PatternInstructionHasType.uint256Word` (`p` at `word`), the dynamic one
    `PatternInstructionMatches.uint256Word` (`p` against the same value), and the source rule
    `MatchPatternSourceRepresents.uint256Word`.
  - Both pattern compilers lower it as `p`'s matcher, since a `uint256` value's Core value is its word.
  - At any other type `uint256(p)` is an ordinary constructor pattern, so it is rejected as upstream rejects
    it. So are `uint8(p)` … `int256(p)` at the other eleven types.
  - `x.value` is not implemented. Upstream rejects it outside std (part 1's probe), so this is no difference.
- **The revert.**
  - `SourceCorePanics.dirtyReason` is the word just below the panic range, `2^256 − 2^8 − 1`.
  - The fault-site tables allocate below it (`tableBound`). `Table.PanicFree` and preparation's
    `PanicFree` check that bound.
  - The decoder gives `RuntimeError.dirtyHigherBitsForInteger` after the tables and before the
    panics (`Table.dirty_diagnostic`).
  - `SourceCorePanics.dirtyRevertData` is upstream's `0x6cc54a63`, with no arguments.
  - The revert is a Frontend convention, as the panics are, so Core, the Hull importer and
    ContractRuntime are unchanged.
  - `FaultTokens` has no law for it yet: no proof reads a conversion's revert. The builtin
    profile that brings the conversions in would add it.
- **Proofs.** The conversions are compiled but stay outside the closed subset, as the fixed-width
  compound targets do.
  - Builtin calls are proved through `InputRep`, which has no conversion.
  - The builtin-call inversion (`BuiltinCalls.call_of_accepted`) takes
    `function.conversion? = none`. The proofs get it from the closure's catalog index
    (`conversion?_of_inventory`) or from the supported syntax.
  - `conversion?` gives the type a conversion gives, so part 2's two functions are conversions
    too.
  - The inference proofs follow a `Typedef` call as a builtin call (`recordBuiltinFunctionCall`).
    `IndirectCalleeAt` excludes it, so the callee is never inferred.
  - A builtin profile with the dirty reason's token would bring the conversions in.
  - `case uint256(p)` needs no exclusion. The pattern proofs take it as `p` at the value's word:
    inference soundness (`inferMatchPatternFlatFuel_success_uint256_sound`), irrefutability and
    completeness (`PatternInstructionIrrefutable.matchesTyped`), and both pattern certificates'
    success and decision (`Tree.uint256Word`).

### Row 1: steps

Row 1 is committed in steps, each through the full gate, so that each can be
integrated on its own. The operators come before the literals. An operator
whose operand is an open literal waits for the literal's type and takes it
(`let a = 1 + 2; let b: uint8 = a;`), so a literal can reach one of the twelve
types only once the operators have typing rules there. Checked `/ %` were
first planned after the literals and moved before them for this reason
([row 1's division](#row-1s-division-before-the-literals)).

1. **Types.** The twelve types are builtins (`BuiltinType.fixed`), resolved
   before declared types. Their values are canonical words
   (`ValueHasType.fixed`), as parameters, results, locals and mapping
   elements, and a missing mapping element is zero. The public API rejects a
   non-canonical argument before the body runs. No operator is defined on the
   twelve types yet, no literal is accepted at them, and open literals still
   default to `word`.
2. **The operators that are Word's on canonical words.** `==`, `!=` and
   `& | ^` on the twelve types, `< > <= >=` on the unsigned ones, and `~` on
   the signed ones and `uint256` are builtins without requirements
   (`Detail.fixedBinaryOperator`, `Detail.fixedUnaryOperator`), with both
   operands of the same type. On canonical words they compute what Word's
   operators compute and keep the words canonical: `& | ^` keep a word below
   `2^N` or sign-extended from bit `N - 1`, and `~` keeps a sign-extended
   word sign-extended. So they evaluate by the existing word rules, and no
   rule looks up an operand's type. This step is committed in two parts: the
   comparisons and unsigned bitwise operators, then the signed bitwise
   operators and `~`.
3. **Checked `+ - *`, the signed comparisons and `~` on the narrower
   unsigned types**, chosen as above. Checked `+ - *` panic with `0x11`.
   Comparisons are signed for `intN`. `~` on `uintN` below 256 keeps the low
   `N` bits. Compound `+= -= *=` check the result at the guard, after the
   setter. This step is committed in four parts: the binary lookup with the
   signed comparisons, which lower to Core's `wordSgt`; the unary lookup with
   `~`; checked `+ - *`, whose faults take the lookup too; and the compound
   forms.
4. **Checked `/ %` and `/= %=`.** A zero divisor panics with `0x12`, and
   `MIN / −1` panics with `0x11`, while `MIN % −1` is 0. Quotients round
   toward zero, and remainders take the dividend's sign. `/= %=` test the
   divisor and the range in the guard after the setter, outside the meaning
   proofs as step 3's compound targets are.
5. **Literals.** A literal at one of the twelve types is range-checked at
   compile time, with builtin `Int` evidence for each type
   ([row 1's literals](#row-1s-literals-checked-by-inference-and-the-compiler)).
   Open literals keep the `word` default.
6. **Unary minus.** A negation out of range panics with `0x11`, and a unary
   `-` on a literal folds into the literal
   ([row 1's unary minus](#row-1s-unary-minus-folded-or-read-as-0---e-before-inference)).
7. **The `uint256` default.** Open literals default to `uint256`, and an open
   literal in no operator, comparison or requirement is rejected as
   ambiguous ([row 1's `uint256`
   default](#row-1s-uint256-default-chosen-by-the-literals-uses)). The
   existing tests that relied on the `word` default change in this step.
   - 7b. **Compound assignments on an open target.** `+= -= *= /= %= &= |=
     ^=` on a target whose type is still open take the operand's type and
     count as an operator use for the `uint256` default, as upstream's
     rewrite to `x = x op e` types them, and finalization checks the type the
     target resolves to ([row 1's `uint256`
     default](#row-1s-uint256-default-chosen-by-the-literals-uses)). The place
     is still evaluated once. Compound shifts stayed `word`-only until step 8d.
8. **Unchecked operators and shifts on the twelve types**, and ports of the
   upstream fixtures.
   - 8a. **Unchecked `+ - * / %`** on the twelve types, and `-x` in a block
     ([row 1's unchecked
     arithmetic](#row-1s-unchecked-arithmetic-wrapped-to-the-types-width)).
   - 8b. **Unchecked compound assignments** on fixed-width and open targets
     ([row 1's unchecked compound
     assignments](#row-1s-unchecked-compound-assignments-the-wrap-belongs-to-the-leaf)).
   - 8c. **The literal operands of unchecked operators** wait for their type
     and default to `uint256`, and finalization rejects one that becomes
     `integer` ([row 1's unchecked literal
     operands](#row-1s-unchecked-literal-operands-they-wait-and-never-take-integer)).
   - 8d. **Shifts on the twelve types**, with their literal operands, by an
     amount of `word` or an unsigned type ([row 1's
     shifts](#row-1s-shifts-on-the-twelve-types-the-amount-takes-its-own-type)).
     The step is committed in two parts: the binary shifts, then the compound
     forms.
   - 8e. **Ports of the upstream fixtures.** The functions of `checked-arith`,
     `unchecked-scope`, `shift-operators`, `int-ops` and
     `issue92-checked-defaults` that need no conversion and no contract
     storage, and the ones that convert only to reach a type, adapted where
     the meaning is kept, run through the public API with the fixtures' values
     and panic codes (`runUpstreamFixtures` in
     `Tests.SourceCoreFixedIntegerOperators`).
9. **The rest of row 1.**
   - 9a. **In-place `~` at the twelve types**, as upstream's rewrite of `x ~=` to `x = ~x` gives it
     ([row 1's in-place `~`](#row-1s-in-place--the-target-keeps-its-type)), committed in two
     parts:
     - first the typing, with the types on which `~` is Word's (`uint256` and the signed ones);
     - then `uint8` … `uint128`, whose `~` keeps the low `N` bits.

     `basic`'s `bnoteq` is ported with 8e's functions.
   - 9b. **Conversions between `word` and the twelve types**, a word becoming a value only when it
     is canonical ([row 1's conversions](#row-1s-conversions-a-word-becomes-a-value-only-when-canonical)),
     planned in three parts:
     - first `uint256(w)`, `uintN(w)` and `intN(w)` with the dirty-integer revert (done);
     - then `Typedef.abs` and `Typedef.rep`, chosen by the type known at the call (done);
     - then `case uint256(p)`, which matches the value's word with `p` (done); `x.value` is rejected
       outside std upstream too.

     Each part ports again the 8e functions it makes possible, as upstream wrote them.
