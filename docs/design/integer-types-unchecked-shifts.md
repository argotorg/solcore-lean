# Integer types, `unchecked` blocks and shifts

Updated: 2026-11-17. Module paths and file counts below predate the layout refactor of f820cc25f;
the marker `-- leanmerge: from <old module>` finds each old module's current file
([following older notes](../guide/conventions.md#following-older-notes)).

Rows 1 to 3 of the roadmap table "Following upstream's semantics: the next units" bring three
solcore-rs changes to Lean's source language. All three are done:

- checked integer types and literal defaulting (#95);
- `unchecked` blocks (#119);
- the shift operators (#129).

This note covers the Lean side: the parser, typing, the source semantics and the lowering to Core.
It gives upstream's semantics at the pin, Lean's semantics as built, each decision with its reason,
the differences from upstream, and what remains. Where a feature is compiled but outside the
meaning proofs, its section says what bringing it in would take.

## Upstream's semantics at `e2eef194`

This comes from std (`std/std.sol`, `std/unsigned.sol`, `std/signed.sol`, `std/unchecked/*.sol`),
the compiler (`crates/parser`, `crates/hir-ty`, `crates/specialize`) and the fixtures
`checked-arith`, `int-ops`, `issue92-checked-defaults`, `unchecked-scope` and `shift-operators`.

**Types.** `uintN` has the range `[0, 2^N − 1]` and `intN` the range
`[−2^(N−1), 2^(N−1) − 1]`, for N in 8, 16, 32, 64, 128 and 256. A value is a `word`: an unsigned
value as it is, a signed one in two's complement, sign-extended from bit N − 1. std defines
`uint256` as an enum and the other eleven types as structs, each wrapping a `word`. Its operators
are trait impls, and literals go through `Int.fromInteger(comptime x: integer)`. Mixing two types,
as in `uint8 + uint16`, is rejected (`SC0201`). Bitwise results stay within the type, masked or
sign-extended, and comparisons are signed for `intN`.

**Checked arithmetic**, outside `unchecked` blocks:

| Operation | Result | Panic |
| --- | --- | --- |
| `a + b`, `a - b`, `a * b` | the exact result | `0x11` when it leaves the type |
| `a / b` | the quotient rounded toward zero | `0x12` when `b = 0`; `0x11` for `MIN / −1` |
| `a % b` | the remainder, with the dividend's sign | `0x12` when `b = 0`; `MIN % −1` is 0 |
| `-a` | `0 − a` | `0x11` for any nonzero unsigned value and for `MIN` |

A panic reverts with 36 bytes: the selector `0x4e487b71`, then the code as a 32-byte big-endian
word.

**`unchecked { … }` blocks.**

- Inside a block, `+ - * / %`, unary `-` and `+= -= *= /= %=` wrap the exact result to the type's
  width. `MIN / −1` gives `MIN`. Division and remainder by zero still panic with `0x12`. Shifts,
  bitwise operators and comparisons are the same in both contexts.
- The scope is lexical. A block reaches the statements written in it, including nested blocks,
  `if`, loops and `match` arms, but not lambda bodies written in it, functions or lambdas called
  from it, or anything after it. A lambda body may contain its own block. A block directly inside
  another block is rejected (`SC0001`).
- The block is a statement: as an expression it is a parse error. `unchecked` is a contextual
  keyword and stays a valid identifier.
- On `word`, `/ 0` and `% 0` give 0 outside a block (raw EVM division) and panic with `0x12` inside
  one, because std's `UncheckedDiv<word>` checks the divisor. `+ - *` and unary `-` wrap in both.
- A block needs `std.unchecked.unsigned` or `std.unchecked.signed` imported, even with only `word`
  operators (`SC0207` otherwise). Importing both with `*` is ambiguous (`SC0120`), as the signed
  one re-exports the unsigned traits.

**Shifts.** `<<` and `>>` are two adjacent `<` or `>` tokens; `<<=` is `<` then `<=`, and `>>=` is
`>` then `>=`. They bind tighter than `&` and looser than `+ -`, and associate to the left. The
result has the left operand's type. The amount is a `word` or an unsigned type
(`Shl<T, n> where n: ShiftAmount`), and a signed amount is rejected (`SC0207`). A shift never
panics. `v << s` is 0 when `s` is at least the type's width, and otherwise `v · 2^s` wrapped to
the type. `v >> s` is the floor quotient by `2^s`: logical for unsigned types and `word`,
arithmetic for signed types, and 0 or −1 when `s ≥ 256`.

**Literals.**

- Context types a literal: an annotation, a parameter, a return type, or the other operand.
- After the solve loop, `crates/hir-ty/src/infer/obligations.rs` defaults open literals to
  `uint256` in three passes:
  - `default_integer_literals_with_non_int_obligations`: a literal or numeric pattern whose
    variable occurs in an unresolved obligation of a class other than the builtin `Int`, such as
    an operator's (`Sub`, `Ord`, …) or a generic call's bound;
  - `default_integer_literal_patterns`: every numeric pattern still open, followed by a range
    check of every `uint256` pattern (`check_integer_literal_pattern_range`);
  - `default_root_integer_literals`: a literal whose variables all occur in the root body's type.

  The obligations are then attempted again, so a bound with no `uint256` implementation is an
  error. Any other open literal is ambiguous (`SC0299`): `let y = 7;` with `y` unused,
  `let y = 7; let z = y;`, `sc_id(7)` with an unused result, `lam () { return 7; }` never called,
  or `let y = poly(7);` when `poly`'s only bound is `Int` (`poly_int_defaulting`). `7 == 7`, an
  unused `7 + 1`, `1 << 3` and a `match` on an open literal are accepted. No literal defaults to
  `word`.
- The parser rewrites `lhs op= rhs` to `lhs = lhs op rhs` before typing (`assign_stmt_kind` in
  `crates/parser/src/parse/stmt.rs`); only storage-index compounds keep an `AssignOp`. So an open
  local target shares one type with its operand, which a later use gives or else defaults to
  `uint256`.
- A closure stays monomorphic: its parameters take their types from its calls, or their literals
  default to `uint256`.
- At an integer type, an out-of-range literal is a compile error (`SC0409` or `SC0411`): `256` or
  `-1` at `uint8`, `-129` at `int8`, `2^256` defaulted, `let k = -1;`, and `a + 300` with
  `a: uint8`. A `word` literal wraps modulo 2^256, so `-1` is `2^256 − 1`, and an `integer`
  literal is exact.
- A `-` applied directly to a literal is part of the literal, through parentheses and repeated. So
  `-128`, `-(128)` and `- -5` are literals, and `-128` is accepted at `int8`.
- Numeric patterns are allowed only on `word`, `integer` and `uint256` scrutinees.

**ABI.** std's decoder rejects an argument whose word is not the canonical representation of a
value of its type. It reverts with `DirtyHigherBitsForInteger()` (`0x6cc54a63`) before the body
runs. The encoder masks or sign-extends results.

## Probe of the pinned Rust paths

A probe compiled hand-written contracts through checked Hull export, Sonatina O0 and O2, and Yul
(`export-rust-yul.py` with solc 0.8.35). It ran them on Anvil and in the Lean Hull runner on the O0
export, against a Python model of the semantics above. The calls covered checked and unchecked
arithmetic at extreme operands of `uint8`, `uint256`, `int8` and `int256`, a block's reach through
control flow, lambdas and helpers, compound assignments, comparisons, bitwise operators, shifts by
amounts up to `2^256 − 1`, `word` division by zero, literals typed by their later uses, and
canonical and non-canonical ABI arguments of all twelve types. Every call matched on every path, so
no upstream defect was recorded. A compile probe through checked Hull export gave the acceptances
and the rejection codes listed above.

## Semantics in Lean

The twelve types are builtins, resolved before declared types such as `word`. Their operators join
the builtin operator path that `word` and `integer` use. A value of one of them is the `.word` that
is its canonical two's complement representation (`ValueHasType.fixed`), as a parameter, result,
local or mapping element. A missing mapping element is zero.

**Operators.** Both operands have the same type, except a shift's amount.

| Form | On the twelve types | On `word` |
| --- | --- | --- |
| `+ - *` | Checked: `Panic(0x11)` outside the type's range | Wrap |
| `/ %` | Checked: `/` rounds toward zero, `%` takes the dividend's sign; `Panic(0x12)` on a zero divisor; `MIN / -1` panics with `0x11`, `MIN % -1` is 0 | A zero divisor gives 0 |
| `-e` | Read as `0 - e`: `Panic(0x11)` for `MIN` and for any nonzero unsigned value | Wraps |
| `+ - * / %` and `-e` in an `unchecked` block | Wrap to the type's width; `MIN / -1` is `MIN`; a zero divisor still panics with `0x12` | Wrap; a zero divisor panics with `0x12` |
| `== != < > <= >=` | Signed on `intN` | Unsigned |
| `& \| ^ ~` | Results stay canonical; `~` keeps the low `N` bits on the narrower unsigned types | Word's |
| `<< >>` | The value's type, by an amount of `word` or an unsigned type; `<<` keeps the low `N` bits, sign-extended on `intN`; `>>` is arithmetic on `intN`; an amount of at least the width gives 0, or -1 for a negative value's `>>`; never panics | Word's shifts |
| `op=` and `x ~=` | As the binary or unary form, at the target's type; the place is evaluated once, and the check runs after the setter | As the binary or unary form |

**Literals.** A literal at one of the twelve types is range-checked by inference and again by the
compiler. A `-` over a literal folds into it, so `-128` is an `int8` literal and `-1` at `uint8`
is a compile error. An open literal defaults to `uint256` when an operator, a comparison, a
compound target or a pending requirement other than its own `Int` uses it, or when it is negative.
Any other open literal is rejected as ambiguous. Numeric patterns work at `word`, `integer` and
`uint256`, range-checked at `uint256`.

**Conversions.** `uint256(w)`, `uintN(w)` and `intN(w)` convert a word that is canonical for the
type, and otherwise revert with `DirtyHigherBitsForInteger()`. `Typedef.abs` and `Typedef.rep` are
chosen by the type known at the call. `case uint256(p)` matches every `uint256` value, with `p`
matched against its word.

**Panics.** A panicking operation is the source fault `SemanticFault.panic code`, and in Core a
language failure whose reason encodes the code. A run that panics ends with
`.failed reason session`, and `session.diagnostic key reason` gives the panic, its code and its
function. A function of the diagnostic gives upstream's 36 bytes of revert data. How a panic is
presented is a choice about Lean's API, which has no revert channel. Which programs panic, and
with which code, follows upstream.

**Public API.** An integer-type argument or result is a `.word` holding the representation, with
the integer type as its source type. An argument whose word is not canonical for its type is
rejected before the body runs, as a data-conversion error: the counterpart of std's
`DirtyHigherBitsForInteger()` revert, since Lean's API takes typed values, not calldata.

**Unchanged:** Core, the Hull importer and the shared contract runtime.

**Meaning proofs.** The operators, literals, unary minus and `case uint256(p)` at the twelve types
are inside the meaning proofs, and so, on the accepted-body route, are the conversions. So are
compound assignments at fixed-width targets, `<<=` and `>>=` included. In-place `~` there is
compiled but outside them.

**Tests.** `Tests.SourceCoreShiftExecution` and `Tests.SourceCoreUncheckedExecution` run shifts
and blocks through the public API. `runUpstreamFixtures` in `Tests.SourceCoreFixedIntegerOperators`
runs, with the fixtures' values and panic codes, the functions of `checked-arith`,
`unchecked-scope`, `shift-operators`, `int-ops` and `issue92-checked-defaults` that need no
conversion and no contract storage, and those that convert only to reach a type, which now run as
upstream wrote them.

### Shifts as implemented

- **Parsing.** One decoder reads an operator from one token or from two adjacent ones
  (`BinaryOp.at?`, `ValueAssignOp.at?`), and the parser and its declarative grammar both use it.
  Type arguments still close with two `>` tokens (`Option<Option<a>>`), and the lexer is unchanged.
  The precedence ladder is `* / %` 9, `+ -` 8 and shifts 7.
- **Typing.** Inference types a shift before any dispatch, and the dispatch map gives shifts no
  trait. The value and the amount take their own types, and an open literal operand waits
  ([row 1's shifts](#row-1s-shifts-on-the-twelve-types-the-amount-takes-its-own-type)).
- **Semantics.** `BinaryPrimitiveApplies` has the two `word` shifts, and the compound forms apply
  them. The twelve types have their own shifts. A shift of any other value is an operand fault.
- **Lowering.** Shifts lower to `wordShl` and `wordShr`, and on the twelve types through the type's
  shift bodies. A compound shift of a local uses a frontend copy of Core's compound-assignment
  shape, so Core is unchanged.
- **`integer` leaves.** The data-place lowering refuses shifts and the unchecked operators at
  `integer`, which typing never produces (`ValueAssignOp.wordOnly`). The assignment profile shared
  by its theorems reads `T = .integer ∧ operator.wordOnly = false`.
- **Legacy fragments.** The older strict-`word` evaluators leave the shifts out.

### Unchecked blocks as implemented

- **No statement form.** Inference reads `Syntax.Statement` itself, and its functional-induction
  proofs name 514 numbered cases in 25 files. So a `StatementValue` constructor would reach them,
  even though no typed program keeps it. `Syntax.Unchecked` works around the parser instead:
  - it records each `unchecked` at a statement start (after `{`, `}` or `;`) that is followed by
    `{`, and replaces the keyword's bytes with spaces, so the parser reads a plain block statement
    and every span stays the same;
  - after parsing, `mark` gives each recorded block's arithmetic its unchecked operators.

  `ProgramLoading` runs both steps. A block written in another block, or a recorded `{` that starts
  no block statement, is a load error. A lambda body written in a block starts outside it.
- **Operators.** `BinaryOp` and `ValueAssignOp` have `uncheckedAdd`, `uncheckedSubtract`,
  `uncheckedMultiply`, `uncheckedDivide` and `uncheckedModulo`, which only the pass produces.
  - On `word` they type, run and lower as the checked operators, except for a zero divisor.
  - On a declared type they dispatch to `UncheckedAdd`, `UncheckedSub`, `UncheckedMul`,
    `UncheckedDiv` and `UncheckedMod` (methods `add`, `sub`, `mul`, `div` and `mod`).
  - On `integer` inference rejects them, since upstream defines no unchecked instance for it.
  - On the twelve types they are builtins that wrap to the type's width
    ([row 1's unchecked arithmetic](#row-1s-unchecked-arithmetic-and-its-literal-operands)).
- **Division and remainder.** `/`, `%`, `/=` and `%=` in a block panic with `0x12` on a zero
  divisor ([panics](#panics-one-generalized-fault-law-one-reason-per-panic-code)).

## Decisions

### The design: builtins, a pass, adjacent tokens and a fault reason

- **Builtins, not a Lean std.** Reading upstream's std would need structs, trait-qualified calls, a
  bundled std, compile-time evaluation of `fromInteger`, a `panic` builtin, trait-dispatched
  compound assignment and two-parameter operator traits. Each is a frontend feature with its own
  proofs, and every arithmetic operation would become a trait method call. With builtins, programs
  import nothing, so upstream's required import for `unchecked` blocks has no Lean counterpart.
- **A pass, not a typed `unchecked` statement.** About 32 SourceSemantics modules match the typed
  statement forms exhaustively, against 5 that match `BinaryOp`. With the pass, the typed IR, the
  source semantics and the lowering see no new statement form.
- **Adjacent tokens, not `<<` and `>>` tokens.** A `>>` token would break nested type arguments
  unless the type parser split it, and upstream joins adjacent tokens too.
- **A fault reason, not a panic outcome.** A new control outcome would have to be propagated by
  every sequencing rule. A panicking primitive is instead a base case of the operator and
  assignment fault relations, so the existing propagation carries it out of every construct.

### Panics: one generalized fault law, one reason per panic code

- **Chosen: one law, as an instance argument.** `FunctionCalls.FaultTokens faults` is a `Prop`
  class whose first law states that the fault `.panic code` fails with that code's reason;
  `RecursiveStageMeaning.FaultTokens` is its staged form. Theorems that need it take
  `[FaultTokens faults]`. Lean finds the instance from the caller's own binder, so the threading
  changes declarations and leaves calls alone. One instance, for the decoded fault relation of the
  public results, serves the places that prove `uninitialized`.
- **Why.** Per-reason threading would put a hypothesis beside each `uninitialized` one: about 414
  declarations in 206 files under `Solcore/SourceSemantics/CoreLowering`, plus every call that
  passes `uninitialized` on, and the same again for each later family. Row 1's checked arithmetic
  and row 4's array panics (`0x31`, `0x32`, `0x41`) are panics too, so they need no more threading.
  A later family whose token does not depend on its site adds a field.
- **One reason per code, not per site.** `SourceCorePanics` gives panic code `c` the Core reason
  `2^256 − 2^8 + c` in every function, and upstream's revert data (`revertData`). A site's token
  would depend on its `reasonAt`, which varies by header and method under binders, so no single
  instance could carry it.
- **Decoding.** `Table.diagnostic?` tries the fault-site tables first, and a reason in the panic
  range then decodes to `RuntimeError.panic code` at the function's declaration site. So the
  existing decoding theorems keep their statements. Preparation fails with `Error.panicRange`
  unless every table reason lies below the panic range (`Compiled.panicFree`). That check gives the
  panic law for the decoded relation (through `issued_panicFree` and `tokens`), and
  `Table.panic_diagnostic` proves that a checked table decodes every panic. The diagnostic names
  the code and the function, not the operator's span; upstream's revert data carries no site
  either.
- **Lowering.** On `word`, a `/` or `%` in a block lowers to `panickingBody`, which tests the
  divisor and fails with the panic's reason, or applies `wordDiv` or `wordMod`. A compound `/=` or
  `%=` checks the divisor in `guard`, after the setter has rebuilt the latest root and before the
  write. So a structural fault on the latest root still wins over the panic, as the source rule
  requires (`AssignmentOperandsPanic`). `DataPlaceGuard` relates `guard` to its write.

### Row 1's values: integer-typed values are words

- **Chosen: words with typed operations.** The typed operations check the ranges, as upstream's
  Hull and the generators' Core reference do.
- **Why.** Both options give upstream's results, and words touch fewer proofs: the twelve types
  have Core type `word`, and `ValueHasType` gains one case, a word that is canonical for the type.
  Two later decisions below refine the rest of this one. The representations keyed by the
  lowering's metadata view gain a `fixed` case
  ([runtime types](#row-1s-runtime-types-the-shape-erases-the-twelve-types)). And the rules choose
  an operation by looking up the operand's static type, rather than through a rewritten operator
  ([operators](#row-1s-operators-chosen-from-the-operands-static-type)).
- **Rejected: an exact `Dynamic.Value` constructor.** Every relation that matches values would gain
  a case: about 126 arms in 37 files under `Solcore/SourceSemantics/CoreLowering`, 13 arms in five
  files under `Solcore/SourceSemantics/Dynamic`, and the frontend's value conversions and staged
  values.

### Row 1's operators: chosen from the operand's static type

- **Chosen.** The binary and unary rules look up their left (or only) operand's node, and apply
  the twelve types' operations when its type is one of them. About ten rule constructors gain the
  lookup, and the inference proofs are unaffected. The other operand types keep their primitive
  relations, restricted to operands that are not of a fixed-width type, so the semantics stays
  deterministic. CoreLowering chooses its mode from the same type (`Tree.binary`, `BinaryProfile`).
- **Which operators.** Those that are Word's on canonical words need no lookup: `==`, `!=` and
  `& | ^`, `< > <= >=` on the unsigned types, and `~` on the signed ones and `uint256`. Only the
  operators whose meaning differs take the lookup, and only those restrict the primitive rules:
  when this was decided, signed order, `~` on the narrower unsigned types and checked arithmetic.
  The unchecked operators joined them later (`FixedBinaryOwn`). Compound assignment needs no
  lookup, because its form holds the target's type.
- **Preservation** needs the looked-up type to be the operand's typed type where the result would
  leave the range. The source's unique node occurrences give it (`Dynamic.operandType?_of_typing`).
- **Rejected: rewriting the typed IR after finalization.** The inference soundness proofs rest on
  `Detail.finalize_typedSource`: the final source is the inferred node table under the final
  substitution. About 70 rewrites in about 25 inference files use it, as do the
  `TypingSourceExtends` premises of 11 more. A rewritten node falsifies all of them.

### Row 1's runtime types: the shape erases the twelve types

- **The shape views erase them.** `Dynamic.runtimeType` and `SourceTypedRuntime.runtimeType` map
  the twelve types to `word`, as they erase `comptime`. They only compare value shapes: the
  mapping key guard (`ValueRuntimeTypeMatches`), the builtin argument check
  (`ValuesFirstTypeMismatch`), the shared runtime's `Value.type?` checks and the unified API's
  result check.
- **The metadata view keeps them.** The lowering's operator profiles test
  `SourceCoreRawMetadata.runtimeType leaf = .word` to choose word operations. Erasing the twelve
  types there would apply wrapping word operations to them. So the value relations keyed by this
  view (`CompatiblePayload.ValueRep`, `DataPayload.ValueRep`, the public input and output shapes,
  the defaults) have a `fixed` case: the word itself, canonical for the type.
- **Inputs check the range.** Every encoder and the shared runtime's input validator reject a word
  that is not canonical for its type, nested values included (`unstagedType`).
- **The legacy lowering rejects them.** `SourceCoreElaboration.lowerType` rejects the twelve types,
  as it rejects `integer`, because its local-cell proofs rely on each Core type having one source
  type. The catalog projections, which the public pipelines use, lower them to `word`.

### Row 1's compound assignments: checked at the guard

- **Typing.** A compound assignment takes the target's type where its binary operator is a builtin
  there (`Detail.compoundOperandType`).
- **Semantics.** The value-assignment rules apply `CompoundAssignmentApplies` at the target's
  static type: `AssignmentValueApplies` where the meaning is Word's, Integer's or plain assignment,
  and `FixedBinaryApplies` for checked arithmetic at a fixed-width target. Checked arithmetic
  outside the range panics with `Panic(0x11)` after the latest root has been traversed
  (`AssignmentOperandsPanic`), as `/=` and `%=` do.
- **Lowering.** The place lowering chooses the modifier from the target's static type
  (`assignmentModifier`). Checked `+= -= *=` compute Word's operation, which in range is the exact
  result's word. `guard` checks the exact result, read from the snapshot and the right-hand side,
  against the type's range after the setter (`Check.range`). For `/= %=` the operation is Word's
  `wordDiv` and `wordMod`, or `wordSdiv` and `wordSmod` on the signed types, and the guard tests
  the divisor against zero first (`DivisorPasses`). `&= |= ^=` keep Word's modifier.
  `CompatibleBareAssignment.of_lower` states the choice.
- **Why at the guard.** After the setter, a structural fault on the latest root still wins over the
  panic, as the source rule requires.
- **Fault sites.** A fixed-width target has its own site
  (`SourceCoreAssignmentFaultSites.operandTarget`), so an absent operand fails with its own
  `invalidAssignmentOperands` diagnostic, naming the target's type.
- **Meaning proofs.** `WideAssignmentProfile` admits these targets (`FixedCompoundAssignment`),
  and so does the receipts' `sourceProfile`, which still excludes Integer targets.
  `FixedCompoundModifier.Agreement` and `CompatiblePlaceModifier.wide_outcome` relate the
  compiler's modifier and check to `CompoundAssignmentApplies`. Inside the plain profiles,
  `assignmentModifier_plain` turns the compiler's choice back into `binaryOperator`'s, and
  `CompoundAssignmentApplies.eq_of_plain` the relation back into `AssignmentValueApplies`.

### Row 1's division: truncated over Core's Euclidean operations

`/` gives the quotient rounded toward zero (`Int.tdiv`) and `%` the remainder with the dividend's
sign (`Int.tmod`), as `Dynamic.divisionResult` (`FixedBinaryApplies.division`). A zero divisor
panics with `Panic(0x12)` (`FixedBinaryPanics.divisionByZero`), and a result outside the range
with `Panic(0x11)` (`divisionOverflow`). Core's `integerDiv` and `integerMod` are Euclidean, as
Lean's `Int` operations are. So the division body (`SourceCorePrimitive.divisionBody`) tests the
divisor against zero, divides the magnitudes with Core's operations and restores the sign
(`truncatedDivision`), then checks the range, as checked `+ - *` do. `/ %` share the checked mode
inside the meaning proofs (`BinaryProfile.fixedDivision`).

### Row 1's literals: range-checked, folded and defaulted by their uses

- **Typing.** A literal whose type resolves to one of the twelve types takes it
  (`Detail.supportedIntegerLiteralTarget`), and each type has builtin `Int` evidence
  (`BuiltinImplId.intFixed`). An operator that waited on an open literal takes the literal's later
  type and that type's rule (`binaryFixed_hasType_of_deferred`). So
  `let a = 200 + 100; let b: uint8 = a;` panics with `Panic(0x11)`: each operand fits, but the sum
  does not.
- **The range is checked twice**: by inference's finalization (`Detail.literalFitsTarget`,
  `Error.integerLiteralOutOfRange`, which names the type and the value) and by the compiler
  (`validateFixedIntegerLiteral`). The static rule `IntegerLiteralValid.fixed` needs the type and
  the evidence, not the range, because the nested inference proofs carry no literal node and a
  range premise would need one at about 200 sites. The construction
  `ResolvedIntegerLiteralConstructs.fixed` needs the range, so the literal's word is canonical.
- **Unary minus is gone before inference.** `Syntax.Unchecked.mark`, which every loaded file goes
  through, removes each `UnaryOp.negate`: a `-` over a numeric literal, through groups and
  repeated, folds into the literal's spelling, and any other `-e` reads as `0 - e`, as upstream
  reads it. A declared type is rejected, since the `0` would need `Int` of that type, which is
  builtin. Inference still rejects a `negate` (`operatorNotSupported`), so its soundness holds for
  every syntax tree. A negative literal's range is checked with its sign
  (`signedLiteralFitsTarget`), so only `-0` fits an unsigned type; at `word` it wraps.
- **The `uint256` default.** After inference, a literal whose type is still a variable defaults to
  `uint256` (`Detail.defaultIntegerLiteralTarget`) when its type occurs in an operand type of a
  unary or binary node (`operatorMentions`), in a pending requirement other than its own builtin
  `Int` (`requirementMentions`), or when its spelling is negative, so `let k = -1;` fails
  `uint256`'s range as upstream's `SC0411` does. Compound targets and in-place `~` count as
  operator uses. Any other open literal is ambiguous (`Error.ambiguousIntegerLiteral`). Lean's
  builtin operators are deferred nodes, not requirements, so they need their own test. Upstream's
  root pass has no counterpart for named functions, whose root type holds no variable.
- **Numeric patterns** default to `uint256` before literals do, so a `match` on an open literal
  makes the literal `uint256`. They are admitted on `word`, `integer` and `uint256`
  (`Detail.supportedIntegerPatternTarget`), as upstream admits them, and range-checked at
  `uint256` by finalization and the compiler.
- **Compound assignments on an open target** (`compoundTakesTargetType`) share the target's type
  with the operand, as upstream's rewrite to `x = x op e` types them. So `let x = 0; x -= 1;` is
  `uint256` and panics with `0x11`. Finalization rejects a target that becomes `integer`, or that
  nothing fixes, with `Error.compoundTargetNotSupported`. Only the typing follows the rewrite: the
  place is still evaluated once.
- **Two older paths** take only `word` and `integer`, so a `uint256` value fails there: the
  monomorphic scalar and function profile (`SourceCoreFunctions.lowerExpressionWithReasons`) with
  `typeProjection`, and `SourceProgramExecution`'s direct linking (`SourceCoreDirectLinking`) with
  `unsupportedType`. The public compiler (`SourceCoreExecution`) uses neither. Extending the
  scalar profile would reach its Word and Integer meaning proofs, so the tests that use these
  paths type their values `Word`.
- **Effect on programs.** Arithmetic on a defaulted literal is checked at `uint256`, so
  `2^256 - 1 + 1 == 0` panics with `0x11`, where it was `true` at `word`.

### Row 1's unchecked arithmetic and its literal operands

- **Typing.** In an `unchecked` block, `+ - * / %` on one of the twelve types are builtins without
  requirements (`BinaryOperatorHasType.fixedUnchecked`), as upstream's `UncheckedAdd` …
  `UncheckedMod` instances are. An open literal operand waits for its type, as a checked
  operator's does (`Detail.binaryDefers`), so
  `unchecked { let a = 200 + 100; let b: uint8 = a; return b; }` is 44. On an `integer` operand the
  operator never waits; it dispatches as on any closed type, or is rejected. Finalization rejects
  one whose left operand became `integer` (`Detail.validateUncheckedOperand`), with
  `operatorNotSupported` and the trait's name.
- **Meaning.** The exact result wrapped to the type's width (`Dynamic.fixedWrap`) as a canonical
  word (`FixedBinaryApplies.unchecked`, `uncheckedDivision`). `MIN / -1` wraps to `MIN`, and a zero
  divisor panics with `0x12` by `BinaryPrimitivePanics`. The five operators are in `FixedBinaryOwn`
  on all twelve types, so the rules choose the meaning from the operands' static type alone.
- **Lowering.** `uncheckedBody` (the exact result as a Core Integer, wrapped by
  `fixedWrapInteger`) and `uncheckedDivisionBody` (the zero test, `truncatedDivision`, the wrap).
  The meaning proofs cover both (`BinaryProfile.fixedUnchecked`, `fixedUncheckedDivision`).

### Row 1's unchecked compound assignments: the wrap belongs to the leaf

- **Typing and semantics.** `+= -= *= /= %=` in a block take the target's type, as the checked
  forms do, and an open target defaults as above. `CompoundAssignmentApplies.uncheckedAdd` …
  `uncheckedModulo` apply `FixedBinaryApplies` of the binary operator, so the result wraps.
  The meaning proofs take them through `FixedCompoundAssignment`, as they take the checked forms.
- **Lowering.** `assignmentModifier` gives them Word's operation (`checkedWordOperation`) with
  `fixedCheck`: no check for `+= -= *=`, and the zero test for `/= %=`. Word's operation keeps the
  low `N` bits, so the modified leaf is wrapped before the setter writes it. `modified` and
  `execute` take an optional last argument `wrap` (`none` by default), and `wrapLeaf` masks the
  leaf (`wordAnd`) on an unsigned type or sign-extends it (`wordSignExtend`) on a signed one.
  `lower` passes `placeWrap`, and `CompatibleBareAssignment.of_lower` states it.
- **Rejected: the wrap in the guard's `Check`.** It would keep `of_lower`'s text. But the wrap
  belongs to the leaf the setter writes, while `Check` is the post-setter guard that decides a
  panic. It would also change `guard_inv`, `inv_sized` and `Passes` and about 40 of their callers,
  with no gain in a public statement.
- **Proofs.** Statements written without the argument elaborate with `none` and keep their text.
  Under the plain profiles `placeWrap_plain` gives `none`, and the receipts state `placeWrap`.

### Row 1's shifts on the twelve types: the amount takes its own type

- **Typing.** The value is `word` or one of the twelve types, and the result takes its type. The
  amount is typed on its own: `word` or an unsigned type (`ShiftAmountType`), as upstream's
  `ShiftAmount` instances, so `uint8 << uint256` is accepted. `ExpressionFormHasRawType.binary`
  takes the two operand types separately; every other operator rule keeps one, and so do user
  trait shifts (`BinaryOperatorHasType.trait`), which are out of scope.
- **Open literals** wait, as upstream's obligations do, and default to `uint256`. So
  `let a = 1 << 256;` is 0, and `x << -1` is out of `uint256`'s range, as upstream has it.
  Finalization rejects any other value or amount type (`Detail.validateShiftOperands`), a signed
  amount and a lambda parameter that only a shift types included.
- **Meaning and lowering.** `FixedBinaryApplies.shiftLeft` is Word's shift read at the type, and
  `shiftRight` is Word's or, on the signed types, the arithmetic one. `shiftLeftBody` runs
  `wordShl` then the type's wrap, and `shiftRightBody` runs `wordSar` or `wordShr`. `BinaryProfile`
  has `wordShift` and `fixedShift`, so the fixed-width shifts are in the meaning proofs.
- **Compound shifts** type as upstream's rewrite to `x = x << n` types them
  (`SourceAssignmentHasType.shiftCompound`). At a fixed-width target `<<=` writes back through
  the leaf wrap, and `>>=` without one. At both a `Word` and a fixed-width target the amount
  keeps its own type, through `AssignedRhsView`, and at a fixed-width target it need not be
  canonical for the target's type (`fixedShiftAmount`). So `w <<= 3` and a `uint8` `r <<= 1`,
  whose amounts are `uint256`, pass the statement shape check.

### Row 1's in-place `~`: the target keeps its type

- **Typing.** Upstream's parser rewrites `x ~=` to `x = ~x`, so the target keeps its own type and
  takes that type's `BitNot` instance: masked at `uint8` … `uint128`, sign-extended at `int8` …
  `int128`, and Word's at `word`, `uint256` and `int256`. An open target waits and counts as an
  operator use for the default. Finalization rejects a target whose type has no builtin `~`
  (`Detail.validateBitNotTarget`), as upstream defines no `BitNot` on `integer` or `bool`.
- **Meaning.** `BitNotAssignmentApplies` at the target's static type: Word's or Integer's `~` on
  the snapshot (`BitNotSnapshot`), or on `uint8` … `uint128` Word's `~` masked to the low `N` bits,
  which `wrapLeaf` does to the leaf before the setter. Word's `~` alone would not keep a narrow
  target's heap well typed, so the staged rules read the write at `BitNotAssignmentApplies` too.
- **Outside the meaning proofs** at fixed-width targets. The compiler profiles of `~=`
  (`BitNotAssignable`, `ProjectedBitNotAssignable`) take only a `Word` target. `w ~=;` and
  `m[k] ~=;` stay in the compiler body profile that the meaning proofs take, and an `int8` target
  is outside it (`Tests.SourceCoreBitNotSubset`).

### Row 1's conversions: a word becomes a value only when canonical

Chosen by the user, option (a). The rule for `Typedef` is option B.

- **Upstream.** `uint256` is `enum uint256 { uint256(word) }` (`std/std.sol:1010-1012`), and the
  other eleven are one-field structs, `struct uint8 { value: word; }`. `uintN(w)` keeps the raw
  word; only the ABI decoders check it. Outside std, `x.value` on the struct types is rejected
  (`SC0205`), and `case uint256(w)` is accepted.
- **Lean.** A conversion checks the word as the decoders do, so a value of the twelve types stays
  canonical. That is the accepted difference: where upstream keeps a dirty word, Lean reverts.
- **The constructors.** `uint256(w)`, `uintN(w)` and `intN(w)` are builtin functions `word → T`
  (`BuiltinFunctionId.fixedFromWord`), found after the program's own functions. Their argument is
  typed by the parameter, as upstream's constructor's is. A dirty word faults with
  `SemanticFault.dirtyHigherBitsForInteger`, through a direct or an indirect call alike. A
  conversion is no closure, so every program's globals, callable table and closure identities are
  unchanged. It is lowered where it is called (`SourceCoreInteger.conversion`).
- **`Typedef.abs` and `Typedef.rep`.** Upstream's `Typedef<abs, rep>` has the identity as its
  default instance, and each of the twelve types has an instance whose `abs` is its constructor
  and whose `rep` gives its word. A default is admitted only when no other instance head can unify
  with the goal. So `abs` takes its type from its context, and `rep` gives `word` at the twelve
  types.
  - In Lean they are builtin calls when no local and no source namespace is named `Typedef`. The
    function is chosen at the call (`typedefFunction`): `Typedef.abs(e)` by the expected type the
    call is inferred against (an annotated `let`, a `return`, the right side of `=`), and
    `Typedef.rep(e)` by `e`'s inferred type.
  - At `word` either is the identity. At the twelve types `abs` is the type's conversion and `rep`
    the value's word (`BuiltinFunctionId.fixedToWord`).
  - Any other type, and a type still open at the call, is rejected with
    `operatorNotSupported "Typedef" τ`. So `take(Typedef.abs(w))` and `Typedef.rep(5)` are
    rejected. The typing is upstream's wherever both accept.
- **`case uint256(p)`** at a type that is `uint256` or still open unifies the type with `uint256`
  and matches `p` against the value's word (`MatchPatternInstruction.uint256Word`), so it is
  irrefutable exactly when `p` is. At any other type it is an ordinary constructor pattern and is
  rejected, as upstream rejects it.
- **The revert.** `SourceCorePanics.dirtyReason` is the word just below the panic range, and the
  fault-site tables allocate below it. The decoder gives `RuntimeError.dirtyHigherBitsForInteger`,
  and `SourceCorePanics.dirtyRevertData` is upstream's `0x6cc54a63`. It is a Frontend convention,
  as the panics are.
- **In the meaning proofs.** On the accepted-body route every conversion is a nested site, with
  the revert's token law (`CellAwareInvocationAcceptedConversionFaults.DirtyToken`); the older
  families' builtin calls still exclude conversions (`function.conversion? = none`).
  `Typedef.rep` at the twelve types runs its argument's code, and the argument's representation
  gives the canonical word. `case uint256(p)` needs no exclusion: the pattern proofs take it as
  `p` at the value's word (`Tree.uint256Word`).

## Differences from upstream

Four differences remain:

1. **Conversions revert on a dirty word.** `uint256(w)`, `uintN(w)` and `intN(w)` revert with
   `DirtyHigherBitsForInteger()` on a word that is not canonical for the type, where upstream's
   keep the raw word. This is accepted.
2. **A `Typedef` call needs its type known at the call.** Lean rejects one whose type is still open
   there, as in `let a = Typedef.abs(w); let b: uint8 = a;` or `Typedef.rep(5)`, where upstream's
   instance resolution waits for later uses. This is a gap, not a permanent difference: a `Typedef`
   constraint solved at finalization (option A) could lift it, as an unscheduled unit of its own.
3. **A `where` clause cannot name the builtin `Int`.** Lean reports `unknownTrait "Int"`. So
   upstream's `poly_int_defaulting` stops at its signature in Lean, where upstream reports the
   literal as ambiguous. The gap is older than row 1.
4. **Local lambdas are generalized** at their `let`, where upstream keeps a closure monomorphic. So
   a compound assignment, a shift or an in-place `~` on a parameter that neither the lambda's body
   nor a literal types is rejected in Lean, as in `lam(acc, step) { acc += step; return acc; }`, as
   `acc + step` already was. A captured `Word` operand, a declared `acc: Word` or a literal operand
   types it. This also predates row 1.

The note also records these contrasts with upstream:

- An `unchecked` block needs no import: Lean has no std, so upstream's required import has no Lean
  counterpart.
- `SourceInference.inferExpression`, which checks an expression on its own, rejects a lone open
  literal as ambiguous, where upstream's root pass gives it `uint256`. Nothing in the repository
  calls it.
- Unary minus and shifts on a declared type are rejected: Lean's `Int` is builtin, and its operator
  traits take one parameter, where upstream's `Shl<t, n>` and `Shr<t, n>` take two.
- `Typedef`'s identity at other types is rejected: upstream accepts `let c: bool = Typedef.rep(b)`.
  That identity is generic code, which row 1 leaves out.
- A panic is a failure with a diagnostic, and a non-canonical argument a data-conversion error,
  rather than revert data. This is a choice about Lean's API, which has no calldata and no revert
  channel; which programs panic, and with which code, follows upstream.

Not differences: `x.value` on the twelve types, and numeric and constructor patterns at the eleven
struct types, such as `case uint8(w)`, are rejected as upstream rejects them.

## What remains

- **Meaning proofs.** One part is compiled but outside the meaning proofs: in-place `~` at
  fixed-width targets, whose compiler profiles take only a `Word` target.
- **Deferred `Typedef` resolution** at finalization (option A). It is not scheduled.
- **`where` with the builtin `Int`**, a frontend gap older than row 1.
- **Generic code**, such as `Typedef`'s identity at other types, which row 1 leaves out.
- **Two-parameter operator traits**, for shifts on declared types.
- **The two older lowering paths** that take only `word` and `integer`.
- **Unported fixture functions:** those that need contract storage.
- **Out of scope:** conversions between two integer types; `pragma solcore;`, which is row 5; and
  reads of uninitialized locals, which Lean keeps faulting on by decision
  ([closure capture by value](../guide/source-semantics.md#closures-capture-by-value)).
  Conversions between `word` and the integer types were first out of scope, as upstream's are std
  functions; row 1 added them.
