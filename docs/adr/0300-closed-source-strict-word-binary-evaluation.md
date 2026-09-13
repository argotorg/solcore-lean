# ADR-0300: original closed strict Word binary evaluation

## Status and baseline

Accepted design after independent proof and consumer review.
Parsed prototypes passed independent repetition: 140 grouped-reference cases
and 56 saved-call cases. Formal adoption and aggregate verification remain
separate required gates. Baseline is completed ADR-0299 at
`b79cb0ba6ede4c06058635a661473507a27b9f4c`.
Canonical Rust stays at `18fd9f75d290df0070e21ee56e0a5691f232596f`.
Diagnostics and parser proofs remain paused; eight existing untracked Syntax
files are preserved. Working evidence stays under .lake/trace-audits.

## Independent primitive meaning

Add StrictWordBinaryDenotes over Syntax.BinaryOp, two actual Core.Word inputs
and a Core.Value result. Fourteen independent constructors cover addition,
subtraction, multiplication, division, remainder, bitwise and/or/xor, unsigned
greater/less/equal/not-equal/less-equal/greater-equal. Eight produce Words and
six produce Booleans. Meanings use existing Word primitives and comparisons,
not source resolution, lowering or the bounded source runner.
Wrapping and zero results for division/remainder by zero retain the fixed Lean
primitive profile. This does not implement canonical Rust named dispatch.

A separate total evaluateStrictWordBinary? agrees exactly with that relation.
The two logical operators return none. Four public properties give exact
success, result uniqueness, logical-operator exclusions and exact support.
Do not extend DirectWordBinary: its ten forms describe direct Core lowerings,
whereas the four other strict operators have existing composite lowerings.

## Original judgment and execution

Append one strictWordBinary constructor to ClosedSourceExpressionEvaluates,
growing its sixteen clauses to seventeen without changing their order.
Keep all nine body clauses unchanged. The new rule requires the actual left
Word evaluation, then the actual right Word evaluation at the complete left
final store, then independent strict meaning. Its endpoint is RuntimeValue.ofCore
of the actual primitive result and the complete right final store.
Source ranges, lexical owner and ordered names/captures remain literal.

The runner adds one common binary branch after the two logical branches.
Both operands receive the predecessor budget. The right starts at the actual
left final store; no Word value, including zero, skips the other operand.
Failure still does not distinguish depth exhaustion, missing lookup, wrong
runtime payload or unsupported syntax. This is not a fault classifier or a
termination theorem for every source expression.

Compatibility, determinism, soundness, eventual completeness, monotonicity
and threshold contracts retain their ordinary public headers. Only necessary
induction/inversion cases change. Actual generated mutual eliminators and runner
equation artifacts are inspected separately; their types need not stay fixed.
Four short-circuit law headers and both logical behaviors remain unchanged.
New strict meaning is impossible in the logical inversion cases.

Two public laws expose exact strict decomposition and the predecessor runner
equation, with explicit exclusions of logicalAnd/logicalOr. An independent
consumer proves the all-budget cutoff max(Dleft,Dright)+1 from exact child
cutoffs at the actual intermediate store. This is source derivation depth,
not Core transition cost or a claim about arbitrary state-changing prefixes.

## Preserve existing data and cost boundaries

The expression/body data gates remain eleven/seven forms. All six existing
expression/body/invocation/application image statements and their public proof
bodies remain literal. Only two impossible private expression-reflection cases
are added. Four alias-only body/invocation/application/threshold prototype files
remain whole-byte unchanged in the formal tree. Strict raw success is outside
the unchanged expression gate; admission, resolution and execution stay distinct.

No Local cost rule or ordered less-than lowering changes. Independent consumers
construct all fourteen Local costs before machine correspondence: direct ten
add three transitions, != and <= add five, < adds nine, and >= adds eleven.
The proof retains arbitrary child costs, all three stores and every continuation.
This does not identify source closures with Core closures or type opaque tails.

## Independent consumers

Symbolic references use arbitrary Word operands, source ranges, first-match
lookups, mixed captures and complete stores without uniqueness/runtime-typing
premises. All fourteen original witnesses precede both decomposition directions
at every actual value and final store. Non-Word and missing references on either
side exclude every successful original endpoint. Explicit zero operands still
cannot hide a missing opposite operand.

Saved-call consumers independently construct actual creation, callee, argument,
body, call and binary evaluations. The actual returned closure supplies all
four saved fields through foreign caller rows and fresh-parameter shadowing.
They allow duplicate rows and mixed opaque payloads. These particular prefixes
preserve stores; they do not prove an extra state-changing-prefix theorem.

Parsed grouped-reference tests cover fourteen explicit spellings, five Word
pairs and two independent raw/Core stores: 140 fixtures. They check the actual
whole AST, all seven handwritten ranges, EOF and zero diagnostics. Independent
original closed and Local-cost proofs precede machine observations. The actual
inner binary has depth two and its group depth three, each checked at zero,
one below, exact and three above. Core costs are checked separately, including
actual full outputs and exact exhaustion. Word pairs cover zero divisors,
ordinary arithmetic, wrapping and unsigned high-bit boundaries.

Parsed saved calls cover all fourteen spellings on both sides with two value/
store fixtures: 56 cases. Actual parsed lambda creation feeds the returned
closure through caller evaluation to the saved body. Creation/call/binary depth
annotations one/three/four have adjacent checks; they are not universal cutoff
theorems. Source spellings include spaces around operators because the existing
lexer rejects identifier-internal hyphens. No parser implementation or proof
changes, parser-correctness claims or diagnostic guarantees are introduced.

## Verification and publication

Freeze every complete source/header and exact prototype import reversal before
formal adoption. Require each proof source below 300 lines. Register the three
new production modules, seven consumers and two parsed IO tests. Only two old
consumer proofs require the newly added impossible/inductive cases.

Preserve complete ordered historical declaration catalogs, append actual new
public names and constructors, and query standard axioms. Inspect actual owned
declarations for the changed raw judgment/runner and new meaning modules with
full raw types, flags, dependencies and public logical closures. Do not guess
generated names or normalize numeric binder atoms. Generated runner recursion
helpers are acceptable only where independently shown absent from every public
logical closure; authored proof escapes remain forbidden.

Require focused and direct-client builds, complete frontend/syntax/test builds,
retained and new parsed tests, full tests, kernel policy, metadata and whitespace
checks before completion. Keep design, meanings, execution, individual proofs/
consumers, registration and documentation in separate small commits.
No effects, global resolution, general runtime typing, closure conversion,
whole-frontend totality or canonical compiler-correctness claim is added.
