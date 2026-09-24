# ADR-0301: recursive strict Word binary data-image bridges

## Status and baseline

Design for the smallest extension of the existing exact data-image contracts.
Prototype adoption, actual owned-declaration review and complete formal tests
are separate required gates. The baseline is completed ADR-0300 at
`336fbb0bb381792c960f86093cd2c306b5042497`.
Canonical Rust stays at `18fd9f75d290df0070e21ee56e0a5691f232596f`.
Diagnostics/parser proofs remain paused and eight existing untracked Syntax
files are preserved. All working evidence stays in .lake/trace-audits.

## Syntax admission and unchanged public contracts

Append one generic strictWordBinary constructor to ClosedSourceDataExpression.
Its two original children must be admitted, and its operator must differ from
logicalAnd and logicalOr. The expression gate grows from eleven to twelve forms.
The seven-form body gate is unchanged and recursively uses this expression gate.
Admission includes no runtime value, Word typing, successful execution, resolver
output or primitive meaning premise. Original source ranges remain literal.

Only the private reflect/embed proofs in ClosedSourceDataExpressionProperties
change. Reflection first recovers the actual left Word and complete middle
store through ofCore injection, then the actual right Word and full final store.
The fourteen independent meanings select the existing Local rules. Embedding
uses those Local child derivations and original primitive constructors directly.
Logical cases are excluded by their explicit operator disequalities.

All six public expression/body/invocation/application image statements and
their public proof bodies are kept literally unchanged. Four production
body/invocation/application files remain whole-byte unchanged in the formal tree.
Their prototype copies change imports only. The original seventeen expression
and nine body rules, runner, strict primitive foundation, DirectWordBinary,
Local costs, ordered less-than lowering and existing checking APIs do not change.

## Independent expression and boundary consumers

An independent symbolic consumer covers all fourteen operators with arbitrary
Words and ranges, a grouped bit-not left child and grouped reference right child.
First-match lookups permit duplicate spellings/IDs and opaque Core rows/stores.
The original evaluation and Local costs are constructed before machine paths
and either public image direction. Every actual value and full final store is
retained, with no whole-environment typing premise. Child costs three and one
compose with the existing strict overheads three/five/nine/eleven, separately
from the source runner's recursive depth.

The old raw fourteen-operator symbolic consumer changes only its final gate
exclusion to admission; original evaluations, mixed inputs and full endpoint
claims remain intact. The old short-circuit boundary consumer gains only the
new impossible strict/logical inversion cases.

Admission still implies neither success nor whole name resolution. Non-Word
or missing operands can be admitted but exclude every successful endpoint.
An explicit zero on either side does not skip the opposite missing operand.
Original identity-lambda creation, body evaluation and a strict call operand
are built independently and can succeed while their lambda/call syntax remains
outside the data gate. Thus the gate is not the maximal dynamic overlap.

## Body, direct application and actual saved invocation

The expected-Bool fixture binds a fresh p from p + 1, then returns
!(p < 2) && (p >= 2). The expected-Word fixture binds the same initializer,
then returns (p < 2) ? p * 2 : ~p. Direct arguments use c + 1.
Independent original and Local body witnesses precede all four body/application/
invocation contracts. Core paths are composed from existing child costs, not
obtained from the image theorem being exercised.

Saved inputs retain their existing ordered unique typed-ID context, while the
corresponding Core payloads may be opaque and need not inhabit those types.
Actual runtime caller rows can contain duplicates and foreign identities.
Creation's returned source closure supplies its original syntax, saved owner,
names and captures. Actual callee, argument and body results feed the original
call rule, including complete intermediate/final stores and fresh p shadowing.
No identity between source closures and Core closures is asserted.

## Parsed checks and cost boundaries

Fourteen operator spellings, five boundary Word pairs and two Core stores yield
140 grouped-reference checks. Raw rows and stores are explicitly the ofCore
images of those same Core inputs, unlike ADR-0300's separate raw/Core fixtures.
The actual complete AST, seven handwritten ranges, EOF and zero diagnostics
are checked before proof consumers. Inner depth two and group depth three have
all-budget laws and adjacent runner checks; Core costs are tested separately.

The Bool and Word lambda suites each cover five boundary Words and two stores,
including both branch outcomes, wrapping, unsigned high-bit values and opaque
old p payloads. Actual full parsed trees and handwritten nested ranges connect
the proof fixtures to the parser's returned syntax. Direct calls and foreign
saved invocations retain actual outputs and whole final stores.
Body/call depth annotations seven/eight for Bool and six/seven for Word are
finite fixture checks, not universal cutoff theorems. Core costs remain distinct.
No parser implementation, parser-correctness theorem or diagnostic proof changes.

## Verification and publication

Freeze complete prototype sources, literal import reversals and old public
headers before adoption. Inspect actual old/prototype/formal owned declarations,
raw types, flags, dependencies and full public logical closures. Any port-only
name mapping must be explicitly reviewed; numeric atoms are not normalized.
Retain ordered historical source and selected generated-declaration catalogs,
append actual new names and the single new gate constructor, and check axioms.

Require focused and existing-client builds, complete frontend/syntax/test builds,
new and retained parsed suites, full tests, and kernel-policy and whitespace
checks.
Each proof source stays below 300 lines. Keep design, grammar, private proofs,
individual consumers, registration and docs in separate small commits.
No runtime-typing shortcut, canonical dispatch, effects, general state-changing
prefix theorem, closure conversion, fault classifier or whole-language totality
is introduced.
