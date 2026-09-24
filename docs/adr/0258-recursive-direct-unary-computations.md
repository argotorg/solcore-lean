# ADR-0258: Recursive direct unary computations

Status: Accepted
Date: 2026-09-09

## Context

ADR-0257 admits recursive calls, direct Word binaries and conditionals through
one child profile. Prefix operators still use the old pure fallback, so their
operands cannot contain these newly supported calls.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
`crates/parser/src/parse/expr_pat.rs:243-255` parses original prefix operators
in right-nested order around the original postfix child.
`crates/parser/src/lower/body.rs:263-277` retains that child and operator span.
`crates/hir-ty/src/infer/expr.rs:1521-1546` dispatches `!` through the named
`not` function and `~` through `BitNot.bnot`. This change keeps the established
fixed Bool/Word interpretations of ADR-0158 and ADR-0161; it does not claim to
implement that general function/class resolution mechanism.

## Decision

Extend the existing recursive checker at each of the two canonical unary roots.
Check the original operand in the same caller scope. Logical negation requires
Bool and returns Bool; bitwise complement requires Word and returns Word.
Emit the exact existing Core unary boolNot or wordNot around the original child
Core. Preserve outer and operator spans and right-nested prefix order. Do not
rewrite source unary syntax into a call, binary operation or synthetic body.

Add logicalNot and bitNot constructors to each independent typing, elaboration,
raw evaluation and cost judgment. Static rules need only original child evidence.
Raw rules require the actual child Bool or Word, not its static tag, and preserve
the child's actual final store. Apply Boolean negation or the existing 256-bit
Word complement exactly once. Cost is child cost plus two transitions.
Invalid actual payloads can fault after child effects; an earlier child fault
prevents reaching unary application. Neither case supplies a successful raw cost.

Retain every old constructor and success. Old pure and new recursive unary
derivations overlap; reconcile them privately, including raw child success that
skips unsupported syntax even though whole checking rejects it. Do not introduce
a global call-free or whole-checking premise into raw correspondence.

Extend the recursive caller fragment with one generic Core unary constructor.
Its same-cutoff weakening, raw insertion and paired paths reuse the actual child
value/store and the same primitive application. Choose one child cost before
every continuation, then add two. The Core fragment may contain existing unary
primitives not selected by canonical source syntax; source elaboration still
selects only boolNot and wordNot.

## Contracts and integration

Keep all fourteen recursive theorem signatures and the direct-binary map law
unchanged. Add nine constructors, not a new operator map, checker family or
wrapper-theorem family. Reuse shared body and explicit-entry implementations
without edits. Keep unary checker/cost inversions private and reuse existing
Core unary path composition.

Audit existing rejection fixtures explicitly. Promote only original well-typed
unary examples to independent exact success with the same source text. A logical
negation of a Word, complement of a Bool, unknown name or genuinely unextended
root must remain rejected. Old pure and nonrecursive endpoints still reject
recursive unary children. Preserve existing pure unary observations and all
earlier conditional/binary/call cases.

## Validation and limits

Use parsed prefix spans, nesting and precedence; independent original source
typing/elaboration and raw/cost proofs; and separately fixed Core, values,
stores and manual paths. Exercise both Bool values, Word zero/maximum/other
values, nested/double operators, recursive and conditional operands, computed
callees and operand effects. Preserve full entry return tags, wrong-payload and
missing-store faults, genuine saved unaryApply frames and exact resumption.
Use the existing recursive, body and entry laws directly, including arbitrary
caller-slot insertion and actual closure/capture preservation.

Keep proof and consumer files below 300 lines, splitting internal implementation
only when necessary without exporting helper laws solely to cross file boundaries.
Run focused, aggregate and full tests, complete standard-axiom audits, kernel and
whitespace checks, and independent reviews before publication.

Expanded comparisons, lazy Bool roots and tuples do not gain recursive children.
Source lambda construction, global function/class resolution, general early
returns, unfuelled execution, source-only bounds and arbitrary-store safety
remain separate. Parser, Core machine, diagnostics, and Core Wire do
not change.
