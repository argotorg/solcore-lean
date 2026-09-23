# ADR-0010: M1b Semantic Core Wire v1

- Status: Accepted
- Decision date: 2026-07-23
- Scope: M1b Semantic Core representation and conversion boundary
- Implementation: Complete

## Context

M1a established declarative typing and evaluation, an executable checker and
machine, correspondence theorems, and safety theorems for a closed Semantic
Core fragment. The fragment contains unit, booleans, 256-bit words, de Bruijn
variables, initialized immutable `let`, and conditionals.

That formal model needs a closed, versioned representation whose accepted
values cannot silently widen when the internal Core language grows. Lean
constructor names and implementation-specific encodings are not a suitable
stability boundary by themselves.

## Decision

Define `Solcore.Core.Wire.V1` as the closed representation of the M1a fragment.
It contains only:

- `unit`, `bool`, and `word` types and values;
- unit, Boolean, and Word literals;
- de Bruijn variables;
- initialized immutable `let`; and
- condition-first, selected-branch-only `if`.

A Wire v1 `Program` has an explicit result type and body. It contains no named
data definitions, primitive operators, functions, products, sums, cells, host
functions, or contract-runtime constructs.

Wire values convert to the corresponding Core values totality. Core-to-wire
conversion is partial: a current Core value outside the closed v1 algebra
returns `none`. Growth of internal Core therefore cannot extend Wire v1
implicitly.

## Scalar representation

A Word is encoded as `0x` followed by exactly 64 lowercase hexadecimal digits.
Zero padding is mandatory. Short, uppercase, out-of-range, and numeric forms
are not canonical Word representations.

De Bruijn indices and structural limits are nonnegative natural numbers.
Canonical encoding uses decimal integers without a fractional component or
exponent.

These scalar rules are shared by the v1 conversion and codec tests and remain
stable for the lifetime of the version.

## Structural accounting

Each expression constructor counts as one expression node, and a leaf has
depth one. The Program wrapper, result type, and record fields do not count as
expression nodes or expression depth.

Resource bounds are checked explicitly by callers of bounded conversion or
decoding APIs. A bound equal to the exact demand succeeds; a smaller bound
fails without constructing a partial Program.

## Type checking and evaluation

Wire v1 converts to ordinary Core before checking or evaluation. It does not
define a second type system, evaluator, evaluation order, or fuel policy.
Typing, selected-branch behavior, machine transitions, and safety are inherited
from the M1a Core definitions and proofs.

The five fine-grained M1a features represented by this version are:

- `coreUnit`;
- `coreBool`;
- `coreWord`;
- `coreImmutableLet`; and
- `coreConditional`.

`coreWord` covers the Word type and literals only. Arithmetic, comparisons,
division, shifts, and other operators require later Core versions.

## Compatibility rule

Wire v1 is immutable. New Core constructors and operators must be represented
by a later wire version. In particular:

- `ofCore?` continues to reject every value outside the v1 algebra;
- the meaning and order of existing tags do not change;
- the Word and natural-number canonical forms do not change; and
- later Core versions do not reinterpret an accepted v1 Program.

## Required validation

The implementation is validated by:

- conversion round trips for every covered type, value, expression, and
  Program;
- rejection of unsupported current Core constructors by `ofCore?`;
- acceptance of zero and the maximum Word value;
- rejection of noncanonical or out-of-range Word representations;
- stable unbound-variable, condition-type, branch-type, and result-type
  failures after conversion to Core;
- exact expression node and depth boundary tests; and
- the aggregate build, semantic-kernel checks, and axiom checks.

## Consequences

Wire v1 is a small, durable representation of the completed M1a fragment. Its
partial reverse conversion makes the version boundary explicit, while all
semantic meaning continues to come from the Core model rather than a parallel
implementation.
