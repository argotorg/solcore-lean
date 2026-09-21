# ADR-0344: Staged integer and modular Word-literal foundation

## Status

Implemented as a prerequisite for target-compatible `Int.fromInteger`
specialization.

## Context

The pinned reference revision
`argotorg/solcore@1d490d8bb5f374356f06e0720655496482eb1fb4`
does not assign every expression literal the runtime type `word`.  It first
represents the payload as an arbitrary-precision `integer`, then specializes
the builtin `Int.fromInteger : integer -> a` operation for the selected result
type.  The primitive Word instance uses mathematical reduction modulo
`2^256`.

The existing Lean frontend has two intentionally narrower mechanisms.  Its
old local-expression adapter projects only in-range spellings to Word, and its
whole-program inference prototype uses the non-target `FromLiteral`/`Numeric`
convention.  Reusing either mechanism as the meaning of `Int.fromInteger`
would incorrectly reject overflow or erase the required conversion choice.

## Decision

Add a distinct source builtin type `integer`.  Only the exact lowercase
spelling is intrinsic.  It has the lowest unqualified lookup priority:
generic parameters, local types, visible imported types, and the existing
no-import whole-program compatibility lookup all take precedence.  An
unrelated declaration which is not visible does not hide the intrinsic.
`integer` has arity zero; `Integer` and applications such as `integer<Word>`
remain errors unless a visible user declaration gives them another meaning.

`integer` is staged.  It is retained by source type checking but has no
`Core.Ty` projection.  If an integer parameter, result, local, or other value
survives to `SourceCoreElaboration.lowerType`, lowering rejects it explicitly
as an unsupported type.  A later specialization or compile-time evaluator
must remove it before runtime Core.

Keep the existing strict `interpretWordLiteral?` operation unchanged for the
legacy monomorphic adapter.  Add a separate
`interpretWordLiteralModulo?` operation for the future primitive Word
`Int.fromInteger` specialization.  Both use the same whole-spelling,
arbitrary-size natural decoder, but the new operation maps a valid value with
`Core.Word.ofNatModulo`.  Consequently `2^256` maps to zero instead of being
rejected.  Malformed decimal, hexadecimal, and string payloads still fail.

The modulo operation has its own independent `ModuloWordLiteralDenotes`
relation and executable soundness, completeness, exact-failure, and
span-independence laws.  It does not weaken the strict relation or silently
change any existing expression adapter.

## Deferred boundary

This ADR does not yet:

- introduce the builtin `Int` class or its `word` and `integer` instances;
- change whole-program literal inference or its current compatibility tests;
- attach `Int.fromInteger` selection and evidence to typed literal nodes;
- execute the modulo helper from Source Core or the public source pipeline;
- represent negative compile-time integers or evaluate `integerAdd`,
  `integerSub`, or `integerMul`; or
- execute user-defined `Int` instances.

The next step is a collision-free sum identity for source and builtin
trait/implementation evidence.  Literal inference can then retain an exact
`integer -> target` conversion plan, and Source Core can consume the builtin
Word plan without ever emitting `integer` at runtime.

## Verification

Regression tests cover exact lowercase resolution, arity and case errors,
local/import/global compatibility shadowing, an unrelated unimported
declaration, source checking followed by explicit Core rejection, strict
overflow rejection, modulo `2^256 -> 0`, malformed payload rejection, and
span independence.  All new definitions remain executable and use no authored
axioms or proof placeholders.
