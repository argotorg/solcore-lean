import Solcore.Frontend.SourceTypedRuntimeDeepSafety

/-! Audit of the existing typed-source input predicate.  These theorems
describe its current domain; they do not strengthen that domain or certify
source lexical typing.  In particular, readable captures alone do not ensure
that the binders needed by a checked closure body are present.  The public
runner also applies `validateTypeFuel`, which rejects raw closure inputs;
this predicate gap alone therefore does not exhibit an admitted bad call. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary

open Frontend Frontend.SourceInference TypeSystem
open Frontend.SourceTypedRuntime

/-- The public runner's earlier structural input check rejects raw closures.
Thus replacing a readable capture list does not make such a public input
admissible, even though the subsequent deep-safety predicate accepts it. -/
theorem validateTypeFuel_closure_notValid
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan) (expected : Ty)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (captured : SourceTypedRuntime.Environment) (evidence : RuntimeEvidenceEnvironment) :
    (Value.closure parameters resultType body source owner captured evidence).validateTypeFuel fuel signatures plan expected ≠ .valid := by
  cases fuel with
  | zero => intro impossible; cases impossible
  | succ fuel =>
    rw [Value.validateTypeFuel.eq_12] <;> simp

theorem capturesReadable_empty (state : RuntimeState) :
    CapturesReadable state [] := by
  intro binding member
  cases member

/-- Code/evidence authenticity and the outer function type survive arbitrary
capture replacement, as long as every replacement location is readable. -/
theorem deeplySafe_replaceCaptures
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {parameters : List TypedBinder} {resultType expected : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {captured replacement : SourceTypedRuntime.Environment}
    {evidence : RuntimeEvidenceEnvironment}
    (safe : (Value.closure parameters resultType body source owner captured evidence).DeeplySafe signatures plan state expected)
    (readable : CapturesReadable state replacement) :
    (Value.closure parameters resultType body source owner replacement evidence).DeeplySafe signatures plan state expected := by
  refine ⟨?_, ?_⟩
  · cases safe.typed with
    | closure outer expected _ => exact .closure outer expected readable
  · cases safe.code_and_evidence with
    | closure valid => exact .closure valid

/-- Thus the legacy predicate cannot imply capture completeness, even for an
otherwise authentic and accepted closure. -/
theorem deeplySafe_emptyCaptures
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {parameters : List TypedBinder} {resultType expected : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {captured : SourceTypedRuntime.Environment}
    {evidence : RuntimeEvidenceEnvironment}
    (safe : (Value.closure parameters resultType body source owner captured evidence).DeeplySafe signatures plan state expected) :
    (Value.closure parameters resultType body source owner [] evidence).DeeplySafe signatures plan state expected :=
  deeplySafe_replaceCaptures safe (capturesReadable_empty state)

/-- The executable validator has the same limited observation: two capture
lists with equal readability checks are indistinguishable to it. -/
theorem isDeeplySafe_capture_observation
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState)
    (parameters : List TypedBinder) (resultType expected : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (captured replacement : SourceTypedRuntime.Environment)
    (evidence : RuntimeEvidenceEnvironment)
    (same : capturesReadable state captured = capturesReadable state replacement) :
    (Value.closure parameters resultType body source owner captured evidence).isDeeplySafe fuel signatures plan state expected =
      (Value.closure parameters resultType body source owner replacement evidence).isDeeplySafe fuel signatures plan state expected := by
  cases fuel <;>
    simp only [Value.isDeeplySafe, Value.hasLocalTypeFuel,
      Value.hasValidCodeAndEvidenceFuel, Value.type?, same]
  rfl

end Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary
