import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! The actual match statement retains its source-ordered selection and only the
suffix reached after fallthrough. Every child has its original strict grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
open Frontend SourceInference Staging.Recursive

theorem match_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ matchSize value,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.returned value) after) ∨
    (∃ matchSize failure,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.fault failure) after) ∨
    (∃ matchSize,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .breaking environment ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.breaking environment) after) ∨
    (∃ matchSize,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .continuing environment ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.continuing environment) after) ∨
    (∃ matchSize tailSize middle,
      size = Size.stepSize [matchSize, tailSize] ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.fallthrough environment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .matchWith resolution := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _ | letFault actual same _ _
  | assignBare actual same _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | matchReturned actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, matched⟩
  | matchFault actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, rfl, rfl, rfl, matched⟩)
  | matchBreaking actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inl ⟨_, rfl, rfl, rfl, matched⟩))
  | matchContinuing actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inl ⟨_, rfl, rfl, rfl, matched⟩)))
  | matchFallthrough actual same matched next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr ⟨_, _, _, rfl, matched, next⟩)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
