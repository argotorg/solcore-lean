import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! The actual block retains its scoped body and only the suffix reached after
fallthrough. Lexical bindings are restored; the reached heap is retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
open Frontend SourceInference Staging.Recursive

theorem block_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ innerSize innerContext value,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.returned value) after) ∨
    (∃ innerSize innerContext failure,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.fault failure) after) ∨
    (∃ innerSize innerContext innerEnvironment,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .breaking environment ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.breaking innerEnvironment) after) ∨
    (∃ innerSize innerContext innerEnvironment,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .continuing environment ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.continuing innerEnvironment) after) ∨
    (∃ innerSize tailSize innerContext innerEnvironment middle,
      size = Size.stepSize [innerSize, tailSize] ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.fallthrough innerEnvironment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .block statements := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | breaking actual same | continuing actual same
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _ | letFault actual same _ _
  | assignBare actual same _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | blockReturned actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, _, rfl, rfl, rfl, inner⟩
  | blockFault actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩)
  | blockBreaking actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩))
  | blockContinuing actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩)))
  | blockFallthrough actual same inner next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr ⟨_, _, _, _, _, rfl, inner, next⟩)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
