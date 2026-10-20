import Solcore.SourceSemantics.SourceCompiledDirectCallOrigins
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! A real statement position retains its actual call and the direct-emitter
progress through its prefix and suffix. Initializer receipts then expose the
same ready state and the exact raw row selected by generalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
open Frontend SourceInference TypeSystem Detail DirectCallEvents

structure StatementCall (context : SourceInference.Context) (source : Syntax.Statement)
    (expected : Ty) (initial final : State) where
  fuel : Nat
  entry : State
  result : StatementResult
  accepted : inferStatementFuel fuel context source expected entry = .ok result
  prefixProgress : Progress initial entry
  suffixProgress : Progress result.state final

/-- This follows the actual list computation, so repeated equal source syntax
cannot select an unrelated call or a different entering state. -/
theorem statementCall_of_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (position : sources[index]? = some source) :
    Nonempty (StatementCall context source expected initial result.state) := by
  induction fuel generalizing sources initial result index with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil => simp at position
    | cons head rest =>
      cases headRun : inferStatementFuel fuel context head expected initial with
      | error error => simp [inferStatementsFuel, headRun, bind, Except.bind] at accepted
      | ok headResult =>
        have headProgress := inferStatementFuel_origins_progress headRun
        cases rest with
        | nil =>
          have same : result.state = headResult.state := by
            simp only [inferStatementsFuel, headRun, bind, Except.bind, pure, Pure.pure,
              Except.pure, Except.ok.injEq] at accepted
            exact (congrArg BlockResult.state accepted).symm
          cases index with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at position
            subst source
            exact ⟨⟨fuel, initial, headResult, headRun, .refl _, same.symm ▸ Progress.refl _⟩⟩
          | succ index => simp at position
        | cons next remaining =>
          cases tailRun : inferStatementsFuel fuel context (next :: remaining) expected headResult.state with
          | error error => simp [inferStatementsFuel, headRun, tailRun, bind, Except.bind] at accepted
          | ok tailResult =>
            have same : result.state = tailResult.state := by
              simp only [inferStatementsFuel, headRun, tailRun, bind, Except.bind, pure,
                Pure.pure, Except.pure, Except.ok.injEq] at accepted
              exact (congrArg BlockResult.state accepted).symm
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at position
              subst source
              exact ⟨⟨fuel, initial, headResult, headRun, .refl _,
                same.symm ▸ inferStatementsFuel_origins_progress tailRun⟩⟩
            | succ index =>
              obtain ⟨found⟩ := ih tailRun position
              exact ⟨⟨found.fuel, found.entry, found.result, found.accepted,
                headProgress.trans found.prefixProgress, same.symm ▸ found.suffixProgress⟩⟩

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) : Origins receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

theorem header_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) : Origins receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- The actual initialized statement, including its annotation choice,
receives ready-state emitter provenance from this very prefix. -/
theorem StatementCall.initialized
    {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial final : State}
    (call : StatementCall context source expected initial final)
    (origins : Origins initial)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source call.entry call.result,
      Origins receipt.ready := by
  have accepted := call.accepted
  cases fuelEq : call.fuel with
  | zero => simp [fuelEq, inferStatementFuel] at accepted
  | succ fuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := LocalLetRequirementTiming.of_initialized_accepted form accepted
    exact ⟨fuel, receipt, receipt_ready_origins receipt (call.prefixProgress origins)⟩

/-- No externally supplied emitter invariant is needed for an actual
position in the initialized original function run. -/
theorem initialized_statement_position
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {owner : Resolved.DeclarationId} {parameters : Environment}
    {comptime : List Bool} {result : BlockResult} {index : Nat} {source : Syntax.Statement}
    (accepted : inferStatementsFuel fuel context sources expected
      (State.initial owner parameters comptime) = .ok result)
    (position : sources[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ call : StatementCall context source expected (State.initial owner parameters comptime) result.state,
    ∃ childFuel, ∃ receipt : LocalLetRequirementTiming.Receipt childFuel context source call.entry call.result,
      Origins receipt.ready := by
  obtain ⟨call⟩ := statementCall_of_position accepted position
  obtain ⟨childFuel, receipt, ready⟩ := call.initialized (initial_origins _ _ _) form
  exact ⟨call, childFuel, receipt, ready⟩

/-- A template in this exact new binder has its actual raw row and call
emitter at the initializer return, before subsequent inference can run. -/
theorem receipt_template_emitter
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins initial) {template : LocalSchemeRequirement}
    (member : template ∈ receipt.binding.1.schemeRequirements) :
    ∃ raw ∈ receipt.ready.requirements,
      raw.id = template.templateRequirement ∧
      template.predicate = applyPredicate receipt.ready raw.predicate ∧
      HasCall receipt.ready.nodes template.templateRequirement := by
  obtain ⟨raw, present, same, predicate⟩ := generalizeValue_requirement_source
    receipt.ready receipt.locals initial.nextRequirement (receipt.ready.resolve receipt.value.type)
    template member
  exact ⟨raw, present, same, predicate,
    SourceCompiledDirectCallOrigins.generalized_template_emitter (receipt_ready_origins receipt origins)
      receipt.locals initial.nextRequirement (receipt.ready.resolve receipt.value.type) member⟩

end Solcore.SourceSemantics.SourceInferenceDirectCallInitializerOrigins
