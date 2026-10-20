import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledTopLevelInitializerContinuation
import Solcore.Frontend.SourceInference.ForHeaderInferenceContinuation

/-! Actual original for-header initializers reach the same selected finalizer,
including the condition, body, post items and later top-level statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem ForStatementInferenceContinuation

structure HeaderInitializerContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.ForItem) where
  inferenceContext : SourceInference.Context
  original : StatementNode
  originalPresent : .statement original ∈ selected.body.body.state.nodes
  header : HeaderContinuation inferenceContext source selected.body.body.state original
  finalContinuation : header.receipt.ready.InferenceProgress selected.body.resources.finalState

namespace HeaderInitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.ForItem}

theorem substitution (continuation : HeaderInitializerContinuation selected source) :
    selected.body.finalized.substitution.SemanticallyExtends
      continuation.header.receipt.ready.inference.substitution := by
  rw [selected.body.resources.substitution_eq]
  exact continuation.finalContinuation.substitution_extends

theorem no_capture (continuation : HeaderInitializerContinuation selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution
      continuation.header.receipt.binding.1 := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement continuation.original, ?_, continuation.header.retained⟩
  change .statement continuation.original ∈ selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact continuation.originalPresent

end HeaderInitializerContinuation

theorem BodySelection.topLevelForHeader {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement}
    (statementPosition : selected.signature.source.value.body.value[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderInitializerContinuation selected source) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) formation canonical progress.returnBelow
    selected.body.inferred statementPosition
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted statementForm accepted
      obtain ⟨header⟩ := receipt.initialized_header occurrence.ready formation canonical
        (progress.returnBelow.weaken occurrence.before.next_le) isPost position form
      let continued := header.continuation.trans occurrence.continuation
      exact ⟨{
        inferenceContext := _
        original := _
        originalPresent := occurrence.retained.subset receipt.recorded
        header := {
          childFuel := header.childFuel, entry := header.entry, result := header.result,
          receipt := header.receipt, ready := header.ready, continuation := continued,
          retained := header.retained }
        finalContinuation := continued.trans (progress.returnUnification.trans progress.finalization)
      }⟩

/-- Compiler success supplies one original check for all actual for-header
positions of the selected function. -/
theorem compile_top_level_for_header_continuation {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {statementIndex : Nat} {statement : Syntax.Statement},
        selected.signature.source.value.body.value[statementIndex]? = some statement →
        ∀ {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
          {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan},
          statement.value = .forLoop headerSpan initializers condition post body →
          ∀ (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem},
            (if isPost then post else initializers)[headerIndex]? = some source →
            ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
              source.value = .letDecl name annotation (some initializer) →
              Nonempty (HeaderInitializerContinuation selected.toBodySelection source) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected, ?_⟩
  intro statementIndex statement statementPosition initializers post condition body headerSpan statementForm
    isPost headerIndex source position name annotation initializer form
  exact selected.toBodySelection.topLevelForHeader (SourceCoreCompiler.compile_checked_source accepted)
    statementPosition statementForm isPost position form


theorem Selected.topLevelForHeader {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement}
    (statementPosition : selected.signature.source.value.body.value[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderInitializerContinuation selected.toBodySelection source) :=
  selected.toBodySelection.topLevelForHeader checked statementPosition statementForm isPost position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
