import Solcore.Frontend.RustHull.PublicFunctionCorrespondence
import Solcore.Frontend.RustHull.ParameterRenamingCorrespondence

/-! Real function bodies retain their source meaning under the administrative
renaming introduced by global closure installation. Parameter cells are still
derived from the supplied values and the actual initializer. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence ScalarExecution

theorem lowerFunction_body_renamed {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures external statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (heapRelated : HeapRel world initial.heap store)
    (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result sourceResult targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift)
        targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  cases sourceEvaluated with
  | arity mismatch => obtain ⟨value, same⟩ := normal; contradiction
  | body bound sourceExecuted =>
      rename_i allocated sourceEnvironment control
      have controlNormal : NormalControl control := by
        obtain ⟨value, same⟩ := normal
        cases control <;> first | trivial | simp [Semantics.finishFunction] at same
      obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
      obtain ⟨statements, statementsCompiled, bodyShape⟩ := lowerFunction_components compiled
      have bodyEqual := Core.Expr.lambda.inj bodyShape
      rcases bodyEqual with ⟨_, _, rfl⟩
      have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
          mapping.lift (bundleValues targets :: environment) := by
        intro name sourceLocation binding index found looked
        simp [Semantics.lookupLocation] at found
      obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
          sourceBound, cells, parametersRelated, allocatedHeap, allocatedExternal⟩ :=
        initialize_parameters_renamed values arity emptyEnvironment heapRelated externalRelated
          (fun _ _ _ _ hypothesis => frame.allocate hypothesis)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
      obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalExternal⟩ :=
        straight_line_body frame resultCompiled statementsCompiled eligible sourceExecuted controlNormal
          parametersRelated allocatedHeap allocatedExternal
      have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
        (mapping := mapping.lift) rfl
        (fun index value found => by simpa only [Nat.zero_add] using found) executed
      refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalExternal⟩
      · simpa only [parameterCode, values.length.2] using initialized
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.StatementCorrespondence
