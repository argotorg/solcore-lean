import Solcore.Frontend.RustHull.ContextualFunctionBodyCorrespondence
import Solcore.Frontend.RustHull.DerivationStatementCorrespondence
import Solcore.Frontend.RustHull.InitializationCoverage

/-! Function initialization and statement steps driven by induction hypotheses
for the particular independent source evaluation. No function rank or premise
quantifying over every source execution is needed at this boundary. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
open Correspondence ScalarExecution StatementCorrespondence DerivationCorrespondence

/-- Initialize the actual function parameters, then consume the induction
hypothesis at the exact source state produced by bindArguments. -/
theorem function_body {σ : Type} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature} {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial allocated final : Semantics.State σ} {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (continued : ∀ {bodyFuel bodyScope result loops expression},
      lowerStatements bodyFuel signatures bodyScope result loops function.body = .ok expression →
      ScopeCoverage sourceEnvironment bodyScope →
      ∀ {world mapping environment store},
      EnvironmentRel world sourceEnvironment bodyScope mapping environment →
      GlobalEnvironmentRel codes locations bodyScope mapping environment →
      HeapRel world allocated.heap store → InstalledGlobals codes locations captured store →
      ∃ extension targetValue finalStore,
        ControlRel result control targetValue ∧
        Core.Evaluates environment store (expression.rename mapping) targetValue finalStore ∧
        HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (covered : ScopeCoverage [] scope)
    (globalsRelated : GlobalEnvironmentRel codes locations scope mapping environment)
    (heapRelated : HeapRel world initial.heap store) (installed : InstalledGlobals codes locations captured store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result (Semantics.finishFunction function.ret control) targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore ∧ ClosuresPreserved store finalStore := by
  have allowed := ContextualStatementCorrespondence.lowerFunction_parameters_allowed compiled
  obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
  obtain ⟨statements, statementsCompiled, bodyShape⟩ := lowerFunction_components compiled
  have bodyEqual := Core.Expr.lambda.inj bodyShape
  rcases bodyEqual with ⟨_, _, rfl⟩
  have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
      mapping.lift (bundleValues targets :: environment) := by
    intro name sourceLocation binding index found looked
    simp [Semantics.lookupLocation] at found
  obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
      sourceBound, cells, parametersRelated, allocatedHeap, allocatedGlobals⟩ :=
    initialize_parameters_renamed
      (external := fun (_ : σ) targetStore => InstalledGlobals codes locations captured targetStore ∧
        ClosuresPreserved store targetStore)
      values arity emptyEnvironment heapRelated ⟨installed, ClosuresPreserved.refl store⟩
      (fun _ _ _ _ hypothesis => ⟨hypothesis.1.append _, ClosuresPreserved.trans hypothesis.2 (ClosuresPreserved.append _ _)⟩)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
  have parameterGlobals := cells.globalEnvironment arity allowed
    (globalsRelated.temporary (bundleType own.parameters) (bundleValues targets))
  obtain ⟨extension, controlValue, finalStore, related, executed, finalHeap, finalInstalled, lastFrame⟩ :=
    continued statementsCompiled
      ((covered.temporary (bundleType own.parameters)).bindArguments arity sourceBound)
      parametersRelated parameterGlobals allocatedHeap allocatedGlobals.1
  obtain ⟨targetValue, resultRelated, finished⟩ := finish_preserves resultCompiled related executed
  have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
    (mapping := mapping.lift) rfl
    (fun index value found => by simpa only [Nat.zero_add] using found) finished
  refine ⟨parameterExtension ++ extension, targetValue, finalStore, resultRelated, ?_, ?_, finalInstalled, ClosuresPreserved.trans allocatedGlobals.2 lastFrame⟩
  · simpa only [parameterCode, values.length.2] using initialized
  · simpa only [List.append_assoc] using finalHeap

/-- The actual signature and represented arguments have the same arity.
The source binder therefore returns a state, excluding the arity fault rule. -/
theorem arity {σ : Type} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {typeFuel : Nat} {function : Function}
    {code : GlobalCode} {index : Nat} {sources : List Semantics.Value} {state : Semantics.State σ}
    (signatureCompiled : signature typeFuel function = .ok code.own)
    (mismatch : Semantics.bindArguments function.args sources [] state = none) :
    FunctionSimulation codes locations captured code index sources state (.fault .arityMismatch) state := by
  intro targets values
  obtain ⟨sameLength, _⟩ := signature_components signatureCompiled
  obtain ⟨environment, finalState, bound⟩ :=
    bindArguments_exists (sameLength.trans values.length.1.symm) [] state
  rw [mismatch] at bound
  cases bound

/-- The function constructor in the mutual source derivation uses the body
IH at its specific allocated state and preserves the exact installed closure. -/
theorem function_simulation {σ : Type} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {code : GlobalCode} {index : Nat}
    (signatureCompiled : signature typeFuel function = .ok code.own)
    (compiled : lowerFunction fuel signatures scope function code.own = .ok code.expression)
    (covered : ScopeCoverage [] scope)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    {sources : List Semantics.Value} {initial allocated final : Semantics.State σ}
    {sourceEnvironment : Semantics.Environment}
    (bound : Semantics.bindArguments function.args sources [] initial = some (sourceEnvironment, allocated))
    {control : Semantics.Control}
    (continued : StatementsSimulation signatures codes locations captured sourceEnvironment
      function.body allocated control final) :
    FunctionSimulation codes locations captured code index sources initial
      (Semantics.finishFunction function.ret control) final := by
  intro targets values world store heap installed
  have capturedGlobals : GlobalEnvironmentRel codes locations scope (globalShift index)
      (installationEnvironment captured index) := by
    change GlobalEnvironmentRel codes locations scope (fun slot => index + slot)
      (List.replicate index Core.Value.unit ++ captured)
    simpa only [List.length_replicate, Core.Renaming.id]
      using globals.prepend (List.replicate index Core.Value.unit)
  obtain ⟨extension, value, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩ :=
    function_body signatureCompiled compiled values bound continued
      covered capturedGlobals heap installed
  exact ⟨extension, _, finalStore, related, evaluated, finalHeap, finalInstalled, lastFrame⟩

end Solcore.Frontend.RustHull.DerivationFunctionCorrespondence
