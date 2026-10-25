import Solcore.Frontend.RustHull.ContractCodeInitializedExecution
import Solcore.Frontend.RustHull.ContractCatalogCorrespondence

/-! Supplied code images and compiled catalogs reach the public contract
runner through actual compilation, closure capture and initialization. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCodeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    (accepted : AccountRuntime.compileFrame program code (Effects.slots ++ Effects.codeSlots) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (Effects.slots ++ Effects.codeSlots) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (Effects.slots ++ Effects.codeSlots) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_separated
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells _ creatorLocation functionsRelated references initialized separate description _ _ creatorRelated creatorFound creatorAfter
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCodeEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- The actual compiler supplies every catalog closure. The independent entry
evaluation determines the result, including code availability and copy faults. -/
theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates [] [] (object.instantiate context).expression value final ∧
      PublicMessageRel context sourceResult finalSource.external value := by
  have compiled : AccountRuntime.compileObject program path fuel image catalog = .ok object.expression := by
    unfold Contract.compileObject at accepted
    obtain ⟨expression, compiled, returned⟩ := lower_bind_eq_ok.mp accepted
    cases returned
    exact compiled
  obtain ⟨frame, others, frameCompiled, catalogCompiled, objectExpression⟩ :=
    ContractCatalogCorrespondence.compileObject_selected selected compiled
  have signature : ContractCatalogCorrespondence.slots image catalog = Effects.slots ++ Effects.codeSlots := by
    simp only [ContractCatalogCorrespondence.slots, hasCode, ↓reduceIte]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Every genuine public resumption chain reaches the independently derived
message exactly when its cumulative fuel covers the required transitions. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram supported
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (context : Contract.Context) (notDeploying : context.deploying = false)
    {finalSource : Semantics.State RuntimeCodeEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]) (RuntimeCodeEffectsSemantics.effects image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible context notDeploying evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractCodeCorrespondence
