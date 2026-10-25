import Solcore.Frontend.RustHull.ContractCallModeInitializedExecution
import Solcore.Frontend.RustHull.ModeChildFrameCorrespondence
import Solcore.Frontend.RustHull.ContractChildCallInitialLinks

/-! Finite source call trees using CALL, STATICCALL, CALLCODE and DELEGATECALL
reach public receipts and resumption chains. Actual initialization supplies all
three handlers; source-height induction discharges their child execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractCallModeCorrespondence
open Correspondence ScalarExecution CodeBuilder ContractRuntimeEffectsCorrespondence
open ContractChildCallCorrespondence (InitialCatalogLinks initial_links)

theorem objectRuntime_preserves {program : Program} {code : CodeBlock} {fuel : Nat} {compiled : Core.Expr}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {others : List Core.Expr}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (accepted : AccountRuntime.compileFrame program code (RuntimeExtendedInitializedEffects.slots true) fuel = .ok compiled)
    (catalogCompiled : ContractCatalogCorrespondence.CompiledCatalog (RuntimeExtendedInitializedEffects.slots true) fuel catalog others)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    {depth : Nat} {environment : Core.Environment} {initial : Core.Store} {contextCode : Code}
    (object : Contract.CompiledObject) (context : Contract.Context) (notDeploying : context.deploying = false)
    (contextRelated : CodeValue depth environment contextCode (bundleValues (contextValues object context)))
    (initialLinks : CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)))
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object context⟩ sourceResult finalSource) :
    ∃ value final, Core.Evaluates environment initial
      (AccountRuntime.objectRuntime (RuntimeExtendedInitializedEffects.slots true) compiled others
        (ContractCatalogCorrespondence.images image catalog) image catalog contextCode depth) value final ∧
      MessageRel sourceResult finalSource.external context.address value := by
  obtain ⟨closure, captured⟩ := compileFrame_captures accepted environment
  obtain ⟨values, captures⟩ := catalogCompiled.captures environment
  apply objectRuntime_evaluates_callbacks
    (fun value _ => MessageRel sourceResult finalSource.external context.address value)
    (.cons captured captures) (ContractMemoryCorrespondence.sharedValues_related object context contextRelated)
  intro functions shared dispatcher creator extra allocated cells dispatcherLocation creatorLocation functionsRelated references initialized separate description _ dispatcherRelated creatorRelated creatorFound creatorAfter dispatcherAfter dispatcherBefore capture
  have entry := ContractCatalogCorrespondence.entry_reference captures functionsRelated
  exact objectFrame_evaluates accepted eligible captured entry object context notDeploying
    (contextRelated.prepend extra) references initialized separate description creatorRelated creatorFound creatorAfter
    dispatcherRelated dispatcherAfter dispatcherBefore capture catalogCompiled captures connection
    (ModeChildFrameCorrespondence.frame_execution sourceCatalog catalog anchors height) initialLinks evaluated

def PublicMessageRel (context : Contract.Context) (result : Semantics.Result Semantics.Value)
    (state : RuntimeCallEffectsSemantics.State) (value : Core.Value) : Prop :=
  MessageRel result state (Contract.normalizeContext context).address value

/-- Account code is checked in the same normalized source state that begins the
public execution. No Core store, captured closure or execution premise occurs. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context) (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    (contextInitialState image object normalized).runtime.runtime.runtime.runtime.runtime.storage.world

theorem compileObject_preserves {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image)
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
  have signature : ContractCatalogCorrespondence.slots image catalog = RuntimeExtendedInitializedEffects.slots true := by
    change RuntimeExtendedInitializedEffects.slots (image.isSome || !catalog.isEmpty) = _
    rw [hasCode]
  rw [signature] at frameCompiled catalogCompiled objectExpression
  have normalized : (Contract.normalizeContext context).deploying = false := notDeploying
  have links := initial_links object (Contract.normalizeContext context)
    (CatalogWorldCorrespondence.compileObject_images accepted) initialLinks
  obtain ⟨value, final, executed, related⟩ := objectRuntime_preserves frameCompiled
    (ContractCatalogCorrespondence.compiledCatalog catalogCompiled) eligible connection object
    (Contract.normalizeContext context) normalized
    (CodeValue.bound 0 [] (bundleValues (contextValues object (Contract.normalizeContext context)))) links evaluated
  refine ⟨value, final, instantiate_evaluates context (parameter := AccountRuntime.contextType)
    (resultType := AccountRuntime.resultType) ?_ executed, related⟩
  rw [objectExpression]
  rfl

/-- Public resumption uses the actual compiled evaluator. Its fuel threshold is
exact for the independently derived parent and child result. -/
theorem compileObject_resumes_exact {program : Program} {path : List String} {code : CodeBlock} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {sourceCatalog : ChildFrameSemantics.Catalog} {anchors : List CatalogWorldCorrespondence.Anchor} {height : Nat}
    (selected : AccountRuntime.select program.objects path = .ok code)
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (hasCode : (image.isSome || !catalog.isEmpty) = true)
    (eligible : DerivationCorrespondence.ExecutableProgram (supported true)
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code]))
    (connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection sourceCatalog catalog anchors)
    (context : Contract.Context) (notDeploying : context.deploying = false)
    (initialLinks : InitialContextLinks image catalog object context anchors)
    {finalSource : Semantics.State RuntimeCallEffectsSemantics.State} {sourceResult : Semantics.Result Semantics.Value}
    (evaluated : Semantics.EvalFunction
      (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
      (ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image)
      (AccountRuntime.frameFunction code) [] ⟨[], contextInitialState image object (Contract.normalizeContext context)⟩ sourceResult finalSource) :
    ∃ value, PublicMessageRel context sourceResult finalSource.external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  obtain ⟨value, _, executed, related⟩ :=
    compileObject_preserves selected accepted hasCode eligible connection context notDeploying initialLinks evaluated
  exact ⟨value, related, Contract.evaluation_resumes_exact executed⟩

end Solcore.Frontend.RustHull.ContractCallModeCorrespondence
