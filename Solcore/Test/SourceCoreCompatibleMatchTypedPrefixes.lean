import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
import Solcore.Test.SourceCompilerFeatureSupport

/-! The independently selected compatible arm reaches an actual closure body
with exactly its real captured environment. Both finite directions preserve the
hidden/source binder allocations; no body evaluation is supplied by a caller. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMatchTypedPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix CallableIndexedHistory

theorem selected_closure_body
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution (.function .unit .unit) internalReason
      expressionCertificate (fun _ _ code => code = LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))) code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∃ hiddenHeap location selectedEnvironment selectedHeap selectedActual selectedStore selectedMap selectedWorld selectedContext,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) (bindings.map Prod.snd) selectedEnvironment selectedHeap ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions selectedMap selectedWorld selectedHeap selectedStore ∧
      AdministrativePreserved mapping store selectedMap selectedStore ∧
      RuntimeEnvironmentHasTypes selectedWorld selectedActual selectedContext ambient.definitions ∧
      RuntimeValueHasType selectedWorld (.closure .unit .unit (.var 0) selectedActual) (.function .unit .unit) ambient.definitions ∧
      Evaluates actual before (code.rename ξ)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore ∧
      (∀ result finished, Evaluates actual before (code.rename ξ) result finished →
        result = LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual) ∧ finished = selectedStore) := by
  obtain ⟨hiddenHeap, location, finalScope, selectedEnvironment, selectedHeap, selectedCanonical, selectedActual,
      selectedStore, selectedMap, selectedWorld, selectedEmbedding, selectedContext, body,
      allocated, selected, selectedBody, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, _finalReference, _finalRead, _finalUnmapped, agreement⟩ :=
    CompatibleMatchTypedSelectionPrefix.Certificate.selected_prefix_typed certificate ordinary onError allocator valid catalogValid
      definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource
  cases selectedBody with
  | arm identities bound certified =>
    subst body
    have child : Evaluates selectedActual selectedStore
        ((LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))).rename selectedEmbedding)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore := by
      simp only [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]
      exact .caseRight (.inRight .lambda) (.inRight (.inLeft (.inRight (.var rfl))))
    refine ⟨hiddenHeap, location, selectedEnvironment, selectedHeap, selectedActual, selectedStore, selectedMap, selectedWorld, selectedContext,
      allocated, bound, finalHeaps, preserved, finalTyped, .closure finalTyped (.var rfl), agreement.wrap child, ?_⟩
    intro result finished completed
    exact evaluation_deterministic completed (agreement.wrap child)


private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function captured(marker: Word) returns (integer) { match ((lam(x: Word) -> Word { marker = wordFromInteger(integerAdd(wordToInteger(marker), wordToInteger(x))); return marker; }, 2)) { case (f, x) { let changed = wordToInteger(f(x)); return changed; } } }",
    "function selected(p: Word) returns (integer) { match ((p, 7)) { case (0, x) { let next = wordFromInteger(integerAdd(wordToInteger(x), 4)); return wordToInteger(next); } case (v, x) { let next = wordFromInteger(integerAdd(wordToInteger(v), wordToInteger(x))); return wordToInteger(next); } } }",
    "function failed(p: Word) returns (integer) { let hole: Word; match ((p, 7)) { case (0, x) { return wordToInteger(x); } case (v, x) { let changed = wordFromInteger(integerAdd(wordToInteger(v), wordToInteger(hole))); return wordToInteger(changed); } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "typed compatible match prefix" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  SourceCompilerFeatureSupport.require ((← captured.run [w 10]) == .integer 12) "selected closure lost actual typed mutable capture"
  for budget in [0, 7, 43] do captured.checkResume [w 10] (.integer 12) budget
  let selected ← SourceCompilerFeatureSupport.compileNamed program "selected"
  for (p, result) in [(0, 11), (3, 10)] do
    SourceCompilerFeatureSupport.require ((← selected.run [w p]) == .integer result) "selected builtin body changed matched binders or temporary values"
    let tuple : TypeSystem.Ty := .product .word .word
    let cells := if p == 0 then [(.word, some (w 7)), (.word, some (w 11))] else
      [(.word, some (w p)), (.word, some (w 7)), (.word, some (w 10))]
    selected.checkCells [w p] ([(.word, some (w p)), (tuple, some (.product (w p) (w 7)))] ++ cells)
    for budget in [0, 7, 43] do selected.checkResume [w p] (.integer result) budget
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let fault ← failed.invoke [w 3]
  match fault.outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "selected builtin fault did not preserve the completed marked prefix")
  failed.checkCells [w 3] [(.word, some (w 3)), (.word, none),
    (.product .word .word, some (.product (w 3) (w 7))), (.word, some (w 3)), (.word, some (w 7))]
  IO.println "typed compatible match prefixes: all actual temporary slot typing, exact native closure captures, selected builtins and effectful faults GREEN"

end Tests.SourceCoreCompatibleMatchTypedPrefixes
