import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmPrefix
import Solcore.Test.SourceCompilerFeatureSupport

/-! Consumers of the actual compatible marked arm allocator. Both evaluation
directions reach the same independent source allocations even when the
continuation returns a closure capturing the real inserted environment. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleMatchArmAllocations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof DataPatternValues
open CallableIndexedHistory CallableIndexedParameterMeaning

/-- Successful actual lowering is sufficient to derive the prefix. The body
execution and any exact closure equality under weakening are absent as premises. -/
theorem accepted_closure_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {compilation : SourceCoreCompatibleDataMatches.Context}
    {scope : SourceCoreSourceCells.Scope} {bindings : List (TypedBinder × Ty)} {code : Expr}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator compilation source scope bindings
      (.function .unit .unit)
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).weakenAt bindings.length) = .ok code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (sameDefinitions : layouts.definitions = definitions) (registered : layout.Registered definitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {scrutinee : Value}
    {contextLocation : Location} {native : NativeFrame}
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (packValues values :: scrutinee :: canonical) actual) :
    ∃ finalEnvironment finalHeap finalActual finalStore finalMap finalWorld,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      Evaluates actual store (code.rename ξ)
        (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore ∧
      (∀ result finished, Evaluates actual store (code.rename ξ) result finished →
        result = .inRight .word (.closure .unit .unit (.var 0) finalActual) ∧ finished = finalStore) := by
  obtain ⟨finalEnvironment, finalHeap, _, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, _, finalHeaps, _, _, frame, _, agreement⟩ :=
    CompatibleMatchArmPrefix.bindArm_prefix represented sameDefinitions registered allocator accepted
      (named := false) kinds reference read unmapped environments heaps actualLayout
  have child : Evaluates finalActual finalStore
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).rename finalEmbedding)
      (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore := .inRight .lambda
  refine ⟨finalEnvironment, finalHeap, finalActual, finalStore, finalMap, finalWorld, allocated,
    finalHeaps, frame, agreement.wrap child, ?_⟩
  intro result finished completed
  exact evaluation_deterministic (agreement.unwrap completed) child

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function selected(flag: Word, a: Word, b: Word) returns (Word) { match ((flag, (a, b))) { case (0, (x, y)) { return x + y; } default { return 99; } } }",
    "function ordered(p: Word) returns (Word) { match ((p, (11, 13))) { case (0, (x, y)) { return x + y; } case (v, (_, y)) { return v + y; } } }",
    "function captured(marker: Word) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, 2)) { case (f, x) { let ignored: Word = f(x); return marker; } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "compatible marked arm program" (checkProgram workspace)
  let w := SourceCompilerFeatureSupport.scalar
  let tupleType : TypeSystem.Ty := .product .word (.product .word .word)
  let selected ← SourceCompilerFeatureSupport.compileNamed program "selected"
  for (flag, expected) in [(0, 18), (1, 99)] do
    let inputs := [w flag, w 7, w 11]
    SourceCompilerFeatureSupport.require ((← selected.run inputs) == w expected) "selected arm changed source binding order"
    let cells := [(TypeSystem.Ty.word, some (w flag)), (.word, some (w 7)), (.word, some (w 11)),
      (tupleType, some (.product (w flag) (.product (w 7) (w 11))))]
    selected.checkCells inputs (cells ++ if flag == 0 then [(.word, some (w 7)), (.word, some (w 11))] else [])
    for budget in [0, 7, 43] do selected.checkResume inputs (w expected) budget
  let ordered ← SourceCompilerFeatureSupport.compileNamed program "ordered"
  for (value, expected, first) in [(0, 24, 11), (7, 20, 7)] do
    let inputs := [w value]
    SourceCompilerFeatureSupport.require ((← ordered.run inputs) == w expected) "failed arm allocated or changed later arm bindings"
    ordered.checkCells inputs [(.word, some (w value)),
      (tupleType, some (.product (w value) (.product (w 11) (w 13)))),
      (.word, some (w first)), (.word, some (w 13))]
    for budget in [0, 7, 43] do ordered.checkResume inputs (w expected) budget
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  SourceCompilerFeatureSupport.require ((← captured.run [w 10]) == w 12) "marked arm captures included an administrative temporary"
  for budget in [0, 7, 43] do captured.checkResume [w 10] (w 12) budget
  IO.println "compatible marked match arms: actual allocation receipts, skipped temporary captures, exact source cells and finite continuation agreement GREEN"
end Tests.SourceCoreCompatibleMatchArmAllocations
