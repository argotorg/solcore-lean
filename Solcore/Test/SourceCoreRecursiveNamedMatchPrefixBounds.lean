import Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchPrefixContracts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual selected match prefixes retain the original strict native child,
ordered lexical additions, full runtime typing and protected entry. Tests keep
empty-prefix equality and ordinary agreement separate from strict bounds. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchPrefixBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates DataMatchBranchPrefix
open CallableIndexedHistory CompatibleMatchSelectionPrefix RecursiveNamedMatchPrefixContracts

theorem actual_remaining
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
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
    {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry)
    (initial : entry scope mapping world heap store canonical)
    {wholeSize : Nat} {result : Value} {endStore : Store}
    (completed : EvaluationSize wholeSize actual before (code.rename ξ) result endStore) :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      entry finalScope finalMap finalWorld finalHeap finalStore finalCanonical ∧
      ∃ remainingSize, remainingSize < wholeSize ∧
        EvaluationSize remainingSize finalActual finalStore (body.rename finalEmbedding) result endStore := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry, agreement⟩ :=
    success_prefix certificate ordinary onError allocator valid catalogValid definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated transport bindings initial
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, spine, installedEntry,
    agreement.remaining completed⟩

theorem empty_prefix {size : Nat} {environment : Environment} {store after : Store} {code : Expr} {value : Value}
    (original : EvaluationSize size environment store code value after) :
    ∃ remaining, remaining ≤ size ∧ EvaluationSize remaining environment store code value after :=
  (ContinuationSize.refl environment store code).remaining original

theorem empty_prefix_equal {size : Nat} {environment : Environment} {store after : Store} {code : Expr} {value : Value}
    (original : EvaluationSize size environment store code value after) :
    ∃ remaining, remaining = size ∧ EvaluationSize remaining environment store code value after :=
  ⟨size, rfl, original⟩

theorem agreement_does_not_force_strict :
    ContinuationAgreement [] [] .unit [] [] .unit ∧ ¬ ContinuationSize true [] [] .unit [] [] .unit := by
  refine ⟨.refl _ _ _, ?_⟩
  intro strict
  obtain ⟨child, smaller, original⟩ := strict.remaining EvaluationSize.unit
  cases original
  simp at smaller

theorem duplicate_prefix_order {α : Type} (scope : List α) (canonical : Environment)
    (same : α) (first second : Value) :
    CanonicalPrefix scope canonical (same :: same :: scope) (second :: first :: canonical) :=
  (CanonicalPrefix.cons scope canonical same first).trans (.cons _ _ same second)

theorem selected_entry {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry) (binds : ProtectedExpressionMeaning.Binds entry)
    {scope childScope : SourceCoreLocalCell.Scope} {canonical childCanonical : Environment}
    {mapping finalMap : LocationMap} {world finalWorld : StoreTyping} {before after : Dynamic.Heap}
    {store finalStore : Store} (initial : entry scope mapping world before store canonical)
    (spine : CanonicalPrefix scope canonical childScope childCanonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
    entry childScope finalMap finalWorld after finalStore childCanonical ∧
      entry scope finalMap finalWorld after finalStore canonical :=
  ⟨installed transport binds initial spine maps worlds frame metadata, restored transport initial maps worlds frame metadata⟩

private def content : String := String.intercalate "\n" [
  "function ordered(seed: Word) returns (Word) { let kept = seed + 1; match ((seed, (11, 13))) { case (0, (left, right)) { let result = left + right; return result; } case (1, (left, right)) { return right; } default { return kept; } } }",
  "function empty(seed: Word) returns (Word) { match (seed) { case 0 {} default {} } return 17; }",
  "function failed(seed: Word) returns (Word) { match ((seed, 19)) { case (0, value) { let prior = value; let gap: Word; return gap; } default { return 23; } } }",
  "function scrutineeFault() returns (Word) { let gap: Word; match (gap) { case 0 { return 29; } default { return 31; } } }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match prefix public resume" (first.resume 300000)).observation

/-- Source-visible hidden cells and only the selected ordered arm bindings
survive. Native snapshots and markers are checked by actual typed-prefix
formal consumers above, separately from this public source-state observation. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive match prefix bounds" content
    ["ordered", "empty", "failed", "scrutineeFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 839)⟩]}
  let nested : SourceTypedRuntime.Value := .product (word 11) (word 13)
  let pairType : TypeSystem.Ty := .product .word (.product .word .word)
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("ordered", [word 0], word 24, [(.word, some (word 0)), (.word, some (word 1)), (pairType, some (.product (word 0) nested)),
      (.word, some (word 11)), (.word, some (word 13)), (.word, some (word 24))]),
    ("ordered", [word 1], word 13, [(.word, some (word 1)), (.word, some (word 2)), (pairType, some (.product (word 1) nested)),
      (.word, some (word 11)), (.word, some (word 13))]),
    ("ordered", [word 2], word 3, [(.word, some (word 2)), (.word, some (word 3)), (pairType, some (.product (word 2) nested))]),
    ("empty", [word 0], word 17, [(.word, some (word 0)), (.word, some (word 0))]),
    ("empty", [word 1], word 17, [(.word, some (word 1)), (.word, some (word 1))]),
    ("failed", [word 1], word 23, [(.word, some (word 1)), (.product .word .word, some (.product (word 1) (word 19)))])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match prefix resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"match prefix result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match prefix ordered source cells changed {name}"
      | other => throw (IO.userError s!"match prefix expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("failed", [word 0], [(.word, some (word 0)), (.product .word .word, some (.product (word 0) (word 19))),
      (.word, some (word 19)), (.word, some (word 19)), (.word, none)]),
    ("scrutineeFault", [], [(.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 300000 initial
    for fuel in [0, 7, 53, 300000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match prefix fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match prefix fault cells changed {name}"
      | other => throw (IO.userError s!"match prefix expected first fault {name}: {reprStr other}")
  IO.println "recursive named match prefix bounds: ordered arm/default cells, empty body, strict original native continuation, first faults and public resume GREEN"

end Tests.SourceCoreRecursiveNamedMatchPrefixBounds
