import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotSource
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The actual unary compiler yields an independent source write/fault and
seven real typed slots. The continuation cost is taken from its original
Core execution, including when it has effects or reads a captured cell. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreRecursiveNamedBareBitNotBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates
open CompatibleRenamedBareBitNot
section Lowering
variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {assignment : AssignmentResolution} {site : SourceCoreElaboration.ErrorSite}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp} {next lowered : Expr} {output : Ty}
  {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  {identities : Dynamic.Value → Word → Prop}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
  (observations : FunctionObservations compilation.checked.catalog functions identities)
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
    mapping world administrativeContext scope environment canonical)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)

include rootTyped bare profile observations environments heaps locals agrees

theorem actual_lower_reflects_sized
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      output next reasonAt invalid invalidOperand missing = .ok lowered)
    {faults : FunctionCalls.FaultRep} {value : Value} {finalStore : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    {size : Nat} (completed : CoreProof.EvaluationSize size actual store (lowered.rename ξ) value finalStore) :
    ∃ prepared, CompatibleRenamedBareBitNot.ResultAt size compilation.checked registry functions program context evidence source faults prepared assignment.target
      environment before store mapping world actual actualContext ξ next output value finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  refine ⟨prepared, ?_⟩
  exact CompatibleRenamedBareBitNot.reflects_sized layout bare observations (view ▸ profile) environments heaps locals agrees actualTyped slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

end Lowering

section Continuation
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {faults : FunctionCalls.FaultRep} {prepared : Prepared} {place : PlaceResolution}
  {environment : Dynamic.Environment} {before : Dynamic.Heap} {store : Store} {mapping : LocationMap}
  {world : StoreTyping} {actual : Core.Environment} {actualContext : Core.Context} {ξ : Renaming}
  {next : Expr} {output : Ty} {value : Core.Value} {finalStore : Store} {size budget : Nat}

/-- Successful reflection selects only a strictly smaller native continuation.
The source size is independent and has no comparison to the native bound. -/
theorem continuation_or_fault
    (receipt : CompatibleRenamedBareBitNot.ResultAt size checked registry functions program context evidence source faults
      prepared place environment before store mapping world actual actualContext ξ next output value finalStore)
    (within : size ≤ budget) :
    (∃ sourceSize reason, SourceExecutionSize.SourcePlaceBitNotFaults program sourceSize context evidence source
      environment before place reason before) ∨
    (∃ sourceSize updated after written slots remainingSize,
      SourceExecutionSize.SourcePlaceSnapshotUpdate program sourceSize context evidence source Dynamic.BitNotSnapshot
        environment before place updated after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes world (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      remainingSize < budget ∧ CoreProof.EvaluationSize remainingSize (slots ++ actual) written
        (shift 7 (next.rename ξ)) value finalStore) := by
  cases receipt with
  | fault trace _ _ _ => exact .inl ⟨_, _, trace⟩
  | success trace _ _ _ _ count typed smaller continuation =>
    exact .inr ⟨_, _, _, _, _, _, trace, count, typed, Nat.lt_of_lt_of_le smaller within, continuation⟩
end Continuation

private def content : String := String.intercalate "\n" [
  "function wordMask(seed: Word) returns (Word) { let root = seed; let read: function() returns (Word) = lam() -> Word { return root; }; root ~=; return read(); }",
  "function doubleLoop(seed: Word) returns (Word) { let root = seed; for (let i = 0; i < 3; i += 1) { root ~=; root ~=; } return root; }",
  "function firstFault(seed: Word) returns (Word) { let root = seed; let gap: Word; root ~=; gap ~=; root = 99; return root; }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Core.Word.ofNatModulo n)
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let started ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"unary bound resume {name}" (started.resume 400000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "bounded bare unary update" content
    ["wordMask", "doubleLoop", "firstFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let cases : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value) := [
    ("wordMask", [wordValue 7], .word (Core.Word.ofNatModulo 7).bitNot),
    ("doubleLoop", [wordValue 7], wordValue 7)]
  let baselines ← cases.mapM fun (name, arguments, _) => finish compiled name arguments 400000 initial
  let faultBaseline ← finish compiled "firstFault" [wordValue 7] 400000 initial
  for fuel in [0, 37, 400000] do
    for ((name, arguments, expected), baseline) in cases.zip baselines do
      let result ← finish compiled name arguments fuel initial
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr result == reprStr baseline)
        s!"unary resume observation changed {name}"
      match result with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr expected) s!"unary result {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
          s!"unary inert heap prefix {name}"
        SourceCoreUnifiedCorpusSupport.assertTrue
          (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
          s!"unary heap/capture safety {name}"
      | other => throw (IO.userError s!"unary {name}: {reprStr other}")
    let result ← finish compiled "firstFault" [wordValue 7] fuel initial
    SourceCoreUnifiedCorpusSupport.assertTrue (reprStr result == reprStr faultBaseline) "unary fault resume changed"
    match result with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        "unary fault inert prefix"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (final.heap.any fun cell => match cell.value with
          | some (.word value) => value == (Core.Word.ofNatModulo 7).bitNot
          | _ => false) "unary fault lost prior write"
      SourceCoreUnifiedCorpusSupport.assertTrue (!(SourceCoreUnifiedCorpusSupport.hasWord final 99))
        "unary first fault ran continuation"
    | other => throw (IO.userError s!"unary first fault: {reprStr other}")
  IO.println "bounded bare unary: actual compiler, independent source trace, strict original continuation, seven typed slots, capture/loops/prior writes/fault/resume GREEN"
end Tests.SourceCoreRecursiveNamedBareBitNotBounds
