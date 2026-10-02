import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
import Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Native prefix bounds and independently measured source prefixes. These
consumers preserve the actual derivation under the seven assignment and six
post slots. They do not establish bounded assignment child meaning or the
whole header/for semantic factor, which remain separate integration units. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedHeaderBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof RecursiveNamedHeaderContracts
open CallableIndexedHistory (NativeFrame)
open SourceCoreCompatibleDataPlaces
open DataPlaceExecution (referenceEnvironment keysEnvironment snapshotEnvironment rhsEnvironment modifiedEnvironment writtenEnvironment)

/-- A strict-only family cannot be applied to an unchanged empty prefix. -/
theorem strict_does_not_supply_equal (budget : Nat) :
    RecursiveNamedBoundedContracts.Below budget (fun size => size < budget) ∧
      ¬ AtMost budget (fun size => size < budget) := by
  exact ⟨fun _ smaller => smaller, fun inclusive => Nat.lt_irrefl _ (inclusive budget (Nat.le_refl _))⟩

section Nil
variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : SourceSemantics.Program}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Core.Ty} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
  {contextLocation : Location} {native : NativeFrame} {value : Core.Value} {finalStore : Store}

/-- The real same-size continuation can be consumed at the inclusive bound. -/
theorem nil_keeps_size {size : Nat}
    {meaning : Nat → SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}
    (tail : ProtectedForHeader.Tail (entry := entry) registry functions source solved evidence administrative frame globals
      contextLocation native (ContinuationWithin size meaning) context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals
      contextLocation native type faults (ContinuationWithin size meaning) context environment heap []
      tail.mapping tail.world tail.store value finalStore ∧ meaning size context tail.scope tail.code :=
  ⟨ResultAt.nil tail evaluated, tail_at_remaining tail (Nat.le_refl size) (Nat.le_refl size)⟩
end Nil

section SourceFault
variable {program : SourceSemantics.Program} {size : Nat} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {binder : TypedBinder} {initializer : ExpressionId}
  {items : List ForItemForm} {reason : Dynamic.SemanticFault}

/-- Initializer failure retains its actual effects without extending context or
allocating the declared binding. Its expression witness is strictly smaller. -/
theorem initializer_fault_context (mono : binder.scheme.quantified = [])
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment before initializer reason after) :
    SourceExecutionSize.ForItemsFault program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]])
      context evidence source environment before (.letDecl binder (some initializer) :: items) context reason after ∧
    size < SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [size]] := by
  exact ⟨.head (.letInitializer mono failed), Nat.lt_trans
    (SourceExecutionSize.child_lt_stepSize (children := [size]) (by simp))
    (SourceExecutionSize.child_lt_stepSize (children := [SourceExecutionSize.stepSize [size]]) (by simp))⟩
end SourceFault

theorem assignment_continuation_below {size budget : Nat} {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalidOperand : Word}
    {environment : Environment} {before keyStore snapshotStore rhsStore modifiedStore setterStore written finalStore : Store}
    {location : Location} {keyValue snapshot right changed updated old result : Value}
    (referenceSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) location))
    (keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType location environment) before
      (shift 1 keys.expression) (.inRight .word keyValue) keyStore)
    (snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType location keyValue environment) keyStore
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) snapshotStore)
    (rhsEvaluated : Evaluates (snapshotEnvironment prepared.route.rootType location keyValue snapshot environment) snapshotStore
      (shift 3 rhs) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates (rhsEnvironment prepared.route.rootType location keyValue snapshot right environment) rhsStore
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand) (.inRight .word changed) modifiedStore)
    (setterEvaluated : Evaluates (modifiedEnvironment prepared.route.rootType location keyValue snapshot right changed environment) modifiedStore
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) (.inRight .word updated) setterStore)
    (read : setterStore.read? location = some old)
    (write : setterStore.write? location (.inRight .unit updated) = some written)
    (completed : EvaluationSize size environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand) result finalStore) (bounded : size ≤ budget) :
    ∃ remainingSize, remainingSize < budget ∧
      EvaluationSize remainingSize
        (writtenEnvironment prepared.route.rootType location keyValue snapshot right changed updated environment)
        written (shift 7 next) result finalStore := by
  obtain ⟨remainingSize, smaller, remaining⟩ := ForHeaderNativeBounds.execute_continuation
    referenceSelected keysEvaluated snapshotEvaluated rhsEvaluated modifiedEvaluated setterEvaluated read write completed
  exact ⟨remainingSize, Nat.lt_of_lt_of_le smaller bounded, remaining⟩

/-- The post witness is a strict child of the original loop body. Renaming it
under the six concrete temporaries leaves its size unchanged. -/
theorem post_below_loop {size budget : Nat} {actual : Environment} {before conditionStore bodyStore after : Store}
    {type : Core.Ty} {location : Location} {condition body post : Expr} {reason : Word} {value : Core.Value}
    (continued : Bool)
    (completed : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) before
      (LocalLoop.loopBody type condition body post reason) value after)
    (conditionEval : Evaluates (Core.LoopExecution.entryEnvironment type location actual) before
      (Core.LoopExecution.conditionCode condition) (.inRight .word (.bool true)) conditionStore)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) conditionStore
      (Core.LoopExecution.bodyCode body)
      (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore)
    (bounded : size ≤ budget) :
    ∃ postSize postStore postValue, postSize < budget ∧
      EvaluationSize postSize (TypedImperativeFor.postValues type location continued ++ actual)
        bodyStore (ForLoop.postCode post) postValue postStore := by
  obtain ⟨branchSize, smaller, branch⟩ := completed.loop_true_branch conditionEval
  obtain ⟨postSize, postStore, postValue, postSmaller, evaluated⟩ :=
    ForHeaderNativeBounds.post_computation_sized continued branch bodyEval
  exact ⟨postSize, postStore, postValue, Nat.lt_of_lt_of_le (Nat.lt_trans postSmaller smaller) bounded, evaluated⟩

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function empty(raw: mapping(Word => Word)) returns (Word) { for (; false;) { raw[1] = 999; } return raw[1]; }",
  "function post(raw: mapping(Word => Word)) returns (Word) { let count = 0; for (let index: Word, index = 0, next(index); index < 3; let saved: Word, saved = next(index), let copy = saved, raw[1] += copy, index += 1) { count += 1; continue; } return raw[1] + count; }",
  "function initialFault(raw: mapping(Word => Word)) returns (Word) { for (raw[1] += 1, let stop = bad(0); true; raw[1] += 90) { raw[1] += 99; } return raw[1]; }",
  "function postFault(raw: mapping(Word => Word)) returns (Word) { for (let index = 0; index < 3; raw[1] += 1, let stop = bad(index), index += 1) { raw[1] += 2; } return raw[1]; }"
]
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word n), (word 1, word 91)]

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "header actual size boundaries" content
    ["empty", "post", "initialFault", "postFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 819)⟩]}
  let badKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let bad ← SourceCoreUnifiedCorpusSupport.get "header fault body" (SourceCompilationPlan.exactSpecialization compiled.validationPlan badKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders bad.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "header fault binder missing")
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated) in [("empty", some 10, 10), ("post", some 19, 16), ("initialFault", none, 11), ("postFault", none, 13)] do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10] fuel initial
      let completed ← SourceCoreUnifiedCorpusSupport.get "header resume" (started.resume 400000)
      let observation := completed.observation
      let final ← match observation, result with
        | .done actual final, some expected =>
          SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (word expected)) s!"header result {name}"
          pure final
        | .fault (.uninitializedLocal id) final, none =>
          SourceCoreUnifiedCorpusSupport.assertTrue (id == gap) "header exact first fault"
          pure final
        | other, _ => throw (IO.userError s!"header unexpected {name}: {reprStr other}")
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "header inert prefix"
      match final.heap[initial.heap.length]? with
      | some cell => SourceCoreUnifiedCorpusSupport.assertTrue (reprStr cell.value == reprStr (some (table updated))) s!"header ordered mapping/write prefix {name}"
      | none => throw (IO.userError "header mapping missing")
      current := current ++ [reprStr observation]
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "header resumed observation"
  IO.println "recursive header bounds: nil equality, independent source fault context, actual seven/six slot size witnesses, marked locals, duplicate writes and resume GREEN"

end Tests.SourceCoreRecursiveNamedHeaderBounds
