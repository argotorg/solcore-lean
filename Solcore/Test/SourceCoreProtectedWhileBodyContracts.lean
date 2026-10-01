import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Generic five-way body contracts preserve the old lexical API and admit
real break/continue native completions without a runtime child premise.
Actual cached Core regressions also exercise nested control and resumed effects;
recursive guarded statement Tree integration is a subsequent unit. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedWhileBodyContracts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
section Static
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {scope : Scope} {type : Ty} {expected : TypeSystem.Ty}

theorem preserves_embedding {mode : Bool} {statements : List StatementId} {code : Expr}
    (correct : ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code) :
    ProtectedWhile.Body.Preserves functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code :=
  ProtectedWhile.Body.of_lexical_preserves functions program evidence correct

theorem reflects_embedding {mode : Bool} {statements : List StatementId} {code : Expr}
    (correct : ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code) :
    ProtectedWhile.Body.Reflects functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) mode statements expected type code :=
  ProtectedWhile.Body.of_lexical_reflects functions program evidence correct

/-- This actual transfer body has no expression or runtime body assumption. -/
theorem breaking_reflects {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) :
    ProtectedWhile.Body.Reflects functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) false [id] expected type (LocalLoop.breaking type) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
    simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
  exact ⟨_, _, before, mapping, world,
    TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
      (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

/-- This actual transfer body has no expression or runtime body assumption. -/
theorem continuing_reflects {id : StatementId} {node : StatementNode}
    (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) :
    ProtectedWhile.Body.Reflects functions program evidence
      (entry := entry) (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) false [id] expected type (LocalLoop.continuing type) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
    simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated nativeEval
  exact ⟨_, _, before, mapping, world,
    TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
      (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 4)) { index += copied(1); if (less(index, 2)) { continue; } let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } raw[next(0)] += copied(1); if (less(1, inner)) { break; } } } return copied(index + raw[next(0)]); }",
  "function outerBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { raw[next(0)] += copied(2); index += next(0); if (less(2, index)) { break; } } return copied(index + raw[next(0)]); }",
  "function nestedFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); let inner = 0; while (less(inner, 3)) { inner += next(0); raw[next(0)] += copied(1); if (less(1, inner)) { bad(index); } } } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected five-way while resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected five-way while fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected five-way while exact fault binder missing")

private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected five-way while inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected five-way while missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected five-way while raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 3]? with
    | some cell => pure cell | none => throw (IO.userError "protected five-way while missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected five-way while writes changed {name}"
  match final.heap[initial.heap.length + 2]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected five-way while captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 1, initial.heap.length])
      s!"protected five-way while captured source aliases changed {name}"
  | other => throw (IO.userError s!"protected five-way while lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected five-way while contracts" content
    ["nested", "outerBreak", "nestedFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled "bad"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("nested",17,13,4), ("outerBreak",19,16,3)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected five-way result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected five-way success {name}: {reprStr other}")
    let completed ← finish compiled "nestedFault" fuel initial
    match completed with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "protected five-way exact nested fault"
      observe initial final "nestedFault" 12 1
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected five-way failure: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected five-way resume changed observations"
  IO.println "protected five-way while contracts: lexical embeddings, closed break/continue reflection, actual nested loops/transfer/fault effects, raw duplicate/capture aliases and resume GREEN"

end Tests.SourceCoreProtectedWhileBodyContracts
