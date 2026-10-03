import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.Test.SourceCoreRecursiveNamedExpressionTreeBounds

/-! The existing Match Tree consumes bounded expression laws at one budget,
including nested match children and loops. The concrete expression Tree and finite builtin callee close those
laws here; no child/body execution is a field of the static receipt. Source
and native costs are independent, and the preservation endpoint includes N. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedImperativeMatchBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
#check_failure RecursiveNamedImperativeFor.Tree
#check_failure RecursiveNamedImperativeFor.BodyMeaning
#check_failure SourceTypedRuntime.run
section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (catalogValid : SignatureCatalogWellFormed values.checked.signatures)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews catalogValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedHeaderContracts.AtMost budget (fun size => RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.preservesAt_match functions definitions registered extension program evidence
    entry_transport entry_binds budget faithful observations ?_ .reachable unique tree (GenericImperativeMatch.Tree.CatalogSites.of_catalog catalogValid ready)
  intro context valid child within
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews catalogValid unique uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects (budget : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code) := by
  apply RecursiveNamedImperativeFor.reflectsAt_match functions definitions registered extension program evidence
    entry_transport entry_binds budget ?_ faithful observations .reachable runtimeViews unique tree (GenericImperativeMatch.Tree.CatalogSites.of_catalog catalogValid ready)
  intro context valid child smaller
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child (Nat.le_of_lt smaller)

include definitions registered extension faithful observations runtimeViews catalogValid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The inclusive endpoint used by a source-body strong induction. No N+1
budget and no callee law at N is supplied by this consumer. -/
theorem concrete_preserves_at_top (size : Nat)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedLoopContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_preserves functions definitions registered extension faithful observations runtimeViews evidence catalogValid unique owners
    uninitialized missing bodyUninitialized bodyMissing size tree ready size (Nat.le_refl size)

include definitions registered extension faithful observations runtimeViews catalogValid unique uninitialized missing bodyUninitialized bodyMissing in
/-- A completed native body gives its own source size, without relating source
cost to the original native budget. -/
theorem concrete_native_only (budget size : Nat) (smaller : size < budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (ready : GenericImperativeMatch.Tree.ReachableReady registry faults tree) :
    RecursiveNamedLoopContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) mode statements expected type code :=
  concrete_reflects functions definitions registered extension faithful observations runtimeViews evidence catalogValid unique
    uninitialized missing bodyUninitialized bodyMissing budget tree ready size smaller
end Concrete




/-- For inclusion supplies the static site evidence without any catalog premise. -/
abbrev for_without_catalog := @GenericImperativeMatch.Tree.CatalogSites.of_for

/-- The same ordinary root context reconstructs readiness at every actual site. -/
abbrev same_ready := @GenericImperativeMatch.Tree.CatalogSites.ready

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let seen = value; return seen; }",
  "function fail(value: Word) returns (Word) { let seen = value; let gap: Word; return gap; }",
  "function nested(seed: Word) returns (Word) { let sum = 0; for (let i = 0; i < 2; i += 1) { match ((i, mark(seed))) { case (0, value) { sum += value; continue; } default { while (true) { match (i) { case 1 { sum += mark(3); break; } default { sum += 99; break; } } } } } } return sum; }",
  "function terminal(seed: Word) returns (Word) { for (; true; let dead = fail(99)) { match (seed) { case 0 { return mark(5); } default { return mark(7); } } } return 99; }",
  "function selectedFault(seed: Word) returns (Word) { match (seed) { case 0 { let prior = mark(11); return fail(prior); } default { return mark(13); } } }",
  "function scrutineeFault() returns (Word) { let prior = mark(17); match (fail(prior)) { case 0 { return 0; } default { return 1; } } }",
  "function duplicate(raw: mapping(Word => Word)) returns (Word) { match (mark(0)) { case 0 { raw[mark(1)] += mark(2); } default { raw[1] += 99; } } return raw[1]; }",
  "function armShadow(seed: Word) returns (Word) { let kept = seed; match ((0, kept)) { case (0, kept) { let local = mark(kept + 1); } default {} } return kept; }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cell (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))
private def pair (a b : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (word a) (word b)))
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(word 1, word n), (word 1, word 91)]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "whole match public resume" (first.resume 600000)).observation

/-- Actual nested match/loop code exercises both ordinary and terminal paths.
The expected complete heap records every call, hidden scrutinee and arm binder. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive whole match bounds" content
    ["nested", "terminal", "selectedFault", "scrutineeFault", "duplicate", "armShadow"]
  let failKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let failed ← get "whole match actual failing specialization" (SourceCompilationPlan.exactSpecialization compiled.validationPlan failKey)
  let gap ← match (SourceCoreDataPlaces.declaredBinders failed.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "whole match gap is not unique")
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (word 907)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × Nat × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("nested", [word 5], 8, [cell 5, cell 8, cell 2, cell 5, cell 5, pair 0 5, cell 5, cell 5, cell 5, pair 1 5, cell 1, cell 3, cell 3]),
    ("terminal", [word 0], 5, [cell 0, cell 0, cell 5, cell 5]),
    ("terminal", [word 1], 7, [cell 1, cell 1, cell 7, cell 7]),
    ("selectedFault", [word 1], 13, [cell 1, cell 1, cell 13, cell 13]),
    ("duplicate", [table 10], 12, [(.mapping .word .word, some (table 12)), cell 0, cell 0, cell 0, cell 1, cell 1, cell 2, cell 2]),
    ("armShadow", [word 4], 4, [cell 4, cell 4, pair 0 4, cell 4, cell 5, cell 5, cell 5])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 600000 initial
    for fuel in [0, 19, 113, 600000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"whole match resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr (word expected)) s!"whole match result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"whole match ordered cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"whole match expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("selectedFault", [word 0], [cell 0, cell 0, cell 11, cell 11, cell 11, cell 11, cell 11, (.word, none)]),
    ("scrutineeFault", [], [cell 17, cell 17, cell 17, cell 17, cell 17, (.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 600000 initial
    for fuel in [0, 19, 113, 600000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"whole match fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal id) final =>
        require (id == gap) "whole match lost the actual first callee fault"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"whole match fault cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"whole match expected fault {name}: {reprStr other}")
  IO.println "recursive named imperative match bounds: same Tree, nested match/for/while, selected Entry, terminal post skip, raw duplicate mapping, exact faults/cells and public resume GREEN"

end Tests.SourceCoreRecursiveNamedImperativeMatchBounds
