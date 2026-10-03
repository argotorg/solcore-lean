import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Concrete named expression Trees and actual selected For Trees close finite
match children. Reflection consumes no preservation law or prior source trace. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedMatchHeadBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates GenericMatchChildren
variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {program : SourceSemantics.Program}
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {bodies : NamedCallExpressions.Bodies prepared compilation.values ambient.definitions program}
  {calls : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {source : TypedSource} {context : SourceSemantics.Context} {control : ControlContext}
  {evidence : Dynamic.EvidenceEnvironment} {scope : Scope}
  {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionSyntax : ExpressionId → Prop} {requests : List Request} {code : Expr}
  (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    (NamedCallExpressions.Tree bodies calls fuel source context solved reasonAt) (Occurs requests) code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
  (valid : CompatiblePatternLeaves.ContextValid compilation context)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {caseFacts : List BodyFacts}
  (casesTyped : MatchCasesHaveType source control context node.type resolution.cases caseFacts)
  (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}


  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compilation.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  (trees : ∀ request, request ∈ requests → ∀ childContext,
    ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) node.type resolution.cases resolution.defaultBody request childContext →
    NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError calls fuel source expressionSyntax solved reasonAt administrative
      childContext request.scope (.statements false request.statements) expected type request.code)
  (errors : ∀ request member childContext related,
    GenericImperativeFor.Tree.ReachableErrors registry faults (trees request member childContext related))
include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing errors in
include owners in
theorem named_preserves (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedMatchSourceBounds.Head.HeadPreservesAt functions program evidence (values := compilation.values) (source := source) (context := context)
      (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults)
      (entry := NamedCallExpressions.Entry functions registry bodies calls.administrativePrefix)
      size (scope := scope) id expected type code := by
  apply GenericImperativeMatch.head_preserves_bounded onError allocator functions definitions registered extension receipt ordinary valid catalogValid found casesTyped defaultTyped unique budget size bounded
    (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
  · intro contextValid child smaller
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence contextValid
        uninitialized missing bodyUninitialized bodyMissing unique owners) child
  · intro request member childContext related child smaller
    exact RecursiveNamedImperativeFor.preserves_below functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
      budget
      (fun sourceContext contextValid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded
        (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence contextValid
          uninitialized missing bodyUninitialized bodyMissing unique owners) budget) faithful observations
      .reachable unique (trees request member childContext related) (errors request member childContext related) child smaller

include allocator definitions registered extension ordinary valid catalogValid found casesTyped defaultTyped faithful observations runtimeViews unique uninitialized missing bodyUninitialized bodyMissing errors in
theorem named_reflects (budget size : Nat) (bounded : size ≤ budget) :
    RecursiveNamedMatchSourceBounds.Head.HeadReflectsAt functions program evidence (values := compilation.values) (source := source) (context := context)
      (registry := registry) (solved := solved) (administrative := administrative)
      (frameLayout := frame) (globals := globals) (faults := faults)
      (entry := NamedCallExpressions.Entry functions registry bodies calls.administrativePrefix)
      size (scope := scope) id expected type code := by
  apply GenericImperativeMatch.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary valid catalogValid found casesTyped defaultTyped budget size bounded
    (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
  · intro contextValid child smaller
    exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence contextValid
        uninitialized missing bodyUninitialized bodyMissing) child
  · intro request member childContext related child smaller
    exact RecursiveNamedImperativeFor.reflectsAt_for functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies calls.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies calls.administrativePrefix)
      budget
      (fun sourceContext contextValid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded
        (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence contextValid
          uninitialized missing bodyUninitialized bodyMissing) budget) faithful observations
      .reachable runtimeViews unique (trees request member childContext related) (errors request member childContext related) child smaller

private def content : String := String.intercalate "\n" [
  "function mark(value: Word) returns (Word) { let seen = value; return seen; }",
  "function fail(value: Word) returns (Word) { let seen = value; let gap: Word; return gap; }",
  "function choose(seed: Word) returns (Word) { let kept = 5; match ((mark(seed), mark(7))) { case (0, value) { let selected = mark(value); return selected; } default { let selected = mark(9); return selected; } } }",
  "function bodyFault(seed: Word) returns (Word) { match ((mark(seed), 19)) { case (0, value) { let prior = mark(value); return fail(prior); } default { return mark(23); } } }",
  "function scrutineeFault() returns (Word) { match (fail(3)) { case 0 { return mark(29); } default { return mark(31); } } }",
  "function emptyDefault(seed: Word) returns (Word) { match (seed) { case 0 { let selected = mark(1); } default {} } return mark(17); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def cell (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (word n))
private def pair (a b : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value :=
  (.product .word .word, some (.product (word a) (word b)))
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "match finite head public resume" (first.resume 400000)).observation

/-- Full ordered heaps distinguish scrutinee calls, selected-arm calls and
first faults. Unselected bodies execute no calls or source allocations. -/
def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive match head bounds" content
    ["choose", "bodyFault", "scrutineeFault", "emptyDefault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (word 907)⟩]}
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"
  let failed ← get "actual failed callee" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  let gap ← match (SourceCoreDataPlaces.declaredBinders failed.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "match finite head fault binder missing")
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("choose", [word 0], word 7, [cell 0, cell 5, cell 0, cell 0, cell 7, cell 7, pair 0 7, cell 7, cell 7, cell 7, cell 7]),
    ("choose", [word 2], word 9, [cell 2, cell 5, cell 2, cell 2, cell 7, cell 7, pair 2 7, cell 9, cell 9, cell 9]),
    ("bodyFault", [word 1], word 23, [cell 1, cell 1, cell 1, pair 1 19, cell 23, cell 23]),
    ("emptyDefault", [word 0], word 17, [cell 0, cell 0, cell 1, cell 1, cell 1, cell 17, cell 17]),
    ("emptyDefault", [word 2], word 17, [cell 2, cell 2, cell 17, cell 17])]
  for (name, arguments, expected, cells) in successes do
    let baseline ← finish compiled name arguments 400000 initial
    for fuel in [0, 17, 97, 400000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match head resume changed {name}"
      match observed with
      | .done result final =>
        require (reprStr result == reprStr expected) s!"match head result changed {name}"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match head ordered source cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"match head expected success {name}: {reprStr other}")
  let failures : List (String × List SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("bodyFault", [word 0], [cell 0, cell 0, cell 0, pair 0 19, cell 19, cell 19, cell 19, cell 19, cell 19, cell 19, (.word, none)]),
    ("scrutineeFault", [], [cell 3, cell 3, (.word, none)])]
  for (name, arguments, cells) in failures do
    let baseline ← finish compiled name arguments 400000 initial
    for fuel in [0, 17, 97, 400000] do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"match head fault resume changed {name}"
      match observed with
      | .fault (.uninitializedLocal id) final =>
        require (id == gap) "match head did not retain the actual first callee fault"
        require (reprStr final.heap == reprStr (initial.heap ++ cells.map (fun (type, value) => ⟨type, value⟩)))
          s!"match head fault cells changed {name}: {reprStr final.heap}"
      | other => throw (IO.userError s!"match head expected first fault {name}: {reprStr other}")
  IO.println "recursive named match head bounds: actual named scrutinee/arm/default calls, emptyDefault, exact first fault and ordered cells/resume GREEN"

end Tests.SourceCoreRecursiveNamedMatchHeadBounds
