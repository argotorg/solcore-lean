import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
import Solcore.Test.SourceCoreRecursiveNamedExpressionBounds
import Solcore.Frontend.SourceCoreCompiler
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration

/-! Actual named compiler success returns support for the same complete Tree.
Final bounded consumers use the whole runtime ledger, without caller ordinary
validity or an expression runtime premise. Callee BodyBelow and static source,
policy, coverage and constructor conditions remain explicit at this boundary.
Arbitrary tuple arities preserve ordered compiler children; source types and
callee BodyBelow remain independent inputs. Singleton retained IR audits below
do not claim parser or checker provenance. -/
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedTupleExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates

abbrev actual_contextual_tree := @RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_at_runtime_admission

section ActualCompilation
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : RecursiveNamedCatalog.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}
  {locations : Locations} {capturePrefix : Nat}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

include extension faithful functionLeaves functionTypes in
theorem actual_functions_preserves_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_admission
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime functions extension faithful functionLeaves functionTypes
    evidence unique owners uninitialized missing sameLedger runtime budget size within bodies receipt rootFound


include extension faithful functionLeaves functionTypes in
theorem actual_functions_reflects_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : RuntimeAdmission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered)
    (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
    (runtime : RuntimeRequirementLedgerValid context)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (budget size : Nat) (within : size ≤ budget)
    (bodies : ∀ header, header ∈ headers → RecursiveNamedBoundedContracts.Below budget
      (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults)) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have receipt := RecursiveNamedExpressionCompilerCertificates.tree_of_functions_at_runtime_admission
    admission coverage sourceTypes order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active profile fragmentCoercions coercions allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime functions extension faithful functionLeaves functionTypes
    evidence uninitialized missing sameLedger runtime budget size within bodies receipt rootFound

end ActualCompilation

section Boundaries
variable (a b c d : ExpressionId)

theorem old_tuple3_negative : ¬ compositionForm (.tuple [a, b, c]) := by
  simp [compositionForm]

theorem runtime_singleton : runtimeCompositionForm (.tuple [a]) := by
  exact Or.inr ⟨[a], rfl⟩

theorem runtime_tuple3 : runtimeCompositionForm (.tuple [a, b, c]) := by
  exact Or.inr ⟨[a, b, c], rfl⟩

theorem runtime_tuple4 : runtimeCompositionForm (.tuple [a, b, c, d]) := by
  exact Or.inr ⟨[a, b, c, d], rfl⟩

theorem old_singleton_negative : ¬ compositionForm (.tuple [a]) := by
  simp [compositionForm]
end Boundaries

private def content : String := String.intercalate "\n" [
  "function side(x: Word) returns (Word) { return x; }",
  "function fail() returns (Word) { let written = 5; let gap: Word; return gap; }",
  "function triple() returns ((Word, Bool, Word)) { return (side(7), true, 3 + 4); }",
  "function quadruple() returns ((Word, Bool, Word, Bool)) { return (side(11), false, side(13), true); }",
  "function nested() returns (((Word, Bool, Word), Word, Bool)) { return ((side(17), true, 5 + 6), side(19), false); }",
  "function firstFault() returns ((Word, Word, Word)) { return (fail(), side(91), side(92)); }",
  "function laterFault() returns ((Word, Word, Word, Word)) { return (side(23), side(29), fail(), side(99)); }",
  "function singleton() returns (Word) { return (side(31)); }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- Re-enter the actual contextual expression compiler, retaining exact ordered
children, including repeated IDs. Only the last singleton/duplicate audit uses
modified retained IR; it does not claim parser/checker provenance. -/
private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) (names : List String) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "tuple diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "tuple parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut triples := 0
  let mut quadruples := 0
  let mut singletons := 0
  let mut duplicates := 0
  for named in prepared.base.functions do
    let original ← match prepared.base.sourceProgram.signatures.functions.find? (·.id == named.signature.key.declaration) with
      | some signature => pure signature | none => throw (IO.userError "tuple original signature missing")
    if names.contains original.name then
      let own ← match diagnostics.base.find? named.signature.key with
        | some own => pure own | none => throw (IO.userError "tuple own diagnostics missing")
      let source := CallableIndexedNamedGeneration.source named
      let compilation := CallableIndexedNamedGeneration.context prepared named
      let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
      let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
      let reasonAt := diagnostics.reasonAt named.signature.key
      let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
        prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
        prepared.base.callableContext none none
      let nativeContext := SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
        prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
      for item in source.nodes do
        match item with
        | .expression node =>
          match node.form with
          | .tuple ids =>
            let code ← get "actual tuple lowering" (lower prepared.fuel source scope node.id reasonAt)
            let codes ← ids.mapM (fun id => get "ordered tuple child" (lower (prepared.fuel - 1) source scope id reasonAt))
            require (code == SourceCoreCalls.packArguments codes && codes.length == ids.length)
              "tuple actual ordered pack/code vector changed"
            require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
              "tuple actual native type lost"
            require (node.coercions.isEmpty && node.requirements.isEmpty)
              "tuple parent evidence/coercions changed"
            if ids.length == 3 then triples := triples + 1
            if ids.length == 4 then quadruples := quadruples + 1
          | .group child =>
            if original.name == "singleton" then
              let childNode ← match source.lookupExpression? child with
                | some childNode => pure childNode | none => throw (IO.userError "singleton actual operand missing")
              let retained := {source with nodes := source.nodes.map (fun item => match item with
                | .expression current => if current.id == node.id then
                    .expression {current with form := .tuple [child], type := childNode.type, requirements := [], coercions := []}
                  else item
                | _ => item)}
              let code ← get "retained singleton tuple lowering" (lower prepared.fuel retained scope node.id reasonAt)
              let childCode ← get "retained singleton original child" (lower (prepared.fuel - 1) retained scope child reasonAt)
              require (code == SourceCoreCalls.packArguments [childCode]) "retained singleton exact code changed"
              require (Core.infer? nativeContext code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
                "retained singleton native type lost"
              singletons := singletons + 1
              let repeated := {retained with nodes := retained.nodes.map (fun item => match item with
                | .expression current => if current.id == node.id then
                    .expression {current with form := .tuple [child, child, child], type := TypeSystem.Ty.productMany [childNode.type, childNode.type, childNode.type], requirements := [], coercions := []}
                  else item
                | _ => item)}
              let repeatedCode ← get "retained repeated tuple lowering" (lower prepared.fuel repeated scope node.id reasonAt)
              let repeatedChild ← get "retained repeated tuple child" (lower (prepared.fuel - 1) repeated scope child reasonAt)
              require (repeatedCode == SourceCoreCalls.packArguments [repeatedChild, repeatedChild, repeatedChild])
                "retained repeated IDs/order/code changed"
              require (Core.infer? nativeContext repeatedCode.expression prepared.layouts.definitions == some (LanguageResult.resultType repeatedCode.type))
                "retained repeated tuple native type lost"
              duplicates := duplicates + 1
          | _ => pure ()
        | _ => pure ()
  require (triples == 4 && quadruples == 2 && singletons == 1 && duplicates == 1)
    s!"tuple actual coverage changed {triples}/{quadruples}/{singletons}/{duplicates}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO (SourceTypedRuntime.RunResult × String) := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  let final ← get "tuple actual native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "tuple original native execution missing")
  let native := execution.completion.result.native.observation
  match native with
  | .succeeded _ store | .failed _ store =>
    require (!store.isEmpty) "tuple full installed store lost"
  | _ => throw (IO.userError "tuple original native completion missing")
  pure (final.observation, reprStr native)

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "tuple original source heap prefix changed"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"tuple full ordered source heap changed: {reprStr final.heap}"

def run : IO Unit := do
  let names := ["triple", "quadruple", "nested", "firstFault", "laterFault", "singleton"]
  let program ← get "tuple actual checked source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let keys ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let publicCompilation ← get "tuple actual public Core compilation" (SourceCoreCompiler.compileChecked program
    (keys.map (fun key => SourceCoreCompiler.Seed.declaration key.declaration))
    {specializationBudget := 512, compilationFuel := 1000})
  let compiled ← match publicCompilation.artifact? with
    | some compiled => pure compiled | none => throw (IO.userError "tuple actual public compilation has no cached artifact")
  require (compiled.keys == keys) "tuple actual public root order changed"
  inspect compiled names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("triple", .product (w 7) (.product (.bool true) (w 7)), [(.word, some (w 7))]),
    ("quadruple", .product (w 11) (.product (.bool false) (.product (w 13) (.bool true))),
      [(.word, some (w 11)), (.word, some (w 13))]),
    ("nested", .product (.product (w 17) (.product (.bool true) (w 11))) (.product (w 19) (.bool false)),
      [(.word, some (w 17)), (.word, some (w 19))]),
    ("singleton", w 31, [(.word, some (w 31))])]
  let complete ← successes.mapM (fun test => finish compiled test.1 300000 initial)
  let failed ← ["firstFault", "laterFault"].mapM (fun name => finish compiled name 300000 initial)
  for fuel in [0, 1, 43, 300000] do
    for (test, baseline) in successes.zip complete do
      let (name, expected, expectedCells) := test
      let actual ← finish compiled name fuel initial
      require (reprStr actual == reprStr baseline) "tuple full native/source heap/resume changed"
      match actual.1 with
      | .done result final =>
        require (reprStr result == reprStr expected) "tuple actual product result/order changed"
        cells initial final expectedCells
      | other => throw (IO.userError s!"tuple success changed {reprStr other}")
    for (name, baseline) in ["firstFault", "laterFault"].zip failed do
      let actual ← finish compiled name fuel initial
      require (reprStr actual == reprStr baseline) "tuple full native fault/resume changed"
      match actual.1 with
      | .fault (.uninitializedLocal _) final =>
        let earlier := if name == "laterFault" then [(.word, some (w 23)), (.word, some (w 29))] else []
        cells initial final (earlier ++ [(.word, some (w 5)), (.word, none)])
      | other => throw (IO.userError s!"tuple first/later fault changed {reprStr other}")
  IO.println "recursive named tuples: actual public tuple3/4/nested named+builtin / ordered pack / retained singleton+duplicate IR (parser provenance unproved) / full heap+native store / first-later fault+four resume budgets GREEN"

end Tests.SourceCoreRecursiveNamedTupleExpressions
