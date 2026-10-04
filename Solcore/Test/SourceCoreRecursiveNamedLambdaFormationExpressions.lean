import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.Test.SourceCoreUnifiedCorpusSupport
import Solcore.Test.SourceCompilerFeatureSupport

/-! Formation is a leaf of the same whole expression tree and survives inside
actual named callees in one fixed runtime value model. The lambda body receipt
covers the concrete builtin statement grammar; indirect application and a
combined named/anonymous recursive body theorem remain separate boundaries.
Independent source frames, full history, actual compilation and static child
receipts are retained. Native typing supplies only used-prefix type agreement.
The original canonical and actual unused administrative suffixes remain full. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedLambdaFormationExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open RecursiveNamedLambdaFormationHeads
open RecursiveNamedLambdaFormationTreeMeaning

abbrev actual_contextual_site := @CallableIndexedLambdaGeneration.of_contextual
abbrev actual_static_body := @CallableIndexedLambdaRuntimeBody.Body.of_tree
abbrev same_site_head := @RecursiveNamedLambdaFormationHeads.Lambda.of_site
abbrev actual_body_extraction := @RecursiveNamedCatalogRuntimeProfileFactory.formation_provider

section Actual
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

abbrev Calls (authenticated : Bool) := Head (registry := registry) (faults := faults) caller context evidence
  (RecursiveNamedCallEvidenceHeads.Calls (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (if authenticated then some evidence else none) headers
    (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context)

abbrev Expressions (authenticated : Bool) :=
  RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor (Calls (caller := caller) (headers := headers)
    (context := context) (evidence := evidence) (registry := registry) (faults := faults) authenticated)
    fuel values caller.function.source context solved reasonAt

variable {expressionSyntax : Header indexed.ancestry values indexed.layouts.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : values.checked.catalog.callableContracts = true)
variable (authenticated : Bool)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers locations 0 (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header
        arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost) →
      RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry →
      RecursiveNamedCatalogMutualMeaning.FormationProfile (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) authenticated header
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))


include complete alignments extension owners uninitialized missing escaped profiles in
theorem actual_preserves_at
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  have receipt := RecursiveNamedLambdaFormationTreeMeaning.of_functions authenticated alignment
    admission coverage sourceTypes emptyEvidence order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions lambdas allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_preserves_at_formation
    (locations := locations) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    profile authenticated complete alignments extension owners uninitialized missing escaped profiles
    alignment valid callerUninitialized callerMissing size receipt rootFound


include complete alignments extension uninitialized missing escaped profiles in
theorem actual_reflects_at
    (alignment : RecursiveNamedLambdaFormationEntries.FormationHeader
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
      (CallableIndexedNamedGeneration.context indexed caller.named) 0)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {admitted : ExpressionId → Prop}
    (admission : AdmissionFor lambdaForm caller.function.source admitted) (coverage : ReachedCoverage headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers context)
    (emptyEvidence : SelectedEmptyEvidence (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source admitted)
    (order : ∀ id callee arguments instantiation node, admitted id → caller.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered (CallableIndexedNamedGeneration.context indexed caller.named).plan instantiation)
    (unique : NodeOccurrencesUnique caller.function.source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations caller.function.source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw caller.function.source context (CompatibleExpressionBuiltins.Syntax caller.function.source))
    (selectedValid : SelectedDeclarationLaw (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source context admitted)
    (policyFor : PolicyForWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (headers := headers) (if authenticated then some evidence else none) policy (CallableIndexedNamedGeneration.context indexed caller.named) readFuel values caller.function.source context scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callableProfile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax caller.function.source id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → caller.function.source.lookupExpression? id = some node → node.coercions = [])
    (lambdas : ∀ fuel id node lowered, admitted id → caller.function.source.lookupExpression? id = some node →
      lambdaForm node.form → ExpressionHasType caller.function.source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
        (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered →
      Nonempty (Lambda (registry := registry) (faults := faults) caller context evidence scope id lowered))
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : caller.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType caller.function.source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel (CallableIndexedNamedGeneration.context indexed caller.named) caller.function.source scope id reasonAt = .ok lowered)
    (valid : CompatibleRuntimeContextValidity.Valid (CallableIndexedNamedGeneration.context indexed caller.named).solvedRequirements context evidence)
    (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (fun current expression code => current = scope ∧ expression = id ∧ code = lowered) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  have receipt := RecursiveNamedLambdaFormationTreeMeaning.of_functions authenticated alignment
    admission coverage sourceTypes emptyEvidence order unique declarations signatures constructorValid fragmentValid selectedValid
    policyFor native active callableProfile fragmentCoercions coercions lambdas allowed found typed accepted
  intro current expression code same
  obtain ⟨rfl, rfl, rfl⟩ := same
  intro root rootFound
  exact RecursiveNamedCatalogMutualMeaning.expression_reflects_at_formation
    (locations := locations) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy)
    profile authenticated complete alignments extension uninitialized missing escaped profiles
    alignment valid callerUninitialized callerMissing size receipt rootFound

end Actual

section Boundaries
/-- One global reference and a separate frame reference remain in the used
prefix while an arbitrary extra Bool or Unit field stays unconstrained. -/
theorem nonempty_global_unused_suffix :
    NativeExpressionContextSupport.Agrees 3
      [.word, .cell (.function .word .word), .cell .unit]
      [.word, .cell (.function .word .word), .cell .unit, .bool] ∧
    NativeExpressionContextSupport.Agrees 3
      [.word, .cell (.function .word .word), .cell .unit]
      [.word, .cell (.function .word .word), .cell .unit, .unit] ∧
    ([.word, .cell (.function .word .word), .cell .unit, .bool] : Core.Context) ≠
      [.word, .cell (.function .word .word), .cell .unit, .unit] := by
  refine ⟨?_, ?_, by decide⟩
  all_goals
    intro index smaller
    cases index with
    | zero => rfl
    | succ index =>
      cases index with
      | zero => rfl
      | succ index =>
        have same : index = 0 := by omega
        subst index
        rfl

abbrev aligned_callee := @RecursiveNamedLambdaFormationEntries.authorize
abbrev original_creation_reference := @RecursiveNamedLambdaFormationHeads.Lambda.reference_index
abbrev native_used_prefix := @RecursiveNamedLambdaFormationHeads.entry_prefix
abbrev full_actual_captures := @RecursiveNamedLambdaFormationHeads.captures
abbrev closed_callee_preserves := @RecursiveNamedCatalogMutualMeaning.preserves_at_formation
abbrev closed_callee_reflects := @RecursiveNamedCatalogMutualMeaning.reflects_at_formation
end Boundaries

private def content := String.intercalate "\n" [
  "type F = function(Word) returns (Word);",
  "function maker(seed: Word) returns(F) { return lam(item: Word) -> Word { return seed + item; }; }",
  "function keeper(value: F) returns(F) { return value; }",
  "function caller(seed: Word) returns(F) { return keeper(maker(seed)); }",
  "function stored(seed: Word) returns(F) { let value: F = maker(seed); return value; }",
  "function pair(seed: Word) returns(F,F) { return (maker(seed), lam(item: Word) -> Word { return seed + item; }); }",
  "function branch(seed: Word) returns(F) { if(seed == 0) { return lam(item: Word) -> Word { return item; }; } else { return lam(item: Word) -> Word { return seed + item; }; } }",
  "function zero(seed: Word) returns(function() returns(Word)) { return lam() -> Word { { return seed; } }; }",
  "function fail() returns(Word) { let written = 5; let gap: Word; return gap; }",
  "function firstFault(seed: Word) returns(Word,F,F) { return (fail(), maker(seed), maker(9)); }",
  "function laterFault(seed: Word) returns(F,Word,F) { return (maker(seed), fail(), maker(9)); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- These are actual accepted contextual lambda leaves, with their original
callback, complete source metadata, physical globals and compiler child fuel. -/
private def leaf_codes (compiled : SourceCoreUnifiedCompilation.Compiled) : IO (List (Word × SourceCoreBasic.LoweredExpr × Core.Context)) := do
  let prepared := compiled.indexed
  require (!prepared.base.globals.isEmpty) "formation nonempty globals absent"
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "formation diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "formation original parent contexts" (SourceCoreStageCodebook.prepareContexts
    prepared.base.sourceProgram prepared.base.plan (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut leaves := []
  for named in prepared.base.functions do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "formation own diagnostics missing")
    let source := CallableIndexedNamedGeneration.source named
    let compilation := CallableIndexedNamedGeneration.context prepared named
    require (compilation.administrativePrefix == 1 && compilation.globals == prepared.base.globals)
      "formation caller bundle prefix/full globals changed"
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics compilation
      prepared.base.callableContext none none
    let leading :=  SourceCoreLocalCell.coreContext scope ++ named.signature.parameterType ::
      prepared.base.globals.map (·.referenceType) ++ [.cell prepared.ancestry.layout.frame.type]
    for item in source.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .lambda parameters result body =>
          let code ← get "formation actual leaf acceptance" (lower prepared.fuel source scope node.id reasonAt)
          let descriptor ← get "formation actual descriptor" (SourceCoreCallableContracts.descriptor
            prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner node.id []))
          require (Core.infer? leading code.expression prepared.layouts.definitions == some (LanguageResult.resultType code.type))
            "formation used prefix typing failed"
          for suffix in [[.bool], [.unit, .function .unit .unit]] do
            require (Core.infer? (leading ++ suffix) code.expression prepared.layouts.definitions ==
              some (LanguageResult.resultType code.type)) "formation arbitrary unused admin suffix typing changed"
          require (node.requirements.isEmpty && node.coercions.isEmpty &&
            node.type == TypeSystem.Ty.function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result && !body.isEmpty)
            "formation original source annotation/requirements/body changed"
          require (scope.length == 1) "formation fixture exact lexical parameter scope changed"
          leaves := leaves ++ [(descriptor.id, code, leading)]
        | _ => pure ()
      | _ => pure ()
  require (leaves.length == 5) s!"formation actual accepted leaf count {leaves.length}"
  pure leaves

/-- Formation executes the original emitted leaf in the actual captured prefix,
with extra unused native fields retained. This harness does not construct source
history or infer any Entry identity from the captured environment. -/
private def formation_suffix (compiled : SourceCoreUnifiedCompilation.Compiled)
    (leaves : List (Word × SourceCoreBasic.LoweredExpr × Core.Context)) (native : Value) (store : Store) : IO Nat := do
  let prepared := compiled.indexed
  let rec visit (fuel : Nat) (native : Value) : IO Nat := do
    match fuel with
    | 0 => throw (IO.userError "formation native payload traversal budget")
    | fuel + 1 =>
      match native with
      | .pair (.pair marker (.closure parameter result executable (lexical :: actual))) (.word origin) =>
        match leaves.find? (fun leaf => leaf.1 == origin) with
        | none => throw (IO.userError "formation returned lambda origin lacks original leaf")
        | some leaf =>
          let canonicalTypes := leaf.2.2
          let lexicalIndex := (actual.map Value.type).idxOf (canonicalTypes.headD .unit)
          let globalStart := actual.length - (prepared.base.globals.length + 1)
          let embedding : Renaming := fun index =>
            if index == 0 then lexicalIndex else if index == 1 then lexicalIndex + 1
            else globalStart + index - 2
          require (canonicalTypes.zipIdx.all (fun slot => (actual.map Value.type)[embedding slot.2]? == some slot.1))
            "formation actual original lexical/global/frame prefix types changed"
          let location ← match actual[embedding (canonicalTypes.length - 1)]? with
            | some (.cellRef type location) =>
              require (type == prepared.ancestry.layout.frame.type) "formation physical frame type changed"
              pure location
            | _ => throw (IO.userError "formation actual frame reference absent")
          let installed := store.set location lexical
          let inert := Value.closure .unit .unit (.var 0) [.word (Word.ofNatModulo 991), .bool true]
          for suffix in [[.bool false], [.unit, inert]] do
            let environment := actual ++ suffix
            require (Core.infer? (environment.map Value.type) (leaf.2.1.expression.rename embedding) prepared.layouts.definitions ==
              some (LanguageResult.resultType leaf.2.1.type)) "formation full actual environment typing changed"
            match runStateful 300000 (.initial (leaf.2.1.expression.rename embedding) environment installed) with
            | .done (.inRight .word (.pair (.pair actualMarker (.closure actualParameter actualResult actualCode captures)) (.word actualOrigin))) after =>
              require (actualMarker == marker && actualParameter == parameter && actualResult == result &&
                actualCode == executable && actualOrigin == origin && captures == lexical :: environment && after == installed)
                "formation lost full ordered actual captures/unused suffix/original code/store"
            | other => throw (IO.userError s!"formation original leaf did not complete {reprStr other}")
          pure 1
      | .pair left right => return (← visit fuel left) + (← visit fuel right)
      | _ => pure 0
  visit 100 native

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (root : SourceSpecialization.SpecializationKey)
    (fuel : Nat) : IO (String × String × Bool × Nat) := do
  let first ← get "formation original startup" (compiled.run root [.word (Word.ofNatModulo 3)] 1024 fuel)
  let final ← get "formation original resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "formation original execution missing")
  let native := execution.completion.result.native.observation
  match native with
  | .succeeded _ store => pure (reprStr final.observation, reprStr native, false, store.length)
  | .failed _ store => pure (reprStr final.observation, reprStr native, true, store.length)
  | _ => throw (IO.userError "formation original execution incomplete")

def run : IO Unit := do
  let program ← get "formation actual checker" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["maker", "caller", "stored", "pair", "branch", "zero", "firstFault", "laterFault"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let compiled ← get "formation actual public Core compiler" (SourceCoreCompiler.compileChecked program
    (roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration [])
    {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with
    | some cached => pure cached | none => throw (IO.userError "formation original cached artifact absent")
  require (cached.keys == roots) "formation actual ordered roots changed"
  let leaves ← leaf_codes cached
  let failureKey ← SourceCoreUnifiedCorpusSupport.key program "fail"
  let failureSource ← get "formation original fault source" (SourceCompilationPlan.exactSpecialization cached.indexed.base.plan failureKey)
  let missing ← match (SourceCoreDataPlaces.declaredBinders failureSource.function.typedBody).filter (·.name == "gap") with
    | [binder] => pure binder.id | _ => throw (IO.userError "formation original missing binder absent")
  let mut formed := 0
  let mut faultSizes := []
  for (name, root) in names.zip roots do
    let baseline ← finish cached root 300000
    require (baseline.2.2.1 == (name == "firstFault" || name == "laterFault")) "formation success/fault boundary changed"
    for fuel in [0, 1, 31, 300000] do
      require ((← finish cached root fuel) == baseline) "formation full source/native store or resume changed"
    let actual ← get "formation actual indexed invocation" (cached.indexed.runSource root [.word (Word.ofNatModulo 3)] 300000)
    match actual.result.native.observation with
    | .succeeded native store => formed := formed + (← formation_suffix cached leaves native store)
    | .failed token store =>
      let diagnostic ← match actual.result.diagnostics.diagnostic? token with
        | some diagnostic => pure diagnostic | none => throw (IO.userError "formation exact diagnostic absent")
      require (diagnostic.error == .uninitializedLocal missing) "formation exact first missing binder changed"
      let ledger ← get "formation original full ordered ledger" (SourceCoreAllocationLedger.scan cached.indexed.layouts [] store)
      require (ledger.pending.isNone && ledger.rows.any (fun row => row.entry.key.binder.name == "gap" && row.payload.isNone) &&
        ledger.rows.any (fun row => row.entry.key.binder.name == "written" && row.payload == some (.word (Word.ofNatModulo 5))))
        "formation first missing binder/prior ordered writes changed"
      let expected := if name == "firstFault" then
          [("seed", some (Value.word (Word.ofNatModulo 3))), ("written", some (.word (Word.ofNatModulo 5))), ("gap", none)]
        else [("seed", some (Value.word (Word.ofNatModulo 3))), ("seed", some (.word (Word.ofNatModulo 3))),
          ("written", some (.word (Word.ofNatModulo 5))), ("gap", none)]
      require (ledger.rows.map (fun row => (row.entry.key.binder.name, row.payload)) == expected)
        "formation original first/later fault full ordered source cells changed"
      faultSizes := faultSizes ++ [(name, store.length)]
    | _ => throw (IO.userError "formation indexed invocation incomplete")
  require (formed == 7) s!"formation returned lambda audit count {formed}"
  require (faultSizes.length == 2) "formation first/later fault cases absent"
  IO.println "lambda formation: actual whole compiler and named callee; nonempty globals/caller bundle/frame; complete raw metadata/captures/unused admin suffix; original full store/fault/resume GREEN"

end Tests.SourceCoreRecursiveNamedLambdaFormationExpressions
