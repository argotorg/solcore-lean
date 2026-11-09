import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.OrdinaryCallsReady
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.Core.Safety
import Solcore.Core.Fuel
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.Frontend.SourceCore.Internal.CallablePaired
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.MethodOrigins
import Solcore.Frontend.SourceCore.Internal.CallablePrincipals
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.Frontend.SourceCore.Internal.CallableAncestry
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.ViewWrappers

/-!
# Paired callable tests

Paired frames, headers, outputs and restoration, callable contracts, views, shared history and
authenticated calls.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAuthenticatedCallEvidence
/-! Reached evidence validity comes from actual caller resolution, ordered
materialization and callee authentication. Unrelated invalid templates, exact
coercion placement and contextual local rebinding remain distinguishable. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableAuthenticatedCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableNamedMetadata (evidence environment)

/-- Successful public direct-call selection determines both independent
production and the exact source dictionary, without whole-ledger validity. -/
theorem actual_direct_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : SourceSemantics.Context}
    {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    Dynamic.DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates (environment actual) ∧
      ∀ semantic, Dynamic.DirectCallProducesEvidence context (environment available) node.requirements node.coercions instantiation.predicates semantic →
        semantic = environment actual :=
  ⟨CallableCallRequirementLayouts.direct_produces signatures ledger assumptions resolved accepted authenticated,
    fun _ produced => CallableCallRequirementLayouts.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) accepted produced⟩

theorem actual_reference_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {available actual : SourceTypedRuntime.RuntimeEvidenceEnvironment} {context : SourceSemantics.Context}
    {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation = .ok actual)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee instantiation.predicates actual = .ok ()) :
    (∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
      Dynamic.RequirementsProduceEnvironment context (environment available) ids instantiation.predicates (environment actual)) ∧
    ∀ ids semantic, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids →
      Dynamic.RequirementsProduceEnvironment context (environment available) ids instantiation.predicates semantic → semantic = environment actual :=
  ⟨CallableCallRequirementLayouts.reference_produces signatures ledger assumptions resolved accepted authenticated,
    fun _ _ layout produced => CallableCallRequirementLayouts.reference_agrees ledger accepted layout produced⟩

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntWordRule.head
private def otherGoal : ProgramPredicate := ProgramSignatures.builtinIntIntegerRule.head
private def raw : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intWord) []
private def validRow : SolvedRequirement := ⟨⟨0⟩, goal, .implementation raw⟩
private def invalidRow : SolvedRequirement := ⟨⟨99⟩, goal, .assumption otherGoal⟩
private def rows := [validRow, invalidRow, invalidRow]
private def context : SourceSemantics.Context := {signatures, locals := [], assumptions := [], solvedRequirements := rows}
private def callerWith (seed : SourceSpecialization.SpecializedFunction) :=
  {seed with assumptions := [], function := {seed.function with solvedRequirements := rows}}

/-- Successful real receipts prove the reached row even though the unused
ledger includes duplicated, internally misaligned assumption templates. -/
theorem reached_only (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    Dynamic.RequirementsProduceEnvironment context [] [⟨0⟩] [goal] (environment [raw]) ∧
      ¬ SolvedRequirementsValid context rows := by
  have produced := CallableAuthenticatedCallEvidence.produces (program := {program with signatures := signatures})
    (caller := callerWith seed) (callee := seed.key) (context := context)
    (occurrence := occurrence) (available := []) (result := [raw])
    (ids := [⟨0⟩]) (predicates := [goal]) rfl rfl (by simp [callerWith]) rfl rfl rfl
  refine ⟨produced, ?_⟩
  intro allValid
  have impossible := (allValid invalidRow (by simp [rows])).evidence_goal_eq
  cases impossible

/-- Repeated requested IDs and repeated goals keep both output positions;
caller first-match lookup does not erase the ordered result multiplicity. -/
theorem repeated_authenticated (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    let assumed : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
    let caller := {seed with assumptions := [goal, goal], function := {seed.function with solvedRequirements := [assumed, invalidRow]}}
    let context : SourceSemantics.Context := {signatures, locals := [], assumptions := [goal], solvedRequirements := [assumed, invalidRow]}
    SourceCompilationPlan.materializeCallEvidence caller occurrence [raw, raw] [⟨0⟩, ⟨0⟩] [goal, goal] = .ok [raw, raw] ∧
    Dynamic.RequirementsProduceEnvironment context (environment [raw, raw]) [⟨0⟩, ⟨0⟩] [goal, goal] (environment [raw, raw]) := by
  dsimp only
  refine ⟨rfl, ?_⟩
  exact CallableAuthenticatedCallEvidence.produces (program := {program with signatures := signatures})
    (caller := {seed with assumptions := [goal, goal], function := {seed.function with solvedRequirements := [⟨⟨0⟩, goal, .assumption goal⟩, invalidRow]}})
    (callee := seed.key) (occurrence := occurrence) rfl rfl (by simp) rfl rfl rfl

/-- Goal alignment alone cannot authenticate a different implementation tree. -/
theorem same_goal_different_selection_rejected (key : SourceCompilationPlan.Key) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence signatures key [goal]
      [.byImpl goal (.builtin .intInteger) []] =
      .error (.runtimeEvidenceNotSelected key 0 goal (.builtin .intInteger)) := rfl

private def step (id : Nat) : CoercionStep := {requirement := ⟨id⟩, source := .word, target := .word}
private def middleNode (seed : ExpressionNode) := {seed with requirements := [⟨10⟩, ⟨0⟩, ⟨11⟩], coercions := [step 10, step 11]}

/-- Both sides of the owned middle are retained. The compiler only materializes
ID 0, so the two coercion IDs need no callee dictionary rows. -/
theorem actual_middle (program : CheckedProgram) (seed : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    SourceCompilationPlan.exactDirectCallRuntimeEvidence (callerWith seed) (middleNode node) []
      {instantiation with predicates := [goal]} = .ok [raw] ∧
    Dynamic.DirectCallProducesEvidence context [] (middleNode node).requirements (middleNode node).coercions [goal] (environment [raw]) := by
  have accepted : SourceCompilationPlan.exactDirectCallRuntimeEvidence (callerWith seed) (middleNode node) []
      {instantiation with predicates := [goal]} = .ok [raw] := rfl
  exact ⟨accepted, CallableCallRequirementLayouts.direct_produces (program := {program with signatures := signatures})
    (callee := seed.key) rfl rfl (by simp [callerWith]) rfl accepted rfl⟩

theorem reference_repeated_coercions (node : ExpressionNode) :
    Dynamic.OrdinaryRequirementLayout [⟨0⟩, ⟨10⟩, ⟨10⟩] [step 10, step 10] [⟨0⟩] :=
  CallableCallRequirementLayouts.ordinary_owned (node := {node with requirements := [⟨0⟩, ⟨10⟩, ⟨10⟩], coercions := [step 10, step 10]}) rfl

/-- The authenticated entrance applies to the actual local rewrite, retaining
its exact source ledger and the original caller assumptions. It does not
require template rows outside the selected call to acquire validity. -/
theorem local_rebinding_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {substitution : TypeSystem.Substitution} {witnesses : List SourceCoreLocalEvidence.Witness}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : SourceSemantics.Context} {callee : SourceCompilationPlan.Key}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = SourceCoreLocalEvidence.rewriteLedger substitution witnesses caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence (SourceCoreLocalEvidence.contextualCaller caller substitution witnesses)
      occurrence available ids predicates = .ok result)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures callee predicates result = .ok ()) :
    Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates (environment result) :=
  CallableAuthenticatedCallEvidence.produces (caller := SourceCoreLocalEvidence.contextualCaller caller substitution witnesses)
    signatures ledger assumptions resolved accepted authenticated

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = value ? 40 : 6; table[0] += 2; return table[0]; } }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function forward<T>(value: T) returns (T) where T: Mark { return keep(value); }",
    "function converted(flag: Bool) returns (Word) { return forward(flag); }",
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(7), f(flag)); }",
    "function failed(flag: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = forward(flag); let absent: Word; return absent; }"
  ]}] }

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let mut qualified := 0
  let mut coerced := 0
  for named in prepared.base.functions do
    let available ← SourceCompilerFeatureSupport.get "caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram named.signature.key named.specialized.assumptions)
    for item in named.specialized.function.typedBody.nodes do
      match item with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          if !instantiation.predicates.isEmpty && instantiation.predicates.all (fun predicate => (TypedTraitResolution.predicateVariables predicate).isEmpty) then
            let actual ← SourceCompilerFeatureSupport.get "direct ordered evidence"
              (SourceCompilationPlan.exactDirectCallRuntimeEvidence named.specialized node available instantiation)
            discard <| SourceCompilerFeatureSupport.get "authenticate ordered evidence"
              (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence prepared.base.sourceProgram.signatures named.signature.key instantiation.predicates actual)
            qualified := qualified + 1
            if !node.coercions.isEmpty then coerced := coerced + 1
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (qualified > 0 && coerced > 0) "qualified coercion-call receipt coverage disappeared"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "authenticated call checker" (checkProgram workspace)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  audit converted
  for (flag, expected) in [(true, 42), (false, 8)] do
    converted.checkResume [.bool flag] (SourceCompilerFeatureSupport.scalar expected) 9
  let localEntry ← SourceCompilerFeatureSupport.compileNamed program "local"
  localEntry.checkResume [.bool true] (.product (SourceCompilerFeatureSupport.scalar 7) (.bool true)) 17
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke [.bool true]
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "coercion effects did not reach expected later failure")
  let snapshot ← SourceCompilerFeatureSupport.get "evidence failure snapshot" (← session.snapshot 2048)
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "evidence failure suspend"
      (← baseline.initial.run baseline.key [.bool true] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "evidence failure resume snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "coercion dictionary call changed effects, failure or resume"
    | _ => throw (IO.userError "evidence resume changed outcome")
  IO.println "authenticated call evidence: reached validity, exact middle layout, local rebinding, coercion effects and resume GREEN"

end Tests.SourceCoreCallableAuthenticatedCallEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAuthenticatedNamedCalls
/-! Authenticated children retain the actual special hook, ordered arguments,
and nonempty caller evidence. The final consumers build their Tree from actual
contextual acceptance and close runtime children through catalog mutual meaning.
Callee profiles still use the existing ordinary grammar; raw source typing,
constructor formation, reached headers, and real runtime Entry remain explicit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableAuthenticatedNamedCalls
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableCoercionExpressionCertificates
open CallableAuthenticatedNamedCallCertificates

section Accepted
variable {checked : Checked} {base : Base checked}
  {ancestry : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {compilerProgram : CheckedProgram}
  {headers : Inventory ancestry values ambient.definitions (Program.ofChecked compilerProgram)} {locations : Locations} {capturePrefix : Nat}
  {bodyCompilation : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header ancestry values ambient.definitions (Program.ofChecked compilerProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : ((Program.ofChecked compilerProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (bodyCompilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (bodyCompilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)


variable {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {reasonAt : ExpressionId → Word} {readFuel fuel : Nat}
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable {caller : SourceSpecialization.SpecializedFunction}
  {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
  {localCatalog : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode} {output : Lowered}
  (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
  (nonempty : caller.assumptions ≠ [])
  (coverage : Coverage headers compilerProgram caller compilation source scope reasonAt)
  (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
  (sourceSignatures : context.signatures = (Program.ofChecked compilerProgram).signatures)
  (nativeSignatures : context.signatures = values.checked.signatures)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
  (ordinary : CompatibleExpressionBuiltins.Ordinary source localCatalog compilation.owner)
  (notInitializer : ∀ id node callee arguments instantiation, source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → Syntax source id →
    localCatalog.bindings.find? (fun binding => decide (binding.caller = compilation.owner ∧ binding.initializer = id)) = none)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (projectPolicy : representation.expressions.projectType = SourceCoreCompatibleDataExpressions.projectType values.checked)
  (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
  (typed : ExpressionHasType source context id node.type)
  (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures localCatalog parents assignments
    diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok output)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  callerSelected nonempty coverage sourceTypes sourceSignatures nativeSignatures declarations constructorValid ordinary notInitializer
  readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted in
/-- The actual contextual hook supplies every child certificate. No raw or
body runtime law is a premise of this source-to-native consumer. -/
theorem accepted_preserves [FunctionCalls.FaultTokens faults] :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (fun current identifier code => current = scope ∧ identifier = id ∧ code = output)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have tree := tree_of_contextual callerSelected nonempty coverage sourceTypes sourceUnique sourceSignatures nativeSignatures
    declarations constructorValid ordinary notInitializer readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted
  intro current identifier code ⟨rfl, rfl, rfl⟩ root
  exact CallableAuthenticatedNamedCallMeaning.preserves functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing tree

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing
  callerSelected nonempty coverage sourceTypes sourceSignatures nativeSignatures declarations constructorValid ordinary notInitializer
  readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted in
/-- Reflection measures the actual completion; an independent source run and
preservation are not inputs. The source context's residual flag is untouched. -/
theorem accepted_reflects [FunctionCalls.FaultTokens faults] :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (Program.ofChecked compilerProgram) context evidence source
      (fun current identifier code => current = scope ∧ identifier = id ∧ code = output)
      faults (protectedEntry headers locations capturePrefix compilation.administrativePrefix) := by
  have tree := tree_of_contextual callerSelected nonempty coverage sourceTypes sourceUnique sourceSignatures nativeSignatures
    declarations constructorValid ordinary notInitializer readPolicy lowerPolicy leafPolicy projectPolicy syntaxTree found typed accepted
  intro current identifier code ⟨rfl, rfl, rfl⟩ root
  exact CallableAuthenticatedNamedCallMeaning.reflects functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing tree
end Accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function first(value: Word) returns (Word) { let firstEffect: Word = 41; return value; }",
    "function second(value: Word) returns (Word) { let secondEffect: Word = 43; return value; }",
    "function join(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 47; return right; }",
    "function fail() returns (Word) { let beforeFault: Word = 53; let missing: Word; return missing; }",
    "function failBody(left: Word, right: Word) returns (Word) { let bodyEffect: Word = 59; let bodyGap: Word; return bodyGap; }",
    "function zero() returns (Word) { let zeroEffect: Word = 61; return 11; }",
    "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
    "function walk(value: Word, depth: Word) returns (Word) { if (depth == 0) { return value; } return walk(value, depth - 1); }",
    "function nested(value: Word) returns (Word) where Word: Marker { return join(first(value), second(first(value))); }",
    "function repeated(value: Word) returns (Word) where Word: Marker { return join(first(value), first(value)); }",
    "function firstFault() returns (Word) where Word: Marker { return join(fail(), second(9)); }",
    "function laterFault() returns (Word) where Word: Marker { return join(first(7), fail()); }",
    "function bodyFault() returns (Word) where Word: Marker { return failBody(first(7), second(9)); }",
    "function empty() returns (Word) where Word: Marker { return zero(); }",
    "function generic(value: Word) returns (Word) where Word: Marker { return choose(first(value), false); }",
    "function recursive() returns (Word) where Word: Marker { return walk(first(7), 2); }"
  ]}] }
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _
private def scalar := SourceCompilerFeatureSupport.scalar
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

/-- Each authenticated site is inspected in its real nonempty caller. The
actual contextual compiler is compared with its emitted ordinary call code;
only reached callees are required to be ordinary. -/
private def inspect (entry : SourceCompilerFeatureSupport.Entry) (expectedCalls : Nat) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let named ← match base.functions.find? (·.signature.key == entry.key) with
    | some named => pure named | none => throw (IO.userError "authenticated caller missing")
  let caller := named.specialized
  require (!caller.assumptions.isEmpty) "authenticated fixture lost its nonempty caller"
  let representation := (SourceCoreCallableIndexedPrograms.markedRepresentation indexed.ancestry indexed.fuel indexed.layouts).atContext named.signature.key []
  let compilation : SourceCoreFunctions.Context := {
    plan := base.plan, owner := named.signature.key, globals := base.globals,
    administrativePrefix := 1, solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
  let source := caller.function.typedBody
  let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
  let diagnostics ← match base.diagnostics with
    | some value => pure value.program | none => throw (IO.userError "authenticated diagnostics missing")
  let diagnostics := match base.callableContext with
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable} | none => diagnostics
  let own ← match diagnostics.base.find? named.signature.key with
    | some own => pure own | none => throw (IO.userError "authenticated own diagnostics missing")
  let reasonAt := diagnostics.reasonAt named.signature.key
  let lower := SourceCoreGeneralFunctions.lowerContextualExpression base.sourceProgram representation base.sourceProgram.signatures
    base.locals base.contexts own.assignments diagnostics compilation base.callableContext none none
  let callables := SourceCoreGeneralFunctions.callablePolicy base.callableContext []
  let available ← get "authenticated caller evidence"
    (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram caller.key caller.assumptions)
  let mut count := 0
  for item in source.nodes do
    if let .expression node := item then
      if let .call _ arguments (.declaration instantiation) := node.form then
        require (node.coercions.isEmpty && node.requirements.isEmpty) "authenticated empty path/requirements changed"
        let output ← get "authenticated actual contextual acceptance" (lower 150 source scope node.id reasonAt)
        let selectedTarget ← get "authenticated exact target" (SourceCompilationPlan.exactInstantiationKey base.plan instantiation)
        let key ← get "authenticated actual edge" (SourceCompilationPlan.exactCallKey base.plan compilation.owner node.id selectedTarget)
        let selected ← get "authenticated full selected specialization" (SourceCompilationPlan.exactSpecialization base.plan key)
        let dictionary ← get "authenticated actual dictionary"
          (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
        discard <| get "authenticated dictionary check"
          (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence base.sourceProgram.signatures key selected.assumptions dictionary)
        let (signature, slot) ← match base.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
          | [row] => pure row | _ => throw (IO.userError "authenticated reached global not singleton")
        let reached ← match base.functions.filter (·.signature.key == key) with
          | [row] => pure row | _ => throw (IO.userError "authenticated reached Header not singleton")
        require (reached.specialized == selected && reached.signature == signature && selected.assumptions.isEmpty && dictionary.isEmpty &&
          reprStr instantiation == reprStr (CallableNamedCanonicalOrder.retainedInstantiation selected))
          "authenticated full reached record/retained metadata/ordinary dictionary changed"
        let loweredArgs ← get "authenticated ordered children" (arguments.mapM (fun id => lower 149 source scope id reasonAt))
        let packed := SourceCoreCalls.packArguments loweredArgs
        let expected := SourceCoreCalls.call signature (scope.length + compilation.administrativePrefix + slot)
          packed.expression compilation.internalReason
        require (loweredArgs.map (·.type) == reached.inputs.map Prod.snd && packed.type == signature.parameterType &&
          output.type == signature.resultType && output.expression == expected)
          "authenticated ordered argument code/native vector/call slot changed"
        let hooked ← get "authenticated actual evidence special hook"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram representation.expressions.projectType caller compilation
            lower 149 source scope node.id reasonAt callables)
        require (hooked == some output) "actual evidence hook did not select the contextual code"
        match SourceCoreFunctions.selectedSignature representation.expressions compilation source node instantiation false with
        | .error (.callPreparation (.unresolvedAssumptions owner assumptions)) =>
          require (owner == compilation.owner && assumptions == caller.assumptions) "ordinary guard rejected a different caller"
        | _ => throw (IO.userError "ordinary none branch incorrectly accepted nonempty caller")
        let nativeContext := scope.map (fun row => OptionalCell.referenceType row.2) ++ .unit ::
          (base.globals.map SourceCoreCalls.Signature.referenceType ++ [.cell indexed.ancestry.layout.frame.type])
        require (Core.infer? nativeContext output.expression indexed.layouts.definitions == some (LanguageResult.resultType output.type))
          "authenticated emitted native code failed independent checking"
        count := count + 1
  require (count == expectedCalls) s!"authenticated site count changed: {count}/{expectedCalls}"

private def cells (state : SourceTypedRuntime.RuntimeState) (expected : List (Option Nat)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) ==
    reprStr (expected.map fun value => (TypeSystem.Ty.word, value.map word)))
    s!"authenticated full source heap changed: {reprStr state.heap}"

private def gap (entry : SourceCompilerFeatureSupport.Entry) (name : String) : IO Resolved.LocalId := do
  match (entry.cached.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "authenticated fault binder not unique")

private def publicResume (entry : SourceCompilerFeatureSupport.Entry) (arguments : List SourceCoreExecution.Value) : IO Unit := do
  let artifact ← entry.execution.open
  let initial ← SourceCompilerFeatureSupport.boot artifact
  let finished ← get "authenticated complete public call" (← initial.run entry.key arguments SourceCompilerFeatureSupport.executionOptions)
  for budget in [0, 41, 137] do
    let started ← get "authenticated suspended public call"
      (← initial.run entry.key arguments {SourceCompilerFeatureSupport.executionOptions with executionFuel := budget})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 500000 2048 | outcome => pure outcome
    match finished, resumed with
    | .succeeded expected, .succeeded actual =>
      let before ← get "authenticated complete public snapshot" (← expected.session.snapshot 2048)
      let after ← get "authenticated resumed public snapshot" (← actual.session.snapshot 2048)
      require (expected.value == actual.value && reprStr before.cells == reprStr after.cells)
        "authenticated success resume changed value/full native store"
    | .failed expected beforeSession, .failed actual afterSession =>
      let before ← get "authenticated complete public fault snapshot" (← beforeSession.snapshot 2048)
      let after ← get "authenticated resumed public fault snapshot" (← afterSession.snapshot 2048)
      require (expected == actual && reprStr before.cells == reprStr after.cells)
        "authenticated failure resume changed reason/full native store"
    | _, _ => throw (IO.userError "authenticated resume changed public outcome")

def run : IO Unit := do
  let program ← get "authenticated fixture check" (checkProgram workspace 1024)
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  let repeated ← SourceCompilerFeatureSupport.compileNamed program "repeated"
  let firstFault ← SourceCompilerFeatureSupport.compileNamed program "firstFault"
  let laterFault ← SourceCompilerFeatureSupport.compileNamed program "laterFault"
  let bodyFault ← SourceCompilerFeatureSupport.compileNamed program "bodyFault"
  let empty ← SourceCompilerFeatureSupport.compileNamed program "empty"
  let generic ← SourceCompilerFeatureSupport.compileNamed program "generic"
  let recursive ← SourceCompilerFeatureSupport.compileNamed program "recursive"
  for (entry, count) in [(nested, 4), (repeated, 3), (firstFault, 3), (laterFault, 3), (bodyFault, 3), (empty, 1), (generic, 2), (recursive, 2)] do
    inspect entry count
  let firstGap ← gap firstFault "missing"
  let laterGap ← gap laterFault "missing"
  let bodyGap ← gap bodyFault "bodyGap"
  let successes : List (SourceCompilerFeatureSupport.Entry × List SourceCoreExecution.Value × Nat × List (Option Nat)) := [
    (nested, [scalar 7], 7, [some 7, some 7, some 41, some 7, some 41, some 7, some 43, some 7, some 7, some 47]),
    (repeated, [scalar 7], 7, [some 7, some 7, some 41, some 7, some 41, some 7, some 7, some 47]),
    (empty, [], 11, [some 61]),
    (recursive, [], 7, [some 7, some 41, some 7, some 2, some 7, some 1, some 7, some 0])]
  let failures : List (SourceCompilerFeatureSupport.Entry × Resolved.LocalId × List (Option Nat)) := [
    (firstFault, firstGap, [some 53, none]),
    (laterFault, laterGap, [some 7, some 41, some 53, none]),
    (bodyFault, bodyGap, [some 7, some 41, some 9, some 43, some 7, some 9, some 59, none])]
  for budget in [0, 41, 137, 500000] do
    for (entry, arguments, expected, heap) in successes do
      let started ← entry.audit arguments budget
      let finished ← get "authenticated source observation resume" (started.resume 500000)
      match finished.observation with
      | .done value state => require (reprStr value == reprStr (word expected)) "authenticated value changed"; cells state heap
      | other => throw (IO.userError s!"authenticated expected success: {reprStr other}")
    for (entry, binder, heap) in failures do
      let started ← entry.audit [] budget
      let finished ← get "authenticated fault source observation resume" (started.resume 500000)
      match finished.observation with
      | .fault (.uninitializedLocal actual) state => require (actual == binder) "authenticated first fault changed"; cells state heap
      | other => throw (IO.userError s!"authenticated expected fault: {reprStr other}")
    let genericRun ← generic.audit [scalar 7] budget
    let genericRun ← get "authenticated generic resume" (genericRun.resume 500000)
    match genericRun.observation with
    | .done value state =>
      require (reprStr value == reprStr (word 7) &&
        reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr
          [(TypeSystem.Ty.word, some (word 7)), (.word, some (word 7)), (.word, some (word 41)),
           (.word, some (word 7)), (.bool, some (SourceTypedRuntime.Value.bool false))])
        "authenticated generic full heap/raw parameter order changed"
    | other => throw (IO.userError s!"authenticated generic failed: {reprStr other}")
  for (entry, arguments, _, _) in successes do publicResume entry arguments
  for (entry, _, _) in failures do publicResume entry []
  publicResume generic [scalar 7]
  IO.println "authenticated named children: actual nonempty caller hook/full records/ordered nested args/first faults/full heaps/resume GREEN"

end Tests.SourceCoreCallableAuthenticatedNamedCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCallEvidence
/-! Actual ordered materialization, including repeated IDs/goals, is related
to independent source evidence. Rejected selection and forged implementation
fixtures distinguish successful metadata checks from semantic validity. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCallEvidence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableNamedMetadata (evidence environment)
open CallableEvidenceEnvironment CallableCallEvidence

/-- Resolve and materialize actual dictionaries, then identify any independently
produced dictionary. No source production or caller-validity premise is used
to construct the first conjunct. -/
theorem actual_call_dictionary {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {occurrence : ExpressionId} {available result : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {context : SourceSemantics.Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (retained : SolvedRequirementsValid context caller.function.solvedRequirements)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    (accepted : SourceCompilationPlan.materializeCallEvidence caller occurrence available ids predicates = .ok result) :
    Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates (environment result) ∧
      ∀ semantic, Dynamic.RequirementsProduceEnvironment context (environment available) ids predicates semantic →
        semantic = environment result :=
  ⟨produces_of_resolved signatures ledger retained resolved accepted, fun _ produced => agrees ledger accepted produced⟩

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntWordRule.head
private def raw : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intWord) []
private def alternate : TypedTraitResolution.Evidence := .byImpl goal (.builtin .intInteger) []
private def concrete : SolvedRequirement := ⟨⟨0⟩, goal, .implementation raw⟩
private def assumed : SolvedRequirement := ⟨⟨1⟩, goal, .assumption goal⟩
private def unrelated : SolvedRequirement := ⟨⟨2⟩, goal, .implementation raw⟩
private def rows : List SolvedRequirement := [concrete, assumed, unrelated, unrelated]
private def context : SourceSemantics.Context := {
  signatures, locals := [], assumptions := [goal], solvedRequirements := rows }
private def callerWith (seed : SourceSpecialization.SpecializedFunction) (ledger : List SolvedRequirement) :=
  { seed with function := { seed.function with solvedRequirements := ledger } }

private theorem raw_valid : EvidenceValid [] signatures.resolutionRules goal (evidence raw) := by
  simp only [raw, CallableNamedMetadata.evidence, List.map_nil]
  apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
    (by simp [signatures, ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (TraitResolutionSoundness.matchImplHead?_sound (by decide)) .nil

private theorem rows_valid : SolvedRequirementsValid context rows := by
  intro row member
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .intro (.intro (.implementation (CallableNamedMetadata.evidence_represents raw))
      (raw_valid.weakenAssumptions (by simp)))
  · exact .intro (.intro (.assumption goal) (.assumption (by simp [context, assumed])))
  all_goals exact .intro (.intro (.implementation (CallableNamedMetadata.evidence_represents raw))
    (raw_valid.weakenAssumptions (by simp)))

private theorem available_valid : (environment [raw, alternate]).Valid signatures.resolutionRules := by
  intro selected output found
  cases found with
  | head => exact raw_valid
  | tail different found =>
    cases found with
    | head => exact (different rfl).elim
    | tail _ found => cases found

/-- First match preserves the first entire tree despite equal later goals. The
requested spine repeats an ID; unrelated duplicate ledger IDs are untouched. -/
theorem ordered_mixed (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed rows) occurrence [raw, alternate]
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] = .ok [raw, raw, raw] ∧
    Dynamic.RequirementsProduceEnvironment context (environment [raw, alternate])
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] (environment [raw, raw, raw]) := by
  have accepted : SourceCompilationPlan.materializeCallEvidence (callerWith seed rows) occurrence [raw, alternate]
      [⟨1⟩, ⟨0⟩, ⟨1⟩] [goal, goal, goal] = .ok [raw, raw, raw] := rfl
  exact ⟨accepted, produces rfl rows_valid available_valid accepted⟩

theorem actual_duplicate_rejected (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [concrete, concrete]) occurrence []
      [⟨0⟩] [goal] = .error (.duplicateSolvedRequirements seed.key occurrence ⟨0⟩ 2) := rfl

theorem absent_assumption_rejected (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [assumed]) occurrence [] [⟨1⟩] [goal] =
      .error (.missingRuntimeAssumptionEvidence seed.key occurrence ⟨1⟩ goal) := rfl

private def forged (owner : Resolved.DeclarationId) : TypedTraitResolution.Evidence := .byImpl goal (.declaration owner) []
private theorem forged_invalid (owner : Resolved.DeclarationId) :
    ¬ EvidenceValid [] signatures.resolutionRules goal (evidence (forged owner)) := by
  simp only [forged, CallableNamedMetadata.evidence, List.map_nil]
  intro valid
  cases valid with
  | implementation member identity _ _ =>
    simp only [signatures, ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules,
      List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cases identity

/-- Materialization checks goals and exact IDs, but deliberately does not
rerun implementation selection. This accepted forged tree has no independent
closed validity and therefore cannot supply a source production judgment. -/
theorem success_not_validity (seed : SourceSpecialization.SpecializedFunction) (occurrence : ExpressionId) :
    let entry : SolvedRequirement := ⟨⟨0⟩, goal, .implementation (forged seed.declaration)⟩
    SourceCompilationPlan.materializeCallEvidence (callerWith seed [entry]) occurrence [] [⟨0⟩] [goal] =
      .ok [forged seed.declaration] ∧
    ¬ Dynamic.RequirementsProduceEnvironment context [] [⟨0⟩] [goal] (environment [forged seed.declaration]) := by
  refine ⟨rfl, ?_⟩
  intro produced
  cases produced with
  | cons head _ => exact forged_invalid seed.declaration head.closed_valid

/-- No reordering or erasure of recursive premises occurs when closed trees
are passed through the materializer's implementation branch. -/
theorem deep_closed (caller : Dynamic.EvidenceEnvironment) (left right : TypedTraitResolution.Evidence) :
    Dynamic.EvidenceCloses caller
      (evidence (.byImpl goal (.builtin .intWord) [left, right]))
      (.implementation goal (.builtin .intWord) [evidence left, evidence right]) := by
  simpa only [CallableNamedMetadata.evidence, List.map_cons, List.map_nil] using
    closes_self caller (.byImpl goal (.builtin .intWord) [left, right])

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "enum Box<T> { Wrap(T) }",
    "impl<T> Mark<Box<T>> where T: Mark {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function forward<T>(value: T) returns (T) where T: Mark { return keep(value); }",
    "function concrete(seed: Word) returns (Word) { let value = Box.Wrap(Box.Wrap(seed)); forward(value); return seed; }",
    "function failed(seed: Word) returns (Word) { forward(seed); let absent: Word; return absent; }"
  ]}] }

private def depth : TypedTraitResolution.Evidence → Nat
  | .byImpl _ _ premises => 1 + (premises.map depth).foldl Nat.max 0

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let mut assumptions := 0
  let mut concrete := 0
  let mut deepest := 0
  for named in prepared.base.functions do
    let available ← SourceCompilerFeatureSupport.get "caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram named.signature.key named.specialized.assumptions)
    for node in named.specialized.function.typedBody.nodes do
      match node with
      | .expression node =>
        match node.form with
        | .call _ _ (.declaration instantiation) =>
          if node.coercions.isEmpty then
            let result ← SourceCompilerFeatureSupport.get "actual call evidence"
              (SourceCompilationPlan.materializeCallEvidence named.specialized node.id available node.requirements instantiation.predicates)
            SourceCompilerFeatureSupport.require (decide (result.map SourceCompilationPlan.runtimeEvidenceGoal = instantiation.predicates))
              "call evidence order or multiplicity changed"
            for item in result do deepest := max deepest (depth item)
            for requirement in node.requirements do
              match named.specialized.function.solvedRequirements.find? (fun row => row.id == requirement) with
              | some {evidence := .assumption _, ..} => assumptions := assumptions + 1
              | some {evidence := .implementation _, ..} => concrete := concrete + 1
              | none => throw (IO.userError "missing actual call requirement")
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (assumptions > 0 && concrete > 0 && deepest ≥ 3)
    "evidence fixture lost mixed/deep actual compiler coverage"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "call evidence checker" (checkProgram workspace)
  let entry ← SourceCompilerFeatureSupport.compileNamed program "concrete"
  audit entry
  entry.checkResume [SourceCompilerFeatureSupport.scalar 9] (SourceCompilerFeatureSupport.scalar 9) 11
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke [SourceCompilerFeatureSupport.scalar 7]
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "qualified call did not reach expected later fault")
  let snapshot ← SourceCompilerFeatureSupport.get "evidence fault snapshot" (← session.snapshot 2048)
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "evidence fault suspend"
      (← baseline.initial.run baseline.key [SourceCompilerFeatureSupport.scalar 7]
        {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "evidence fault resume snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "qualified evidence call changed failure prefix or resume"
    | _ => throw (IO.userError "qualified evidence resume changed outcome")
  IO.println "call evidence: exact ordered materialization, recursive proofs, first-match duplicates and qualified resume GREEN"

end Tests.SourceCoreCallableCallEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableCallEvidenceCertificates
/-! Accepted outer evidence lowering supplies full selected metadata and the
independent ordered dictionary. None delegates ordinary lowering and does not
certify a target. Actual closed and contextual-local callers share the receipt. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates.Selection.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableCallEvidenceCertificates
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableCallEvidenceCertificates
open CallableNamedMetadata (environment)

/-- The final consumer assumes one actual compiler action, rather than its
resolver, materializer, authenticator or target-predicate subresults. -/
theorem direct_from_outer {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered} {context : SourceSemantics.Context}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered))
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    ∃ receipt : Selection program caller compilation node instantiation false,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      (∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
        calleeNode.form = .reference name (.declaration instantiation) ∧ calleeNode.type = instantiation.type) ∧
      arguments.length = receipt.specialized.function.typedBody.inputs.length ∧
      Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
        instantiation.predicates (environment receipt.actual) ∧
      ∀ semantic, Dynamic.DirectCallProducesEvidence context (environment receipt.available) node.requirements node.coercions
        instantiation.predicates semantic → semantic = environment receipt.actual := by
  obtain ⟨receipt, validated, arity⟩ := direct_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, callee_metadata validated, arity, receipt.direct_produces signatures ledger assumptions,
    fun _ produced => receipt.direct_agrees ledger (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced⟩

theorem reference_from_outer {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {name : String} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered} {context : SourceSemantics.Context}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType caller compilation child fuel source scope id reasonAt callables = .ok (some lowered))
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    ∃ receipt : Selection program caller compilation node instantiation true,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      (∃ ids, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids ∧
        Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates (environment receipt.actual)) ∧
      ∀ ids semantic, Dynamic.OrdinaryRequirementLayout node.requirements node.coercions ids →
        Dynamic.RequirementsProduceEnvironment context (environment receipt.available) ids instantiation.predicates semantic →
          semantic = environment receipt.actual := by
  obtain ⟨receipt⟩ := reference_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, receipt.reference_produces signatures ledger assumptions,
    fun _ _ layout produced => receipt.reference_agrees ledger layout produced⟩

/-- Authenticated local preparation supplies the actual rewritten caller. The
same outer declaration branch determines the returned dictionary inside it. -/
theorem prepared_local_direct {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {parent : SourceCoreLocalEvidence.Prepared} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreEvidence.Lowered}
    (found : parent.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program projectType parent.caller compilation child fuel parent.source scope id reasonAt callables = .ok (some lowered)) :
    ∃ receipt : Selection program parent.caller compilation node instantiation false,
      CallableNamedMetadata.Matches receipt.specialized instantiation ∧
      receipt.specialized.assumptions = instantiation.predicates := by
  obtain ⟨receipt, _, _⟩ := direct_of_accepted found form accepted
  exact ⟨receipt, receipt.metadata, receipt.metadata.predicates⟩

private def emptyPlan : SourceCompilationPlan.Plan := ⟨[], [], [], []⟩

/-- Even a missing declaration target is compatible with none: the evidence
pass has delegated, and the ordinary traversal must still check this call. -/
theorem bypass_is_not_selection {program : CheckedProgram} {projectType : SourceCoreEvidence.Projector}
    {caller : Specialized} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreEvidence.Scope} {id callee : ExpressionId}
    {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (requirements : node.requirements = []) (coercions : node.coercions = []) (assumptions : caller.assumptions = []) :
    SourceCoreEvidence.lowerWithProjector program projectType caller {compilation with plan := emptyPlan}
      child fuel source scope id reasonAt callables = .ok none ∧
    SourceCompilationPlan.exactInstantiationKey emptyPlan instantiation =
      .error (.missingInstantiationTarget instantiation.declaration instantiation.type) :=
  ⟨direct_bypass found form requirements coercions assumptions, rfl⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function value() returns (Word) where Word: Mark { return 4; }",
    "function empty() returns (Word) { return 5; }",
    "function direct() returns (Word) { return value(); }",
    "function inherited() returns (Word) where Word: Mark { return empty(); }",
    "function referenced() returns (Word) { let f: function() returns (Word) = value; return f(); }",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function local(flag: Bool) returns (Word, Word) { let f = lam(item) { keep(item); return value(); }; return (f(7), f(flag)); }",
    "function failed() returns (Word) { let table: mapping(Word => Word); table[0] = value(); let absent: Word; return absent; }"
  ]}] }

private def rejectChild : SourceCoreEvidence.Child := fun _ _ _ id _ => .error (.missingExpression id)

/-- Audit only nullary named calls and retained declaration reference edges.
These use the real outer compiler without requiring any child callback. -/
private def auditSource (entry : SourceCompilerFeatureSupport.Entry) (caller : Specialized)
    (source : TypedSource) : IO (Nat × Nat × Nat) := do
  let base := entry.cached.indexed.base
  let context : SourceCoreFunctions.Context := {
    plan := base.plan
    owner := caller.key
    globals := base.globals
    administrativePrefix := 1
    solvedRequirements := caller.function.solvedRequirements
    internalReason := Word.ofNatModulo 0 }
  let mut direct := 0
  let mut reference := 0
  let mut inherited := 0
  for item in source.nodes do
    match item with
    | .expression node =>
      let relevant := match node.form with
        | .call _ [] (.declaration _) => true
        | .reference _ (.declaration _) => base.plan.referenceEdges.any (fun edge => decide (edge.caller = caller.key ∧ edge.occurrence = node.id))
        | _ => false
      if relevant then
        let output ← SourceCompilerFeatureSupport.get "actual outer evidence lowering"
          (SourceCoreEvidence.lowerWithProjector base.sourceProgram SourceCoreFunctionTypes.projectType caller context rejectChild
            100 source [] node.id (fun _ => Word.ofNatModulo 0))
        match output with
        | none => pure ()
        | some _ =>
          match node.form with
          | .call _ _ (.declaration instantiation) =>
            direct := direct + 1
            if instantiation.predicates.isEmpty && !caller.assumptions.isEmpty then inherited := inherited + 1
          | .reference _ (.declaration _) => reference := reference + 1
          | _ => throw (IO.userError "outer evidence audit changed branch")
    | _ => pure ()
  pure (direct, reference, inherited)

private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO (Nat × Nat × Nat) := do
  let mut total := (0, 0, 0)
  for named in entry.cached.indexed.base.functions do
    let counts ← auditSource entry named.specialized named.specialized.function.typedBody
    total := (total.1 + counts.1, total.2.1 + counts.2.1, total.2.2 + counts.2.2)
  pure total

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "outer call evidence checker" (checkProgram workspace)
  let direct ← SourceCompilerFeatureSupport.compileNamed program "direct"
  let directCounts ← audit direct
  SourceCompilerFeatureSupport.require (directCounts.1 > 0) "qualified direct branch disappeared"
  direct.checkResume [] (SourceCompilerFeatureSupport.scalar 4) 11
  let inherited ← SourceCompilerFeatureSupport.compileNamed program "inherited"
  let inheritedCounts ← audit inherited
  SourceCompilerFeatureSupport.require (inheritedCounts.2.2 > 0) "caller-only authentication did not run"
  inherited.checkResume [] (SourceCompilerFeatureSupport.scalar 5) 3
  let referenced ← SourceCompilerFeatureSupport.compileNamed program "referenced"
  let referenceCounts ← audit referenced
  SourceCompilerFeatureSupport.require (referenceCounts.2.1 > 0) "qualified reference branch disappeared"
  referenced.checkResume [] (SourceCompilerFeatureSupport.scalar 4) 19
  let localEntry ← SourceCompilerFeatureSupport.compileNamed program "local"
  let mut contextual := 0
  for binding in localEntry.cached.indexed.base.locals.bindings do
    for candidate in binding.instances do
      let parent ← SourceCompilerFeatureSupport.get "actual local preparation"
        (SourceCoreLocalEvidence.prepare program localEntry.cached.indexed.base.plan candidate)
      let counts ← auditSource localEntry parent.caller parent.source
      contextual := contextual + counts.1
  SourceCompilerFeatureSupport.require (contextual ≥ 2) "contextual lambda evidence branches disappeared"
  localEntry.checkResume [.bool true] (.product (SourceCompilerFeatureSupport.scalar 4) (SourceCompilerFeatureSupport.scalar 4)) 23
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  let baseline ← failed.invoke []
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "outer call fixture did not reach later failure")
  let snapshot ← SourceCompilerFeatureSupport.get "outer evidence failure snapshot" (← session.snapshot 2048)
  for spent in [0, 17, 53] do
    let started ← SourceCompilerFeatureSupport.get "outer evidence suspension"
      (← baseline.initial.run baseline.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "outer evidence resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "outer selected call changed failure or store prefix on resume"
    | _ => throw (IO.userError "outer evidence resume changed outcome")
  IO.println "outer call evidence certificates: full selected metadata, ordered dictionaries, caller-only and contextual authentication, reference and failure/resume GREEN"

end Tests.SourceCoreCallableCallEvidenceCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableContextFrameCodec
set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrameCodec
open Solcore Solcore.Frontend
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n

def run : IO Unit := do
  let layout : SourceCoreCallableContextFrames.Layout := ⟨⟨3⟩⟩
  let other : SourceCoreCallableContextFrames.Layout := ⟨⟨4⟩⟩
  let frames : List SourceCoreCallableContextFrames.Frame := [.empty, .named (w 1), .lambda (w 2) .empty,
    .view (w 7) (w 2) (.named (w 1)),
    .lambda (w 8) (.view (w 7) (w 2) (.lambda (w 2) (.named (w 1))))]
  for frame in frames do
    assertTrue (SourceCoreCallableContextFrameCodec.decode layout (SourceCoreCallableContextFrames.encode layout frame) == some frame)
      "callable frame did not retain its exact recursive ancestry"
    assertTrue ((SourceCoreCallableContextFrameCodec.decode other (SourceCoreCallableContextFrames.encode layout frame)).isNone)
      "foreign nominal frame layout was accepted"
  let malformed : List Core.Value := [.unit, .word (w 1),
    .constructed layout.empty (.word (w 1)), .constructed layout.named .unit,
    .constructed layout.lambda (.pair (.word (w 2)) (.bool true)),
    .constructed layout.view (.pair (.word (w 7)) (.pair .unit (SourceCoreCallableContextFrames.encode layout .empty))),
    .constructed ⟨layout.dataType, 4⟩ .unit,
    .constructed layout.lambda (.pair (.word (w 2)) (SourceCoreCallableContextFrames.encode other .empty))]
  assertTrue (malformed.all fun value => (SourceCoreCallableContextFrameCodec.decode layout value).isNone)
    "malformed callable frame was accepted"
  IO.println "exact recursive callable frame codec GREEN"

end Tests.SourceCoreCallableContextFrameCodec
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableContextFrameProofs
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Finite frame-helper laws with real lexical selectors, arbitrary closure
captures, effectful frame preparation, body allocation, nested restoration,
language failures and suspension before restoration. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrameProofs
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableContextFrames
open Solcore.SourceSemantics.CoreLowering.CallableContextFrames
open Solcore.SourceSemantics.CoreLowering.DataEquality (Selects)

private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private def cyclic : Value := .closure .unit .unit (.var 0) [.cellRef (.function .unit .unit) 0]
private def before : Store := [cyclic, encode layout .empty, .word (w 99)]
private def environment : Environment := [.pair .unit (.cellRef layout.type 1), .cellRef .word 2]
private def context : Context := [.product .unit (.cell layout.type), .cell .word]
private def reference : Expr := .second (.var 0)
private def next : Expr :=
  .letE (.storeCell reference (named layout (w 13))) (named layout (w 3))
private def body (failure : Bool) : Expr :=
  .letE (.newCell .word (.word (w 42)))
    (.letE (.storeCell (.var 2) (.word (w 7)))
      (.letE (.storeCell (.second (.var 2)) (named layout (w 88)))
        (if failure then LanguageResult.failure .word (.word (w 23))
         else LanguageResult.success (.loadCell (.var 2)))))
private def expected (failure : Bool) : Value :=
  if failure then .inLeft .word (.word (w 23)) else .inRight .word (.word (w 42))
private def after : Store := [cyclic, encode layout .empty, .word (w 7), .word (w 42)]

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private theorem selected : Selects environment reference (.cellRef layout.type 1) := .second (.var rfl)

example : RuntimeStoreHasTypes [.function .unit .unit, layout.type, .word] before definitions := by
  constructor
  · rfl
  · intro index type found
    cases index with
    | zero => cases found; exact ⟨cyclic, rfl, .closure (.cons (.cellRef rfl) .nil) (.var rfl)⟩
    | succ index =>
      cases index with
      | zero => cases found; exact ⟨_, rfl, encode_runtime_typed _ ⟨rfl⟩ .empty⟩
      | succ index =>
        cases index with
        | zero => cases found; exact ⟨_, rfl, .word⟩
        | succ index => cases found

/-- An arbitrary resulting closure really captures the administrative values.
No equality with an unshifted body evaluation is asserted. -/
example (outer : Environment) (saved : Value) (store : Store)
    (readable : store.read? 0 = some saved) :
    Evaluates (.cellRef .unit 0 :: outer) store
      (withFrame (.var 0) .unit (.lambda .unit .unit (.var 0)))
      (.closure .unit .unit (.var 0) (.unit :: saved :: .cellRef .unit 0 :: outer))
      ((store.set 0 .unit).set 0 saved) :=
  withFrame_evaluates (nextStore := store) (installedValue := .unit) (.var rfl) readable
    (by simpa [Expr.weakenAt] using (Evaluates.unit (environment := saved :: .cellRef .unit 0 :: outer) (store := store)))
    (by simpa [Expr.weakenAt] using (Evaluates.lambda (environment := .unit :: saved :: .cellRef .unit 0 :: outer)
      (store := store.set 0 .unit) (parameterType := .unit) (resultType := .unit) (body := .var 0)))

example {result : Value} {store : Store} {fuel : Nat}
    (done : runStateful fuel (.initial (withFrame reference next (body true)) environment before) = .done result store) :
    store.read? 1 = some (encode layout .empty) :=
  (withFrame_restores selected rfl (runStateful_evaluation_sound done)).1

example {result : Value} {store : Store}
    (done : ∃ fuel, runStateful fuel (.initial (withFrame reference next (body false)) environment before) = .done result store) :
    ∃ installed nextStore bodyStore,
      Evaluates (encode layout .empty :: environment) before (next.weakenAt 0) installed nextStore ∧
      Evaluates (.unit :: encode layout .empty :: environment) (nextStore.set 1 installed)
        (((body false).weakenAt 0).weakenAt 0) result bodyStore ∧
      store = bodyStore.set 1 (encode layout .empty) :=
  (withFrame_run_done_iff selected rfl).mp done

private def scopedCases : IO Unit := do
  for failure in [false, true] do
    let expression := withFrame reference next (body failure)
    assertTrue (infer? context expression definitions == some (LanguageResult.resultType .word))
      "actual selector/temporary environment failed Core checking"
    match runStateful 10000 (.initial expression environment before) with
    | .done result store =>
      assertTrue (result == expected failure && store == after) "finite restoration changed body effects/result"
    | result => throw (IO.userError s!"finite context helper did not finish: {reprStr result}")
    let mut state := State.initial expression environment before
    let mut sawPrepared := false
    let mut sawInstalled := false
    let mut sawBodyWrite := false
    let mut completed := false
    for _ in List.range 500 do
      match runStateful 1 state with
      | .outOfFuel checkpoint =>
        sawPrepared := sawPrepared || checkpoint.store.read? 1 == some (encode layout (.named (w 13)))
        sawInstalled := sawInstalled || checkpoint.store.read? 1 == some (encode layout (.named (w 3)))
        sawBodyWrite := sawBodyWrite || checkpoint.store.read? 1 == some (encode layout (.named (w 88)))
        state := checkpoint
      | .done result store =>
        assertTrue (result == expected failure && store == after) "single-step resume lost pending restoration"
        completed := true
        break
      | .fault fault _ => throw (IO.userError s!"typed frame helper faulted: {reprStr fault}")
    assertTrue (completed && sawPrepared && sawInstalled && sawBodyWrite)
      "checkpoints failed to retain actual non-restored context states"

private def nested : IO Unit := do
  let inner := withFrame reference (named layout (w 2)) (LanguageResult.failure .word (.word (w 8)))
  let middle := .letE inner (.pair (.var 0) (.loadCell (reference.weakenAt 0)))
  let expression := withFrame reference (named layout (w 1)) middle
  let expectedType := .product (LanguageResult.resultType .word) layout.type
  assertTrue (infer? context expression definitions == some expectedType) "nested restoration is not typed"
  match runStateful 10000 (.initial expression environment before) with
  | .done result store =>
    assertTrue (result == .pair (.inLeft .word (.word (w 8))) (encode layout (.named (w 1))))
      "inner failure restored the outer caller instead of its saved lexical frame"
    assertTrue (store == before) "outer restoration lost original frame or cyclic administrative cell"
  | result => throw (IO.userError s!"nested frame execution did not finish: {reprStr result}")

private def selectedCases : IO Unit := do
  let captured : ContextFrame := .view (w 41) (w 5) (.lambda (w 17) (.named (w 3)))
  for current in ([.empty, .named (w 99), .lambda (w 99) .empty,
      .view (w 7) (w 11) (.view (w 8) (w 11) .empty), .view (w 7) (w 12) .empty] : List ContextFrame) do
    let env := [Value.pair (encode layout captured) (encode layout current)]
    let expression := lambdaFrame layout (w 11) (.first (.var 0)) (.second (.var 0))
    assertTrue (infer? [.product layout.type layout.type] expression definitions == some layout.type)
      "recursive encoded frame selection was not typed"
    match runStateful 10000 (.initial expression env before) with
    | .done value store =>
      assertTrue (value == encode layout (selectedFrame (w 11) captured current) && store == before)
        "frame selection retained dynamic caller ancestry or changed the store"
    | result => throw (IO.userError s!"encoded frame selection did not finish: {reprStr result}")

example (captured current : ContextFrame) (store : Store) :
    Evaluates [Value.pair (encode layout captured) (encode layout current)] store
      (lambdaFrame layout (w 11) (.first (.var 0)) (.second (.var 0)))
      (encode layout (selectedFrame (w 11) captured current)) store :=
  lambdaFrame_evaluates _ (.first (.var rfl)) (.second (.var rfl)) _

def run : IO Unit := do
  scopedCases
  nested
  selectedCases
  IO.println "finite context restoration/reflection, cyclic stores, exact captures and pending resume GREEN"
end Tests.SourceCoreCallableContextFrameProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableContextFrames
set_option autoImplicit false
namespace Tests.SourceCoreCallableContextFrames
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableContextFrames
abbrev ContextFrame := Solcore.Frontend.SourceCoreCallableContextFrames.Frame
private def w (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

example : RuntimeValueHasType [] (encode layout (.lambda (w 1) (.view (w 7) (w 1) (.named (w 3)))))
    layout.type definitions := encode_runtime_typed [] registered _

private def scopedBody (fail : Bool) : Expr :=
  .letE (.storeCell (.var 1) (.word (w 7)))
    (if fail then LanguageResult.failure .word (.word (w 23)) else LanguageResult.success (.word (w 11)))
private def program (fail : Bool) : Program := ⟨LanguageResult.resultType .word,
  .letE (.newCell .word (.word (w 99)))
    (allocate layout (withFrame (.var 0) (named layout (w 3)) (scopedBody fail))), definitions⟩

private def quoteFrame : ContextFrame → Expr
  | .empty => empty layout
  | .named origin => named layout origin
  | .lambda origin captured => lambda layout origin (quoteFrame captured)
  | .view id target parent => view layout id target (quoteFrame parent)

private def lambdaCase (current captured : ContextFrame) (expected : ContextFrame) : IO Unit := do
  let program : Program := ⟨layout.type, lambdaFrame layout (w 11) (quoteFrame captured) (quoteFrame current), definitions⟩
  assertTrue program.check "dynamic lambda context failed actual Core checking"
  match program.runStateful 10000 with
  | .done result store =>
      assertTrue (result == encode layout expected) "dynamic lambda context changed lexical ancestry"
      assertTrue store.isEmpty "context selection allocated cells"
  | result => throw (IO.userError s!"dynamic lambda context did not finish: {reprStr result}")

def run : IO Unit := do
  for fail in [false, true] do
    let program := program fail
    assertTrue program.check "administrative context save/restore failed Core checking"
    let expected := if fail then Value.inLeft .word (.word (w 23)) else .inRight .word (.word (w 11))
    match program.runStateful 10000 with
    | .done result store =>
        assertTrue (result == expected) "administrative context changed language result"
        assertTrue (store == [.word (w 7), encode layout .empty])
          "context restore lost body effects or retained the callee frame"
    | result => throw (IO.userError s!"administrative context did not finish: {reprStr result}")
    match program.runStateful 9 with
    | .outOfFuel state =>
        match runStateful 10000 state with
        | .done result store =>
            assertTrue (result == expected && store == [.word (w 7), encode layout .empty])
              "administrative context checkpoint/resume changed result or restoration"
        | result => throw (IO.userError s!"context checkpoint did not finish: {reprStr result}")
    | _ => throw (IO.userError "context regression did not suspend")
  let captured : ContextFrame := .lambda (w 17) (.named (w 3))
  lambdaCase .empty captured (.lambda (w 11) captured)
  lambdaCase (.named (w 99)) captured (.lambda (w 11) captured)
  lambdaCase (.lambda (w 99) .empty) captured (.lambda (w 11) captured)
  lambdaCase (.view (w 7) (w 11) (.named (w 99))) captured
    (.lambda (w 11) (.view (w 7) (w 11) captured))
  lambdaCase (.view (w 7) (w 12) (.named (w 99))) captured (.lambda (w 11) captured)
  IO.println "ordinary Core dynamic callable ancestry and scoped context restoration GREEN"

end Tests.SourceCoreCallableContextFrames
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableContracts
#check_failure Solcore.Frontend.SourceCoreCallableContracts.Descriptor.mk
#check_failure Solcore.Frontend.SourceCoreCallableContracts.Callsite.mk
#check_failure fun (site : Solcore.Frontend.SourceCoreCallableContracts.Callsite) => { site with call := site.call }

set_option autoImplicit false

namespace Tests.SourceCoreCallableContracts

open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableContracts

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function before() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function after() returns (comptime<Word>) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function accepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }"
  ]}] }

private def prepare (program : CheckedProgram) (name : String) : IO (SourceCoreStageCodebook.Table × Key) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError "callable adapter root missing")
  let key : Key := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 16 with
    | .ok (.complete plan) => match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
      | .ok plan => pure plan
      | .error error => throw (IO.userError s!"callable adapter plan failed {reprStr error}")
    | other => throw (IO.userError s!"callable adapter discovery failed {reprStr other}")
  let types := [.word, TypeSystem.Ty.product .word .word, .function (.product .word .word) .word]
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 64 types with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"callable adapter catalog failed {reprStr error}")
  match SourceCoreStageCodebook.prepare program plan checked with
  | .ok table => pure (table, key)
  | .error error => throw (IO.userError s!"callable adapter codebook failed {reprStr error}")

private def reasonAt : ReasonAt := fun _ _ _ phase _ =>
  match phase with | .beforeArguments => word 71 | .beforeApplication => word 73

private def raw : Core.Expr :=
  Core.TaggedFunction.anonymous (.lambda (.product .word .word) (Core.LanguageResult.resultType .word)
    (.letE (.storeCell (.var 1) (.word (word 777))) (Core.LanguageResult.success (.word (word 7)))))

private def argument : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 22)))
    (Core.LanguageResult.success (.pair (.word (word 1)) (.word (word 2))))

private def native (site : Callsite) (id : Core.Word) (calleeFailure : Bool) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (.newCell .word (.word (word 0)))
    (site.lower (word 74) .word
      (.letE (.storeCell (.var 0) (.word (word 11)))
        (if calleeFailure then Core.LanguageResult.failure
          (Core.CallableContract.functionType (.product .word .word) .word) (.word (word 72))
         else Core.LanguageResult.success (Core.CallableContract.wrap id (raw.weakenAt 0))))
      argument)
}

private def testNative (site : Callsite) (id : Core.Word) (reason : Option Nat) (trace : Nat) : IO Unit := do
  for failure in [false, true] do
    let program := native site id failure
    assertTrue program.check "callable adapter native fixture failed checking"
    let result := if failure then Core.Value.inLeft .word (.word (word 72)) else
      match reason with | none => .inRight .word (.word (word 7)) | some reason => .inLeft .word (.word (word reason))
    let store := [Core.Value.word (word (if failure then 11 else trace))]
    assertTrue (program.runStateful 200 == .done result store)
      "callable adapter changed callee/stage/argument/arity/body order"
    match program.runStateful 12 with
    | .outOfFuel checkpoint =>
        assertTrue (Core.runStateful 188 checkpoint == .done result store)
          "callable adapter checkpoint changed guards or store"
    | _ => throw (IO.userError "callable adapter must suspend at fuel twelve")

example (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row) :
    Core.CallableContract.decision site.gates phase unknown id = reason row site.reasonAt phase :=
  site.decision_known phase unknown id row found

example (site : Callsite) (phase : Phase) (unknown id : Core.Word) (missing : site.rowAt? id = none) :
    Core.CallableContract.decision site.gates phase unknown id = some unknown :=
  site.decision_unknown phase unknown id missing

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"callable adapter source failed {reprStr error}")
  for (name, expectedReason, trace) in [("before", some 71, 11), ("after", some 73, 22), ("accepted", none, 777)] do
    let (table, key) ← prepare program name
    let entry ← match table.entries.filter (fun entry => match entry.origin with
      | .lambda owner _ [] => decide (owner = key) | _ => false) with
      | [entry] => pure entry | _ => throw (IO.userError "callable adapter lambda origin missing")
    let row ← match table.decisions.filter (fun row => decide (row.caller = key) && row.entry.id == entry.id) with
      | [row] => pure row | _ => throw (IO.userError "callable adapter callsite missing")
    let descriptor ← match SourceCoreCallableContracts.descriptor table entry.origin with
      | .ok descriptor => pure descriptor
      | .error error => throw (IO.userError s!"callable descriptor rejected {reprStr error}")
    assertTrue (descriptor.id == entry.id) "callable descriptor mismatched its sealed origin"
    let site ← match prepareCallsite table key row.call reasonAt with
      | .ok site => pure site | .error error => throw (IO.userError s!"callable callsite rejected {reprStr error}")
    testNative site descriptor.id expectedReason trace
    testNative site Core.Word.zero (some 74) 11
    for row in site.rows do
      for phase in [Core.CallableContract.Phase.beforeArguments, .beforeApplication] do
        assertTrue (Core.CallableContract.decision site.gates phase (word 74) row.entry.id ==
          reason row reasonAt phase) "callable gate altered the retained exact decision"
    let missing : Origin := .named ⟨key.declaration, [.bool]⟩
    assertTrue (match SourceCoreCallableContracts.descriptor table missing with
      | .error (.missingOrigin _) => true | _ => false) "unregistered origin acquired a descriptor"
    let absent := {row.call with occurrence := {row.call.occurrence with index := row.call.occurrence.index + 100000}}
    assertTrue (match prepareCallsite table key absent reasonAt with
      | .error (.missingCallsite _ _) => true | _ => false) "unregistered callsite acquired gates"

end Tests.SourceCoreCallableContracts
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableEquality
/-! Contract descriptors govern calls; source equality observes the retained
function identity. The same compiler certificates cover both catalog profiles. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableEquality
open Solcore Solcore.Core Solcore.Frontend SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataEquality DataEquality DataEqualityValues DataEqualityCertificates

private def word (value : Nat) : Word := Word.ofNatModulo value
private def catalog : SourceCoreDataCatalog.Catalog := { callableContracts := true }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩

private def oneIdentity (function : Dynamic.GlobalFunction) (source : Dynamic.Value) (id : Word) : Prop :=
  source = .global function ∧ id = Word.zero
private theorem oneFaithful (function : Dynamic.GlobalFunction) : IdentityFaithful (oneIdentity function) := by
  constructor
  · intro source id represented
    rw [represented.1]
    exact .global _
  · intro left right leftId rightId leftRep rightRep
    simp [leftRep.1, rightRep.1, leftRep.2, rightRep.2]

/-- A legacy tagged function cannot masquerade as a product component in the
contracted profile's equality relation. Core typing alone is not that relation. -/
example {source : Dynamic.Value} {value : Value} {parameter result : Ty}
    (observed : Observation catalog signatures (fun _ _ => False)
      (TaggedFunction.functionType parameter result) source value) : False :=
  Carrier.not_tagged_contract observed.carrier

/-- Descriptor words and closure code can differ while the named source
identity remains equal. Actual generated initialization and invocation follow. -/
example (prepared : Prepared checked)
    (type : prepared.type = CallableContract.functionType .word .word)
    (function : Dynamic.GlobalFunction) (leftCode rightCode : Value) (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (.initial (.letE prepared.expression
        (.apply (.var 0) (.pair (.var 1) (.var 2))))
        [.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7)),
         .pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))] store) =
        .done (.bool true) store := by
  have left : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7))) :=
    type ▸ .contractedIdentified _ _ _ _ ⟨rfl, rfl⟩ rfl
  have right : Observation catalog signatures (oneIdentity function) prepared.type (.global function)
      (.pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))) :=
    type ▸ .contractedIdentified _ _ _ _ ⟨rfl, rfl⟩ rfl
  obtain ⟨result, meaning, evaluated⟩ := prepared_compare_preserves prepared (oneFaithful function) left right
    [.pair (.pair (.inRight .unit (.word Word.zero)) leftCode) (.word (word 7)),
      .pair (.pair (.inRight .unit (.word Word.zero)) rightCode) (.word (word 9))]
    store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have same : result = true := meaning.mpr ⟨rfl, .global _⟩
  subst result
  have noBodies : prepared.bodies = [] := by
    have generated := prepared.bodiesGenerated
    simpa [helperBodies, checked, catalog, pure, Except.pure] using generated.symm
  simpa [checked, catalog, noBodies, DataEqualityInstalled.cells, Expr.weakenAt]
    using evaluation_runStateful_complete_with_sufficient_fuel evaluated

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def raw : Expr :=
  .lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0))
private def effectful : Expr :=
  .lambda .word (LanguageResult.resultType .word)
    (.letE (.newCell .word (.var 0)) (LanguageResult.success (.loadCell (.var 0))))
private def named (contract : Nat) (code : Expr := raw) : Expr :=
  CallableContract.wrap (word contract) (TaggedFunction.identified Word.zero code)
private def anonymous (contract : Nat) : Expr :=
  CallableContract.wrap (word contract) (TaggedFunction.anonymous raw)

private def compare (checked : SourceCoreDataCatalog.Checked) (type : TypeSystem.Ty)
    (left right : Expr) (expected : Bool) : IO Unit := do
  let prepared ← match SourceCoreDataEquality.prepare 64 checked type with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"callable equality compilation failed: {reprStr error}")
  let expression := Expr.letE prepared.expression
    (.pair (.apply (.var 0) (.pair left right)) (.apply (.var 0) (.pair right left)))
  let program : Core.Program := ⟨.product .bool .bool, expression, checked.catalog.definitions⟩
  assertTrue program.check "callable equality program failed checking"
  match program.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .pair (.bool expected) (.bool expected)) "callable equality changed source identity"
      assertTrue (store.length == checked.catalog.entries.length) "equality invoked closure effects or reinstalled helpers"
  | other => throw (IO.userError s!"callable equality failed: {reprStr other}")
  match program.runStateful 4 with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful 9996 checkpoint == program.runStateful 10000)
        "callable equality resume changed result or store"
  | _ => throw (IO.userError "callable equality did not suspend at fuel four")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "enum Tree<T> { Leaf(T), Pair(Tree<T>, Tree<T>) }\nfunction identity(value: Word) returns (Word) { return value; }"}]
}

def run : IO Unit := do
  let functionType := TypeSystem.Ty.function .word .word
  compare checked functionType (named 7) (named 9 effectful) true
  compare checked functionType (anonymous 7) (anonymous 7) false
  compare checked functionType (anonymous 7) (named 7) false
  compare checked (.product functionType .word)
    (.pair (named 7) (.word (word 1))) (.pair (named 9) (.word (word 2))) false
  compare checked (.product functionType .word)
    (.pair (named 7) (.word (word 1))) (.pair (named 9) (.word (word 1))) true
  let legacy : SourceCoreDataCatalog.Checked :=
    ⟨{}, DataEnvironment.isWellFormed_sound (by decide)⟩
  compare legacy (.product functionType .word)
    (.pair (TaggedFunction.identified Word.zero raw) (.word (word 7)))
    (.pair (TaggedFunction.identified Word.zero raw) (.word (word 9))) false
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"callable equality source failed: {reprStr error}")
  let declaration ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some declaration => pure declaration
    | none => throw (IO.userError "callable equality Tree signature missing")
  let treeType := TypeSystem.Ty.nominal declaration.id [functionType]
  let recursive ← match SourceCoreDataCatalog.prepare program.signatures 64 [treeType] true with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"callable recursive catalog failed: {reprStr error}")
  let id ← match recursive.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "callable recursive identity missing")
  let leaf := fun code => Expr.construct ⟨id, 0⟩ code
  let node := fun a b => Expr.construct ⟨id, 1⟩ (.pair a b)
  compare recursive treeType
    (node (leaf (named 7)) (leaf (named 7)))
    (node (leaf (named 9 effectful)) (leaf (named 9))) true
  compare recursive treeType
    (node (leaf (named 7)) (leaf (anonymous 7)))
    (node (leaf (named 9)) (leaf (anonymous 7))) false
  IO.println "callable equality profiles, generated certificates and recursive payloads GREEN"

end Tests.SourceCoreCallableEquality
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedFrames
/-! Small kernel-checked native laws. The carrier preserves parent order and
rejects malformed shapes. These tests intentionally grant no provenance to a
well-typed frame or to its numeric words; owned compiler tests supply that
separate boundary. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedFrames
open Solcore Core Frontend
abbrev PairedFrame := Solcore.Frontend.SourceCoreCallablePairedFrames.Frame
private def w (n : Nat) : Word := Word.ofNatModulo n
private def layout : Solcore.Frontend.SourceCoreCallablePairedFrames.Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def caller : PairedFrame := .named (w 7)
private def lexical : PairedFrame := .named (w 8)
private def current : PairedFrame := .view (w 3) (w 9) caller
private def paired : PairedFrame := .appliedView (w 3) (w 9) caller lexical

example : definitions.WellFormed := DataEnvironment.isWellFormed_sound rfl

example : RuntimeValueHasType [] (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) layout.type definitions :=
  Solcore.Frontend.SourceCoreCallablePairedFrames.encode_runtime_typed [] registered paired

example : SourceCoreCallablePairedFrameCodec.decode layout (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) = some paired :=
  SourceCoreCallablePairedFrameCodec.decode_encode layout paired

example : Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired ≠ Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout (.appliedView (w 3) (w 9) lexical caller) := by
  intro same
  have decoded := congrArg (SourceCoreCallablePairedFrameCodec.decode layout) same
  rw [SourceCoreCallablePairedFrameCodec.decode_encode, SourceCoreCallablePairedFrameCodec.decode_encode] at decoded
  have different : paired ≠ .appliedView (w 3) (w 9) lexical caller := by decide
  exact different (Option.some.inj decoded)

example : SourceCoreCallablePairedFrameCodec.decode layout
    (.constructed layout.appliedView (.pair (.word (w 3)) (.pair (.word (w 9)) .unit))) = none := rfl

example : SourceCoreCallablePairedFrameCodec.decode layout
    (.constructed ⟨⟨1⟩, 4⟩ (.pair (.word (w 3)) (.pair (.word (w 9))
      (.pair (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller) (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical))))) = none := rfl

example : SourceCoreCallablePairedFrameCodec.decode layout (.cellRef layout.type 0) = none := rfl

example : Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame (w 9) lexical current = paired := rfl

example : Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame (w 10) lexical current = .lambda (w 10) lexical := rfl

example : HasType [layout.type, layout.type] (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1))
    layout.type definitions := Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame_hasType registered (w 9) (.var rfl) (.var rfl)

private theorem selectedEvaluation : Evaluates [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical, Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout current] [.word (w 55)]
    (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1)) (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) [.word (w 55)] :=
  by simpa only [Solcore.Frontend.SourceCoreCallablePairedFrames.selectedFrame, current, paired, ↓reduceIte] using
    SourceSemantics.CoreLowering.CallablePairedContextFrames.lambdaFrame_evaluates
      (layout := layout) (lexicalFrame := lexical) (currentFrame := current) (w 9) (.var rfl) (.var rfl) [.word (w 55)]

example : ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel (.initial (Solcore.Frontend.SourceCoreCallablePairedFrames.lambdaFrame layout (w 9) (.var 0) (.var 1))
    [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout lexical, Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout current] [.word (w 55)]) =
    .done (Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout paired) [.word (w 55)] :=
  evaluation_runStateful_complete_with_sufficient_fuel selectedEvaluation

/-- Failure does not read a missing administrative reference. -/
example : Evaluates [] []
    (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower layout .word .word (w 3) (w 9) 999
      (LanguageResult.failure (CallableContract.functionType .word .word) (.word (w 44))))
    (.inLeft (CallableContract.functionType .word .word) (.word (w 44))) [] :=
  Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower_failure (.inLeft .word)

private def original : Value :=
  .pair (.pair (.inLeft .word .unit)
    (.closure .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0)) [.cellRef layout.type 0])) (.word (w 9))
private def originalExpression : Expr :=
  .pair (.pair (.inLeft .word .unit)
    (.lambda .word (LanguageResult.resultType .word) (LanguageResult.success (.var 0)))) (.word (w 9))

/-- Successful wrapping saves the frame at the read, then the original
callable, and preserves the heap exactly. Both identity fields remain intact. -/
example : Evaluates [.cellRef layout.type 0] [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller]
    (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower layout .word .word (w 3) (w 9) 0 (LanguageResult.success originalExpression))
    (.inRight .word (.pair (.pair (.inLeft .word .unit)
      (.closure .word (LanguageResult.resultType .word) (Solcore.Frontend.SourceCoreCallablePairedAncestry.viewBody layout (w 3) (w 9) 0)
        [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller, original, .cellRef layout.type 0])) (.word (w 9))))
    [Solcore.Frontend.SourceCoreCallablePairedFrames.encode layout caller] :=
  Solcore.Frontend.SourceCoreCallablePairedAncestry.viewLower_evaluates (.inRight (.pair (.pair (.inLeft .unit) .lambda) .word)) rfl rfl

end Tests.SourceCoreCallablePairedFrames
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedHeaders
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.PrincipalHeader.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.LambdaHeader.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedHeaders.Prepared.mk

/-! The cache stores raw principal headers from actual paired source states.
Open unused principals survive even when the native context also contains an
unrelated caller substitution. Capture provenance is tested by runtime joins. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedHeaders
open Solcore Solcore.Frontend SourceInference
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let unused = lam(value) { return value; }; let local = lam(value: Word) -> Word { return value; }; local(0); return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }"
  ]}] }

def run : IO Unit := do
  let program ← get "paired header checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "sharedHistory") with
    | some signature => pure signature | none => throw (IO.userError "missing paired header root")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"paired header plan failed: {reprStr other}")
  let automatic ← get "paired header compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let graph ← get "paired header graph" (SourceCoreCallableAncestryPairedPreparation.prepare automatic.prepared)
  let headers ← get "paired raw headers" (SourceCoreCallablePairedHeaders.prepare graph)
  let mut different := 0
  for header in headers.principalHeaders do
    if header.principal.principal.binder.name == "unused" && header.state.metadata.active != header.state.nativeActive then
      assertTrue (!header.resultType.freeVariables.isEmpty) "unused principal lost its open source result"
      assertTrue (header.parameters.length == 1 && !header.body.isEmpty) "raw lambda header was discarded"
      let cell := header.cell []
      assertTrue (cell.type == header.declaration.binder.scheme.body) "source cell type came from the native binder"
      match cell.value with
      | some (.closure parameters result body source owner captured evidence) =>
        assertTrue (parameters == header.parameters && result == header.resultType && body == header.body &&
          source == header.state.metadata.source && owner == header.state.metadata.owner &&
          captured.isEmpty && reprStr evidence == reprStr header.principal.context.evidence)
          "principal restoration changed raw metadata, captures or evidence"
      | _ => throw (IO.userError "unused principal native bundle replaced its source closure")
      if header.state.metadata.source != header.principal.context.source then different := different + 1
  assertTrue (different > 0) "missing distinct source/native principal context"
  assertTrue (!headers.lambdaHeaders.isEmpty) "ordinary lambda header cache was empty"
  assertTrue ((headers.lambdaAt? 999999 (Core.Word.ofNatModulo 999999)).isNone) "foreign lambda header accepted"
  let native ← get "paired header native program" (SourceCoreCallablePairedPrograms.prepare automatic.prepared 500)
  let nativeGraph ← get "owned native header graph" (SourceCoreCallableAncestryPairedPreparation.prepare native.base)
  let nativeHeaders ← get "owned native headers" (SourceCoreCallablePairedHeaders.prepare nativeGraph)
  let owner : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer 17)⟩, ⟨.bool, none⟩]
  for budget in [0, 31, 211, 100000] do
    let completion ← get "paired header execution" (native.runSource owner [.word (Core.Word.ofNatModulo 3)] budget)
    let completion := completion.resume 100000
    let ledger ← get "paired header observed ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let rows := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (rows.length == 2) "unused principal allocation count changed"
    for row in rows do
      assertTrue (row.payload == some Core.Value.unit) "unused source principal acquired executable native instances"
      let restored ← get "actual paired principal restoration" (SourceCoreCallablePairedPrincipalAllocations.restore (program := native) nativeHeaders row)
      assertTrue (!restored.header.resultType.freeVariables.isEmpty &&
        restored.header.state.metadata.active != restored.header.state.nativeActive)
        "allocation restoration replaced open raw source metadata with native cumulative context"
      assertTrue (restored.header.state.metadata.source != restored.header.principal.context.source)
        "actual shared allocation lost its lexical source"
      match restored.cell.value with
      | some (.closure _ _ _ source key captured _) =>
        assertTrue (source == restored.header.state.metadata.source && key == owner && captured.length == 2 &&
          captured.all (fun entry => initial.length ≤ entry.2.index)) "actual principal captures lost source prefix or lexical scope"
      | _ => throw (IO.userError "actual Unit principal was not restored to a source closure")
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == Core.Word.ofNatModulo 6) "paired principal restoration changed computation"
    | _ => throw (IO.userError "paired principal execution did not finish")
  IO.println "paired cached raw headers: unused open principals, ordinary lambdas, separate source/native contexts GREEN"

end Tests.SourceCoreCallablePairedHeaders
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedOutputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedOutputs.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedOutputs.Located.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedOutputs.Leaf.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedOutputs.Success.mk

set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev SourceValue := SourceTypedRuntime.Value
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "enum Holder { Hold(Word, F) }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function tuple(seed: Word) returns (F, F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return (f, f); }",
    "function nominal(seed: Word) returns (Holder) { let f = lam(item) { keep(item); seed += 1; return seed; }; return .Hold(7, f); }",
    "function mappingReturn(value: mapping(Word => F), seed: Word) returns (mapping(Word => F)) { let f = lam(item) { keep(item); seed += 1; return seed; }; value[4] = f; return value; }",
    "function plain(seed: Word) returns (Word, Bool) { return (seed, true); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"deep output fixture missing {name}")
private structure Projected (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.function .word .word, none⟩]
private def prefixMatches (heap : List SourceTypedRuntime.Cell) : Bool :=
  reprStr (heap.take initial.length) == reprStr initial

private def closure (plan : SourceSpecializationWorklist.Plan) (value : SourceValue) : IO SourceTypedRuntime.Environment := do
  match value with
  | .instantiated substitution witnesses (.closure parameters _ _ _ _ captured _) =>
    assertTrue (!substitution.isEmpty && witnesses.length == 1) "deep output lost its actual read witnesses"
    assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "deep output specialized its raw original header"
    assertTrue (value.type? plan == some (.function .word .word)) "deep closure restored runtime type changed"
    assertTrue (captured.all (fun binding => initial.length ≤ binding.2.index)) "deep closure referenced opaque source prefix"
    pure captured
  | _ => throw (IO.userError "deep output lost instantiated original closure")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"deep output source rejected: {reprStr error}")
  let roots ← ["tuple", "nominal", "mappingReturn", "plain", "inc"].mapM (key program)
  let requests := roots.map fun owner =>
    (⟨owner.declaration, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"deep output worklist failed: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"deep output base failed: {reprStr error}")
  let native ← match SourceCoreCallablePairedPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"deep output native preparation failed: {reprStr error}")
  let output ← match SourceCoreCallablePairedOutputs.prepare native with
    | .ok output => pure output | .error error => throw (IO.userError s!"deep output caches failed: {reprStr error}")
  let cellHeaders ← match SourceCoreCallablePairedCellHeaders.prepare (program := native) output.graph with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"raw source cell headers failed: {reprStr error}")
  let heapOutput ← match SourceCoreCallablePairedHeapOutputs.prepare native with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"heap output preparation failed: {reprStr error}")
  let inc ← key program "inc"
  let mapping : SourceValue := .mapping .word (.comptime (.function .word .word))
    [(.word (w 4), .global inc []), (.word (w 4), .global inc [])]
  let fixtures : List (String × List SourceValue) :=
    [("tuple", [.word (w 3)]), ("nominal", [.word (w 3)]),
     ("mappingReturn", [mapping, .word (w 3)]), ("plain", [.word (w 3)])]
  for (name, arguments) in fixtures do
    for budget in [0, 29, 100000] do
      let checkpoint ← match native.runSource (← key program name) arguments budget 500 with
        | .ok completion => pure completion
        | .error error => throw (IO.userError s!"deep output native call failed: {reprStr error}")
      if budget == 0 then
        let early ← match SourceCoreCallablePairedHeapOutputs.exportHeap heapOutput checkpoint initial with
          | .ok exported => pure exported | .error error => throw (IO.userError s!"early heap export failed: {reprStr error}")
        assertTrue (early.heap.length == initial.length && prefixMatches early.heap) "zero-fuel export changed opaque source prefix"
      let completion := checkpoint.resume 100000
      let projected ← match same : automatic.checked.catalog.project completion.entry.sourceResultType with
        | .error error => throw (IO.userError s!"deep output projection failed: {reprStr error}")
        | .ok type =>
          if equal : type = completion.entry.native.resultType then
            pure (show Projected automatic.checked completion.entry.sourceResultType completion.entry.native.resultType from
              ⟨by simpa only [equal] using same⟩)
          else throw (IO.userError "deep output native result type changed")
      let decoded ← match SourceCoreCallablePairedOutputs.decodeSuccess output completion completion.entry.sourceResultType
          projected.eq initial 1024 with
        | .ok decoded => pure decoded | .error error => throw (IO.userError s!"deep source output failed: {reprStr error}")
      for row in decoded.ledger.ledger.rows do
        let selected ← match SourceCoreCallablePairedCellHeaders.select cellHeaders row with
          | .ok selected => pure selected | .error error => throw (IO.userError s!"raw allocation header selection failed: {reprStr error}")
        assertTrue (selected.header.raw.binder.id == row.entry.key.binder.id) "raw source cell header changed binder identity"
      let exported ← match SourceCoreCallablePairedHeapOutputs.exportHeap heapOutput completion initial with
        | .ok exported => pure exported | .error error => throw (IO.userError s!"paired source heap export failed: {reprStr error}")
      assertTrue (prefixMatches exported.heap) "heap export changed opaque source prefix"
      assertTrue (exported.cells.length == decoded.ledger.ledger.rows.length) "heap export lost source allocation order"
      let genericRows := decoded.ledger.ledger.rows.filter (fun row => !row.entry.key.binder.scheme.quantified.isEmpty)
      if name != "plain" then
        assertTrue (!genericRows.isEmpty) "generic closure fixture no longer records a principal"
      for row in genericRows do
        match exported.heap[row.sourceLocation.index]? with
        | some ⟨_, some (.closure parameters _ _ _ _ captured _)⟩ =>
          assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "heap export specialized original principal"
          assertTrue (captured == row.environment) "heap export changed principal capture order or aliases"
        | _ => throw (IO.userError "heap export lost raw generic principal closure")
      match name, decoded.decoded.source with
      | "tuple", .product left right =>
        let leftEnv ← closure plan left
        let rightEnv ← closure plan right
        assertTrue (leftEnv == rightEnv && leftEnv.length == 1) "deep tuple split the shared seed cell"
      | "nominal", .constructed _ [.word number, value] =>
        assertTrue (number == w 7) "nominal data changed alongside closure restoration"
        assertTrue ((← closure plan value).length == 1) "nominal closure lost source capture"
      | "mappingReturn", .mapping keyType valueType [(.word first, left), (.word second, .global owner _)] =>
        assertTrue (keyType == .word && valueType == .comptime (.function .word .word)) "deep mapping raw metadata changed"
        assertTrue (first == w 4 && second == w 4 && owner == inc) "deep mapping duplicate order changed"
        assertTrue ((← closure plan left).length == 2) "deep mapping closure lost value/seed captures"
      | "plain", .product (.word number) (.bool flag) => assertTrue (number == w 3 && flag) "data-only output changed"
      | _, value => throw (IO.userError s!"unexpected deep source output {name}: {reprStr value}")
      match SourceCoreCallablePairedOutputs.locate completion decoded.ledger (.word (w 987654321)) with
      | .error .unavailableValue => pure () | _ => throw (IO.userError "foreign value gained native result/payload provenance")
  let hidden := Core.Value.cellRef .word 42
  let carrier := Core.Value.closure .unit .unit .unit [hidden]
  assertTrue (SourceCoreCallableNativeSubvalues.find hidden carrier |>.isNone) "public native path entered a closure environment"
  IO.println "deep paired tuple/nominal/mapping closure outputs, raw metadata and native data origins GREEN"

end Tests.SourceCoreCallablePairedOutputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedProtocol
/-! Finite protocol regressions retain metadata receipts and exact native
administrative contexts. Failure restores the original current frame. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallablePairedProtocol
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallablePairedProtocol SourceCoreCallablePairedFrames

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {lexical current : PairedFrame} {state : MetadataState} {origin : Word}
    (entry : Entry inputs origin lexical current state) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) := entry.authenticates

/-- Both distinct parent histories survive a matching applied view. Witness
preparation uses the caller; its rewrite target is the lexical metadata. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical : PairedFrame} {callerState lexicalState : MetadataState} {id target : Word}
    (callerHistory : Authenticates inputs caller (some callerState))
    (lexicalHistory : Authenticates inputs lexical (some lexicalState))
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id target = .ok read)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexicalState)
    (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexicalState = .ok applied) :
    Authenticates inputs (.appliedView id target caller lexical) (some (read.after lexicalState)) := by
  simpa only [selectedFrame, ↓reduceIte] using
    (Entry.applied callerHistory lexicalHistory read prepared applied appliedPrepared).authenticates

/-- A body returning a language failure is still a completed call: restoration
uses the saved frame, preserving its current stable or transient history. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {lexical current : PairedFrame} {state : MetadataState} {origin reason : Word}
    (saved : Current inputs current) (entry : Entry inputs origin lexical current state) :
    Evaluates [.unit, encode layout lexical, .cellRef layout.type 0] [encode layout current]
      (withFrame (.var 2)
        (lambdaFrame layout origin (.var 1) (.loadCell (.var 2)))
        ((LanguageResult.failure .unit (.word reason)).weakenAt 1))
      (.inLeft .unit (.word reason)) [encode layout current] := by
  have caller : CellState inputs layout 0 current [encode layout current] := ⟨rfl, saved⟩
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .unit, encode layout lexical, .cellRef layout.type 0]
      ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current)))
      ((((LanguageResult.failure .unit (.word reason)).weakenAt 1).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason)) ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current))) := by
    simpa [LanguageResult.failure, Expr.weakenAt] using
      (show Evaluates [.unit, encode layout current, .unit, encode layout lexical, .cellRef layout.type 0]
        ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current)))
        (.inLeft .unit (.word reason)) (.inLeft .unit (.word reason))
        ([encode layout current].set 0 (encode layout (selectedFrame origin lexical current))) from .inLeft .word)
  have evaluated := (lambda_body_evaluates (referenceIndex := 0) (environment := [.cellRef layout.type 0])
    (argument := .unit) rfl caller entry bodyEvaluation).2.1
  simpa using evaluated

/-- An actual successful compiler hook, rather than an arbitrary typed closure,
provides the exact native formation expression and its static origin receipt. -/
example {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (prepared : SourceCoreCallablePairedAncestry.Prepared base)
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {context : SourceCoreFunctions.Context} {source : SourceInference.TypedSource}
    {scope : SourceCoreFunctions.Scope} {node : SourceInference.ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : SourceCoreCallablePairedAncestry.expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = SourceCoreCallablePairedAncestry.snapshotLambda prepared.layout.frame origin
        (SourceCoreCallablePairedAncestry.creationReferenceIndex context scope) parameter result body :=
  CallablePairedEmission.expressionHook_receipt prepared accepted

end Solcore.Test.SourceCoreCallablePairedProtocol
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedReadViews
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedReadViews.Template.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedReadViews.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedReadViews.Produced.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedReadViews.Stored.mk

/-! Actual compiler output supplies the transparent read wrapper and its saved
original callable. Result and stored-payload provenance are kept separately.
The tests check native code/descriptor authenticity and by-value captures: two
reads of one generalized local share its principal's snapshot cells, and each
call starts again from them. Dynamic requirement rewriting is deliberately left
to the prepared ancestry metadata layer, rather than inferred from canonical
read rows.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedReadViews
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallablePairedReadViews
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function views(seed: Word) returns (F, F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return (f, f); }",
    "function nested(seed: Word) returns (F, F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); seed += 1; return seed; }; return (inner, inner); }; return outer(1); }",
    "function shared(seed: Word) returns (F, F) { let shared = lam(item) { seed += 1; return seed; }; let outer = lam(value) { keep(value); return (shared, shared); }; return outer(1); }",
    "function mono(seed: Word) returns (F) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return f; }",
    "function failure(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; while (true) {} return 0; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"read views fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["views", "nested", "shared", "mono", "failure", "suspended"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"read views worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"read views base failed: {reprStr error}")
private def initial : SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} {prepared : Prepared checked} (template : Template prepared) :
    template.carrier = SourceCoreCallablePairedAncestry.viewRepack prepared.ancestry.layout.frame
      template.parameter template.result template.entry.id template.target template.referenceIndex := template.carrierExact

example {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : Authenticated cache world store value) :
    Core.RuntimeValueHasType world authenticated.original
      (Core.CallableContract.functionType authenticated.wrapper.parameter authenticated.wrapper.result)
      prepared.layouts.definitions := authenticated.originalTyped

private def retag (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with | .pair tagged _ => .pair tagged (.word descriptor) | other => other
private theorem retag_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty} (descriptor : Core.Word)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter result) definitions) :
    Core.RuntimeValueHasType world (retag value descriptor) (Core.CallableContract.functionType parameter result) definitions := by
  cases typed with | pair tagged _ => exact .pair tagged .word

private def replaceBody (value : Core.Value) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result _ environment)) descriptor =>
      .pair (.pair identity (.closure parameter result (Core.LanguageResult.success (.word (w 999))) environment)) descriptor
  | other => other
private theorem replaceBody_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter : Core.Ty}
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter .word) definitions) :
    Core.RuntimeValueHasType world (replaceBody value) (Core.CallableContract.functionType parameter .word) definitions := by
  cases typed with
  | pair tagged descriptor =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment _ => exact .pair (.pair identity (.closure environment (.inRight .word .word))) descriptor

private def replaceSavedDescriptor (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result body (caller :: original :: outer))) own =>
      .pair (.pair identity (.closure parameter result body (caller :: retag original descriptor :: outer))) own
  | other => other

private theorem replaceSavedDescriptor_typed {checked : Checked} {prepared : Prepared checked}
    {templates : Templates prepared} {cache : Cache templates} {world : Core.StoreTyping}
    {store : Core.Store} {value : Core.Value} (authenticated : Authenticated cache world store value)
    (descriptor : Core.Word) : Core.RuntimeValueHasType world (replaceSavedDescriptor value descriptor)
      (Core.CallableContract.functionType authenticated.wrapper.parameter authenticated.wrapper.result)
      prepared.layouts.definitions := by
  have typed := authenticated.typed
  conv at typed => arg 2; rw [authenticated.exact]
  conv => arg 2; rw [authenticated.exact]; simp only [replaceSavedDescriptor]
  cases typed with
  | pair tagged own =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment body =>
        cases environment with
        | cons caller rest =>
          cases rest with
          | cons original outer =>
            have changed := retag_typed descriptor authenticated.originalTyped
            rw [← authenticated.originalTyped.type_eq, original.type_eq] at changed
            exact .pair (.pair identity (.closure (.cons caller (.cons changed outer)) body)) own

private def reuse {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (left right : Core.Value)
    (leftTyped : Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) definitions)
    (rightTyped : Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) definitions)
    (frame : SourceCoreCallablePairedFrames.Layout) (snapshot allocated : Nat) : IO Unit := do
  let body := Core.LocalSequence.pair .word .word
    (.apply (.second (.first (.var 1))) (.word (w 10)))
    (.apply (.second (.first (.var 0))) (.word (w 20)))
  have typed : Core.HasType [Core.CallableContract.functionType .word .word, Core.CallableContract.functionType .word .word]
      body (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := .initial body [right, left] store
    typed := .eval stored (.cons rightTyped (.cons leftTyped .nil)) typed .nil }
  for spent in [0, 31, 100000] do
    let first := checkpoint.resume spent
    let completed := match first.checkpoint? with | none => first | some checkpoint => checkpoint.resume 100000
    match completed.observation with
    | .succeeded (.pair (.word first) (.word second)) final =>
      -- Each call starts again from the principal's snapshot `seed = 3`.
      assertTrue (first == w 4 && second == w 4) "read wrapper did not restart each call from the principal's snapshot"
      assertTrue (final[snapshot]? == some (.inRight .unit (.word (w 3)))) "read wrapper call wrote the principal's snapshot cell"
      assertTrue (final[0]? == some (SourceCoreCallablePairedFrames.encode frame .empty)) "view/lambda frames were not restored"
      assertTrue (final.length == store.length + allocated) "view reentry changed actual capture copies or source parameter allocations"
    | observation => throw (IO.userError s!"read wrapper reentry failed: {reprStr observation}")

private def pair {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) (nested sharedPrincipal : Bool) : IO Unit := do
  for spent in [0, 39, 100000] do
    let first ← match prepared.runSource owner [.word (w 3)] spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"read views source run failed: {reprStr error}")
    let _ ← match SourceCoreCallablePairedLedger.scan first initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"read views partial ledger failed: {reprStr error}")
    let completion := first.resume 100000
    if same : completion.entry.native.resultType = .product (Core.CallableContract.functionType .word .word) (Core.CallableContract.functionType .word .word) then
      match success : completion.result.native.observation with
      | .succeeded (.pair left right) store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) left (Core.CallableContract.functionType .word .word) prepared.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) right (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
          obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
          have equal := stored.world_eq
          subst world
          rw [same] at typed
          cases typed with | pair left right => exact ⟨stored, left, right⟩
        let leftAuth ← match authenticate cache typed.1 left .word .word typed.2.1 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"left read wrapper auth failed: {reprStr error}")
        let rightAuth ← match authenticate cache typed.1 right .word .word typed.2.2 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"right read wrapper auth failed: {reprStr error}")
        assertTrue (leftAuth.wrapper.entry.id != rightAuth.wrapper.entry.id) "different reads shared a view token"
        assertTrue (!leftAuth.canonicalOwnSubstitution.isEmpty && !rightAuth.canonicalOwnSubstitution.isEmpty)
          "generalized read lost its own substitution"
        assertTrue (leftAuth.canonicalOwnWitnesses.length == (if sharedPrincipal then 0 else 1) && rightAuth.canonicalOwnWitnesses.length == (if sharedPrincipal then 0 else 1))
          "qualified read lost its exact own witnesses"
        assertTrue (sharedPrincipal || leftAuth.canonicalOwnWitnesses.map (·.actualRequirement) != rightAuth.canonicalOwnWitnesses.map (·.actualRequirement))
          "same-type reads collapsed occurrence-specific requirements"
        assertTrue ((!leftAuth.parentActive.isEmpty) == nested) "parent context was confused with own substitution"
        assertTrue (leftAuth.underlying.template.source.lambda.active == leftAuth.cumulative)
          "underlying native code was not the cumulative selected instance"
        for owned in [(⟨left, leftAuth⟩ : Σ value : Core.Value, Authenticated cache (store.map Core.Value.type) store value), ⟨right, rightAuth⟩] do
          let authenticated := owned.2
          let callerPosition ← match graph.table.lookupIndex? authenticated.caller.frame with
            | some (some index) => pure index | _ => throw (IO.userError "read caller snapshot lacks prepared state")
          let lexicalPosition ← match graph.table.lookupIndex? authenticated.underlying.snapshot.frame with
            | some (some index) => pure index | _ => throw (IO.userError "lexical snapshot lacks prepared state")
          let recipe ← match graph.recipeAt? callerPosition lexicalPosition authenticated.wrapper.entry.id authenticated.wrapper.target with
            | some recipe => pure recipe | none => throw (IO.userError "exact read caller/principal pair lacks cached recipe")
          assertTrue (recipe.read.substitution == authenticated.canonicalOwnSubstitution) "paired read changed its own substitution"
          assertTrue ((!recipe.read.witnesses.isEmpty) == !sharedPrincipal) "paired read inherited unrelated caller witnesses"
          assertTrue ((authenticated.caller.frame != authenticated.underlying.snapshot.frame) == sharedPrincipal)
            "read caller and lexical principal were incorrectly rebased"
          if sharedPrincipal then
            assertTrue (recipe.lexical.nativeActive.isEmpty && !recipe.caller.nativeActive.isEmpty &&
              (recipe.read.after recipe.lexical).metadata.active != (recipe.read.after recipe.lexical).nativeActive)
              "shared principal was forced to use its compiled cumulative context"
        assertTrue (leftAuth.underlying.current.frame == .empty) "returned view retained active administrative context"
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts initial (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"read views ledger failed: {reprStr error}")
        let leftProduced := Produced.of_success (authenticated := leftAuth) success (.pairLeft .root)
        let rightProduced := Produced.of_success (authenticated := rightAuth) success (.pairRight .root)
        let leftJoined ← match joinProduced leftProduced ledger with
          | .ok joined => pure joined | .error error => throw (IO.userError s!"left read captures failed: {reprStr error}")
        let rightJoined ← match joinProduced rightProduced ledger with
          | .ok joined => pure joined | .error error => throw (IO.userError s!"right read captures failed: {reprStr error}")
        assertTrue (leftJoined.captures.environment == rightJoined.captures.environment) "read wrappers lost the principal's shared snapshot environment"
        assertTrue (leftJoined.captures.environment.map Prod.fst == leftAuth.underlying.template.source.scope.map Prod.fst)
          "read wrapper added saved carrier/context slots to source captures"
        assertTrue (leftJoined.captures.environment.all (fun binding => initial.length ≤ binding.2.index))
          "read capture referenced inert source prefix"
        match authenticate cache typed.1 (retag left (w 999999)) .word .word (retag_typed _ typed.2.1) with
        | .error .closureMismatch => pure () | _ => throw (IO.userError "typed foreign view descriptor authenticated")
        match authenticate cache typed.1 (replaceBody left) .word .word (replaceBody_typed typed.2.1) with
        | .error .closureMismatch => pure () | _ => throw (IO.userError "typed foreign view body authenticated")
        match authenticate cache typed.1 (replaceSavedDescriptor left (w 999999)) leftAuth.wrapper.parameter leftAuth.wrapper.result
            (replaceSavedDescriptor_typed leftAuth (w 999999)) with
        | .error (.underlying .closureMismatch) => pure ()
        | _ => throw (IO.userError "typed foreign saved original carrier authenticated")
        if spent == 100000 then
          let seed ← match leftAuth.underlying.sourceCaptures.find? (fun capture =>
              (leftAuth.underlying.template.source.lambda.context.bindingAt? capture.binder).map (·.binding.binder.name) == some "seed") with
            | some capture => pure capture | none => throw (IO.userError "read wrapper source seed capture missing")
          -- Each call makes marked allocations of three cells: the copies of the
          -- principal's captures (`seed`, and in `nested` also `value`), the
          -- lambda's parameter and, except for `shared`, `keep`'s parameter.
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame seed.location
            (if sharedPrincipal then 12 else if nested then 24 else 18)
      | observation => throw (IO.userError s!"read views pair did not succeed: {reprStr observation}")
    else throw (IO.userError "read views pair result projection changed")

private def stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 10000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored read source run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored read observation classification changed"
  let ledger ← match SourceCoreCallablePairedLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored read ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored read allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored read payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallablePairedLedger.world completion) value
          (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
        simpa only [type] using row.payload_typed ledger.typed payloadFound
      let authenticated ← match authenticate cache ledger.typed value .word .word typed with
        | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"stored read auth failed: {reprStr error}")
      let receipt := Stored.of_payload (authenticated := authenticated) rfl ordinal payloadFound .root
      let joined ← match joinStored receipt with
        | .ok joined => pure joined | .error error => throw (IO.userError s!"stored read captures failed: {reprStr error}")
      assertTrue (joined.captures.environment.length == 1) "stored read lost the principal seed capture"
      assertTrue (joined.captures.environment.all (fun binding => initial.length ≤ binding.2.index))
        "stored read capture referenced opaque prefix"
    else throw (IO.userError "stored read callable type changed")

private def monomorphic {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 100000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"mono read failed: {reprStr error}")
  if same : completion.entry.native.resultType = Core.CallableContract.functionType .word .word then
    match success : completion.result.native.observation with
    | .succeeded value store =>
      have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
          Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
        have equal := stored.world_eq
        subst world
        exact ⟨stored, by simpa only [same] using typed⟩
      match authenticate cache typed.1 value .word .word typed.2 with
      | .error .closureMismatch => pure () | _ => throw (IO.userError "monomorphic read was treated as instantiated view")
      match SourceCoreCallablePairedTemplates.authenticate templates typed.1 value .word .word typed.2 with
      | .ok _ => pure () | .error error => throw (IO.userError s!"mono snapshot auth failed: {reprStr error}")
    | _ => throw (IO.userError "mono closure did not complete")
  else throw (IO.userError "mono result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"read views source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallablePairedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"read views marked compiler failed: {reprStr error}")
  let templates ← match SourceCoreCallablePairedTemplates.prepare prepared with
    | .ok templates => pure templates | .error error => throw (IO.userError s!"read views snapshot cache failed: {reprStr error}")
  let cache ← match prepare templates with
    | .ok cache => pure cache | .error error => throw (IO.userError s!"read views emitted wrapper scan failed: {reprStr error}")
  assertTrue (!cache.wrappers.isEmpty) "actual two-pass compiler emitted no read wrappers"
  for wrapper in cache.wrappers do
    match decode prepared wrapper.carrier with
    | .ok decoded => assertTrue (decoded.entry.id == wrapper.entry.id && decoded.body == wrapper.body) "full carrier decoder changed the view"
    | .error error => throw (IO.userError s!"retained wrapper failed complete rescan: {reprStr error}")
    match decode prepared (.pair (.pair .unit (.lambda wrapper.parameter (Core.LanguageResult.resultType wrapper.result) wrapper.body)) (.word wrapper.target)) with
    | .error .malformedWrapper => pure () | _ => throw (IO.userError "carrier with forged copied identity was accepted")
  let graph ← match SourceCoreCallableAncestryPairedPreparation.prepare prepared.base with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"paired graph preparation failed: {reprStr error}")
  pair cache graph (← key program "views") false false
  pair cache graph (← key program "nested") true false
  pair cache graph (← key program "shared") true true
  monomorphic cache (← key program "mono")
  stored cache (← key program "failure") false
  stored cache (← key program "suspended") true
  IO.println "exact emitted read wrappers, saved original auth, ordered snapshot captures, stored failure/suspension and resume GREEN"


end Tests.SourceCoreCallablePairedReadViews
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedRestoration
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.Ordinary.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.Read.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.ProducedRead.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.StoredRead.mk

set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedRestoration
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(seed: Word) returns (F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return f; }",
    "function nested(seed: Word) returns (F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); seed += 1; return seed; }; return inner; }; return outer(1); }",
    "function shared(seed: Word) returns (F) { let f = lam(item) { seed += 1; return seed; }; let outer = lam(value) { keep(value); return f; }; return outer(1); }",
    "function mono(seed: Word) returns (F) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return f; }",
    "function failure(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; while (true) {} return 0; }",
    "function named(seed: Word) returns (F) { return plus; }",
    "function plus(value: Word) returns (Word) { return value + 1; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"restoration fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["qualified", "nested", "shared", "mono", "failure", "suspended", "named"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"restoration worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"restoration base failed: {reprStr error}")
private def initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.function .word .word, none⟩]

private def returned {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallablePairedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    (headers : SourceCoreCallablePairedHeaders.Prepared graph)
    (templates : SourceCoreCallablePairedTemplates.Cache program)
    (views : SourceCoreCallablePairedReadViews.Cache templates) (owner : Key) (ordinary shared : Bool) : IO Unit := do
  for spent in [0, 31, 100000] do
    let first ← match program.runSource owner [.word (w 3)] spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"restoration run failed: {reprStr error}")
    let completion := first.resume 100000
    if same : completion.entry.native.resultType = Core.CallableContract.functionType .word .word then
      match success : completion.result.native.observation with
      | .succeeded value store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store program.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType .word .word) program.layouts.definitions := by
          obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
          have equal := stored.world_eq
          subst world
          exact ⟨stored, by simpa only [same] using typed⟩
        let ledger ← match SourceCoreAllocationLedger.scanTyped program.layouts initial (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"restoration ledger failed: {reprStr error}")
        if ordinary then
          let authenticated ← match SourceCoreCallablePairedTemplates.authenticate templates typed.1 value .word .word typed.2 with
            | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"ordinary auth failed: {reprStr error}")
          let produced := SourceCoreCallablePairedCaptures.Produced.of_success authenticated success .root
          let receipt ← match SourceCoreCallablePairedRestoration.restoreProducedOrdinary headers produced ledger with
            | .ok receipt => pure receipt | .error error => throw (IO.userError s!"ordinary restoration failed: {reprStr error}")
          let restored := receipt.restored
          assertTrue (restored.source.type? program.base.plan == some (.function .word .word)) "ordinary restored type changed"
          match restored.source with
          | .closure parameters result body source owner captures _ =>
            assertTrue (parameters == restored.header.parameters && result == restored.header.resultType && body == restored.header.body)
              "ordinary restoration changed its raw header"
            assertTrue (source == restored.header.state.metadata.source && owner == restored.header.state.metadata.owner)
              "ordinary restoration changed its lexical source"
            assertTrue (captures == restored.captures.environment && captures.length == 1) "ordinary restoration changed captures"
          | _ => throw (IO.userError "ordinary source closure shape changed")
        else
          let authenticated ← match SourceCoreCallablePairedReadViews.authenticate views typed.1 value .word .word typed.2 with
            | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"read auth failed: {reprStr error}")
          let produced := SourceCoreCallablePairedReadViews.Produced.of_success (authenticated := authenticated) success .root
          let receipt ← match SourceCoreCallablePairedRestoration.restoreProducedRead headers produced ledger with
            | .ok receipt => pure receipt | .error error => throw (IO.userError s!"read restoration failed: {reprStr error}")
          let restored := receipt.restored
          assertTrue (restored.source.type? program.base.plan == some (.function .word .word)) "read restored type changed"
          match restored.source with
          | .instantiated substitution witnesses (.closure parameters result body source owner captures _) =>
            assertTrue (substitution == restored.recipe.read.substitution && witnesses.length == (if shared then 0 else 1))
              "read restoration changed its actual own substitution or witnesses"
            assertTrue (parameters == restored.recipe.applied.parameters && result == restored.recipe.applied.resultType && body == restored.recipe.applied.body)
              "read restoration replaced the original raw header"
            assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "read restoration prematurely specialized raw parameters"
            assertTrue (source == restored.recipe.lexical.metadata.source && owner == restored.recipe.lexical.metadata.owner)
              "read restoration used caller source instead of lexical source"
            assertTrue (captures == restored.captures.environment && captures.all (fun binding => initial.length ≤ binding.2.index))
              "read restoration changed source captures or opaque prefix"
            if shared then assertTrue (restored.caller != restored.lexical) "shared read collapsed caller and lexical states"
          | _ => throw (IO.userError "read restoration lost instantiated original closure")
      | _ => throw (IO.userError "restoration invocation did not succeed")
    else throw (IO.userError "restoration result projection changed")

private def stored {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallablePairedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    (headers : SourceCoreCallablePairedHeaders.Prepared graph)
    {templates : SourceCoreCallablePairedTemplates.Cache program}
    (views : SourceCoreCallablePairedReadViews.Cache templates) (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match program.runSource owner [.word (w 3)] 10000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored restoration run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored restoration observation changed"
  let ledger ← match SourceCoreCallablePairedLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored restoration ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored restoration allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored restoration payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallablePairedLedger.world completion) value
          (Core.CallableContract.functionType .word .word) program.layouts.definitions := by
        simpa only [type] using row.payload_typed ledger.typed payloadFound
      let authenticated ← match SourceCoreCallablePairedReadViews.authenticate views ledger.typed value .word .word typed with
        | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"stored restoration auth failed: {reprStr error}")
      let stored := SourceCoreCallablePairedReadViews.Stored.of_payload (authenticated := authenticated) rfl ordinal payloadFound .root
      let receipt ← match SourceCoreCallablePairedRestoration.restoreStoredRead headers stored with
        | .ok receipt => pure receipt | .error error => throw (IO.userError s!"stored read restoration failed: {reprStr error}")
      assertTrue (receipt.restored.source.type? program.base.plan == some (.function .word .word)) "stored source type changed"
      assertTrue (receipt.restored.captures.environment.length == 1) "stored source seed capture missing"
    else throw (IO.userError "stored restoration payload type changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"restoration source rejected: {reprStr error}")
  let automatic ← artifact program
  let native ← match SourceCoreCallablePairedPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"restoration marked compiler failed: {reprStr error}")
  let templates ← match SourceCoreCallablePairedTemplates.prepare native with
    | .ok templates => pure templates | .error error => throw (IO.userError s!"restoration template cache failed: {reprStr error}")
  let views ← match SourceCoreCallablePairedReadViews.prepare templates with
    | .ok views => pure views | .error error => throw (IO.userError s!"restoration wrapper cache failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPairedPreparation.prepare native.base with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"restoration graph failed: {reprStr error}")
  let headers ← match SourceCoreCallablePairedHeaders.prepare graph with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"restoration header cache failed: {reprStr error}")
  returned headers templates views (← key program "qualified") false false
  returned headers templates views (← key program "nested") false false
  returned headers templates views (← key program "shared") false true
  returned headers templates views (← key program "mono") true false
  stored headers views (← key program "failure") false
  stored headers views (← key program "suspended") true
  let outputRecipe ← match SourceCoreCompatibleOutputs.preparePaired native with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"paired output recipe failed: {reprStr error}")
  let named ← match native.runSource (← key program "named") [.word (w 3)] 100000 500 with
    | .ok named => pure named | .error error => throw (IO.userError s!"paired named run failed: {reprStr error}")
  match projected : automatic.checked.catalog.project (.function .word .word) with
  | .error error => throw (IO.userError s!"paired named output projection failed: {reprStr error}")
  | .ok type =>
    if same : type = named.entry.native.resultType then
      have projection : automatic.checked.catalog.project (.function .word .word) = .ok named.entry.native.resultType := by
        simpa only [same] using projected
      match SourceCoreCompatibleOutputs.decodeSuccess outputRecipe named.result.context named.result.contextOwner
          (.function .word .word) projection named.result.native with
      | .ok decoded => match decoded.decoded.source with
        | .global owner _ => assertTrue (owner == (← key program "plus")) "paired global output owner changed"
        | _ => throw (IO.userError "paired named output source shape changed")
      | .error error => throw (IO.userError s!"paired named output decode failed: {reprStr error}")
    else throw (IO.userError "paired named output projection changed")
  IO.println "paired raw closure/read and failed/suspended heap restoration, named exact outputs GREEN"

end Tests.SourceCoreCallablePairedRestoration
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePairedPrograms
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedPrograms.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedAncestry.Prepared.mk

/-! Actual two-pass compiler execution retains a generalized read's caller
snapshot separately from the principal's lexical creation snapshot. Closures
capture by value: a lambda keeps copies of its captured cells made when it is
created, and each call starts again from them. This test uses the owned native
runner and allocation ledger; decoding a frame alone is not treated as evidence
of its execution history or source closure identity.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedPrograms
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared (checked : Checked) := Solcore.Frontend.SourceCoreCallablePairedPrograms.Prepared checked

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let probe: Word = 0; return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }",
    "function getLocal(seed: Word) returns (F) { let f = lam(item) { seed += 1; return item; }; return f; }",
    "function useReturned(seed: Word) returns (Word) { let f = getLocal(seed); return f(8) + f(9); }",
    "function mono(seed: Word) returns (Word) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; f(3); return f(4); }",
    "function zero() returns (Word) { let f = lam() -> Word { let probe: Word = 9; return probe; }; return f(); }",
    "function recursive(n: Word) returns (Word) { let f: F; f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent(seed: Word) returns (Word) { let f = lam(item) { seed += 1; let absent: Word; return absent; }; return f(0); }",
    "function spin() returns (Word) { let f = lam() -> Word { while (true) {} return 0; }; return f(); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"paired native fixture missing {name}")
private def initial : SourceCoreAllocationLedger.SourceHeap :=
  [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} (prepared : Prepared checked) :
    SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallablePairedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : Checked} {prepared : Prepared checked}
    (completion : SourceCoreCallablePairedPrograms.Completion prepared) :
    Core.RuntimeStoreHasTypes (SourceCoreCallablePairedLedger.world completion)
      (SourceCoreCallablePairedLedger.store completion) prepared.layouts.definitions :=
  SourceCoreCallablePairedLedger.store_typed completion

/-- Run `owner` after `spent` fuel to its end and check its ledgers and
restored frame, whatever its outcome. -/
private def completed {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (spent : Nat) :
    IO (SourceCoreCallablePairedPrograms.Completion prepared) := do
  let first ← get "paired native start" (prepared.runSource owner arguments spent 500)
  let early ← get "paired partial typed ledger" (SourceCoreCallablePairedLedger.scan first initial)
  assertTrue (early.ledger.initialHeap.map (·.type) == initial.map (·.type)) "suspension altered inert source prefix"
  let completion := first.resume 150000
  let ledger ← get "paired complete typed ledger" (SourceCoreCallablePairedLedger.scan completion initial)
  assertTrue ledger.ledger.pending.isNone "paired completion retained an incomplete marker"
  assertTrue (ledger.ledger.rows.all (fun row => initial.length ≤ row.sourceLocation.index))
    "paired administrative cell entered the source prefix"
  assertTrue (SourceCoreCallablePairedLedger.frame? completion == some .empty)
    "paired invocation failed to restore its empty current frame"
  pure completion

private def successful {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (expected : Nat) (spent : Nat) :
    IO (SourceCoreCallablePairedPrograms.Completion prepared) := do
  let completion ← completed prepared owner arguments spent
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w expected) "paired execution changed the result"
  | other => throw (IO.userError s!"paired invocation did not succeed: {reprStr other}")
  pure completion

/-- The binder `name` declared in `owner`'s checked body. -/
private def binder {checked : Checked} (prepared : Prepared checked) (owner : Key) (name : String) :
    IO Resolved.LocalId := do
  let specialized ← get "paired specialization" (SourceCompilationPlan.exactSpecialization prepared.base.plan owner)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"paired fixture binder missing {name}")

private def shared {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "paired shared origin missing")
  let lexical : Frame := .named named
  let rootPosition ← match graph.table.lookupIndex? lexical with
    | some (some index) => pure index | _ => throw (IO.userError "paired lexical root unavailable")
  for spent in [0, 31, 150000] do
    let completion ← successful prepared owner [.word (w 3)] 6 spent
    let ledger ← get "shared paired ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let shared ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some row => pure row | none => throw (IO.userError "paired shared bundle missing")
    -- The principal captures the copy of `seed` taken around its declaration,
    -- allocated after the input and right before the principal's own cell.
    let [input, seed] := (ledger.ledger.rows.takeWhile (·.entry.key.binder.name != "shared")).filter
        (·.entry.key.binder.name == "seed")
      | throw (IO.userError "paired shared seed or its snapshot missing")
    assertTrue (shared.environment == [(seed.entry.key.binder.id, seed.sourceLocation)] && seed.payload == input.payload)
      "read-parent compilation changed the principal's lexical environment"
    let mut callers : List Frame := []
    let mut sources : List TypedSource := []
    for row in ledger.ledger.rows do
      let snapshot ← get "paired allocation snapshot"
        (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue ((graph.table.lookup? snapshot.frame).isSome)
        s!"actual paired allocation {row.entry.key.binder.name} lacks cached metadata"
      if row.entry.key.binder.name == "probe" then
        match snapshot.frame with
        | .appliedView read target caller captured =>
          assertTrue (captured == lexical) "shared principal's creation snapshot was replaced by its read caller"
          match caller with
          | .appliedView _ _ outerCaller outerLexical =>
            assertTrue (outerCaller == lexical && outerLexical == lexical) "outer read lost one of its root snapshots"
          | _ => throw (IO.userError "shared read did not preserve its active outer caller")
          let callerPosition ← match graph.table.lookupIndex? caller with
            | some (some index) => pure index | _ => throw (IO.userError "actual shared caller unavailable")
          let recipe ← match graph.recipeAt? callerPosition rootPosition read target with
            | some recipe => pure recipe | none => throw (IO.userError "actual shared paired recipe unavailable")
          let state ← match graph.table.lookup? snapshot.frame with
            | some (some state) => pure state | _ => throw (IO.userError "actual shared source state missing")
          assertTrue (state.nativeActive != state.metadata.active &&
            state.metadata.active == recipe.read.substitution && recipe.read.witnesses.isEmpty)
            "native cumulative substitution leaked into the source principal"
          callers := callers ++ [caller]
          sources := sources ++ [state.metadata.source]
        | _ => throw (IO.userError "shared allocation did not retain the paired applied-view frame")
    assertTrue (callers.length == 2 && callers.eraseDups.length == 2 && sources.eraseDups.length == 1)
      "different read callers did not preserve the shared principal's single source profile"

private def escaped {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (getOwner useOwner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named getOwner) with
    | some named => pure named | none => throw (IO.userError "paired get origin missing")
  let lexical : Frame := .named named
  for spent in [0, 41, 150000] do
    let completion ← successful prepared useOwner [.word (w 3)] 17 spent
    let ledger ← get "returned paired ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let wrapper ← match ledger.ledger.rows.find? (fun row =>
        row.entry.key.binder.name == "f" && row.entry.key.owner == useOwner) with
      | some row => pure row | none => throw (IO.userError "escaped view payload missing")
    match wrapper.payload with
    | some (.pair (.pair _ (.closure _ _ _ (readSnapshot :: original :: _))) _) =>
      assertTrue (SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame readSnapshot == some lexical)
        "escaped view sampled the application caller instead of the read-time caller"
      match original with
      | .pair (.pair _ (.closure _ _ _ (creationSnapshot :: _))) _ =>
        assertTrue (SourceCoreCallablePairedFrameCodec.decode prepared.ancestry.layout.frame creationSnapshot == some lexical)
          "escaped view lost its original lambda's creation snapshot"
      | _ => throw (IO.userError "escaped view did not retain its original native callable")
    | _ => throw (IO.userError "escaped read wrapper did not save its two values at creation")
    -- Closures capture by value: `getLocal`'s input and the returned closure's
    -- snapshot keep 3, and each application increments its own copy once.
    let seeds := (ledger.ledger.rows.filter (fun row =>
        row.entry.key.binder.name == "seed" && row.entry.key.owner == getOwner)).map (·.payload)
    assertTrue (seeds == [3, 3, 4, 4].map (fun n => some (.word (w n))))
      "escaped applications did not each restart from the returned closure's snapshot"
    let items := ledger.ledger.rows.filter (·.entry.key.binder.name == "item")
    assertTrue (items.length == 2) "escaped applications lost their source parameter allocations"
    for row in items do
      let snapshot ← get "escaped application snapshot"
        (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      match snapshot.frame with
      | .appliedView _ _ caller captured =>
        assertTrue (caller == lexical && captured == lexical) "escaped application replaced the saved read profile"
      | _ => throw (IO.userError "escaped application lacked a paired frame")
      assertTrue ((graph.table.lookup? snapshot.frame).isSome) "escaped paired snapshot lacked a prepared source profile"

private def otherFlows {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (program : CheckedProgram) : IO Unit := do
  -- Both calls of `mono`'s `f` start again from `seed = 10`; the second returns 10 + 4.
  for (name, arguments, expected) in [
      ("mono", [SourceTypedRuntime.Value.word (w 10)], 14),
      ("zero", [], 9), ("unused", [], 7), ("looping", [.word (w 4)], 6)] do
    let owner ← key program name
    for spent in [0, 37, 150000] do
      let completion ← successful prepared owner arguments expected spent
      let ledger ← get "paired simple flow ledger" (SourceCoreCallablePairedLedger.scan completion initial)
      for row in ledger.ledger.rows do
        let snapshot ← get "paired simple flow snapshot"
          (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
        assertTrue ((graph.table.lookup? snapshot.frame).isSome) s!"{name} lost an allocation metadata profile"
        if name == "zero" && row.entry.key.binder.name == "probe" then
          assertTrue (match snapshot.frame with | .lambda .. => true | _ => false)
            "zero-parameter monomorphic lambda acquired a generalized view"
        if name == "unused" && row.entry.key.binder.name == "unused" then
          assertTrue (row.payload == some .unit) "unused principal unexpectedly required a native lambda"
  -- `f` is still uninitialized when its lambda is created, so the lambda's copy
  -- of `f` is too, and the first recursive read faults.
  let recursive ← key program "recursive"
  let missing ← binder prepared recursive "f"
  for spent in [0, 37, 150000] do
    let completion ← completed prepared recursive [.word (w 4)] spent
    match completion.result.native.observation with
    | .failed reason _ =>
      assertTrue ((completion.result.diagnostics.diagnostic? reason).map (·.error) == some (.uninitializedLocal missing))
        "read of the lambda's uninitialized copy of its own local did not fault"
    | other => throw (IO.userError s!"paired recursive capture classification changed: {reprStr other}")
    let ledger ← get "paired recursive ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    for row in ledger.ledger.rows do
      let snapshot ← get "paired recursive snapshot"
        (SourceCoreCallablePairedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue ((graph.table.lookup? snapshot.frame).isSome) "recursive lost an allocation metadata profile"
  let failed ← get "paired language failure" (prepared.runSource (← key program "absent") [.word (w 3)] 150000 500)
  match failed.result.native.observation with
  | .failed reason _ =>
    assertTrue ((failed.result.diagnostics.diagnostic? reason).isSome) "paired failure lost its source diagnostic"
    assertTrue (SourceCoreCallablePairedLedger.frame? failed == some .empty) "language failure did not restore context"
    let ledger ← get "paired failure ledger" (SourceCoreCallablePairedLedger.scan failed initial)
    -- The input and the snapshot of `f` keep 3; the call's own copy keeps the
    -- body's write made before the failure.
    let seeds := (ledger.ledger.rows.filter (·.entry.key.binder.name == "seed")).map (·.payload)
    assertTrue (seeds == [3, 3, 4].map (fun n => some (.word (w n))))
      "language failure erased the call's earlier write to its copy"
  | other => throw (IO.userError s!"paired language failure classification changed: {reprStr other}")
  let pending ← get "paired nonterminating run" (prepared.runSource (← key program "spin") [] 5000 500)
  let resumed := pending.resume 5000
  for completion in [pending, resumed] do
    assertTrue (match completion.result.native.observation with | .outOfFuel .. => true | _ => false)
      "infinite source loop was reported as completion"
    let _ ← get "paired suspended ledger" (SourceCoreCallablePairedLedger.scan completion initial)
    let current ← match SourceCoreCallablePairedLedger.frame? completion with
      | some current => pure current | none => throw (IO.userError "suspended paired frame missing")
    assertTrue ((graph.table.lookup? current).isSome) "suspended callable lost its prepared metadata profile"

def run : IO Unit := do
  let program ← get "paired source checker" (checkProgram workspace)
  let names := ["sharedHistory", "getLocal", "useReturned", "mono", "zero", "recursive", "unused", "looping", "absent", "spin"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"paired worklist failed: {reprStr other}")
  let automatic ← get "paired compatible base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "paired two-pass compiler" (SourceCoreCallablePairedPrograms.prepare automatic.prepared 500)
  let graph ← get "paired reached metadata" (SourceCoreCallableAncestryPairedPreparation.prepare prepared.base)
  assertTrue (prepared.entries.length == keys.length) "paired root inventory changed"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "paired administrative suffix changed the original catalog"
  assertTrue (!prepared.layouts.entries.isEmpty) "paired compilation emitted no source markers"
  shared prepared graph (← key program "sharedHistory")
  escaped prepared graph (← key program "getLocal") (← key program "useReturned")
  otherFlows prepared graph program
  IO.println "actual paired callable frames: saved read/lexical parents, shared source profiles, escaped captures and typed resume GREEN"

end Tests.SourceCoreCallablePairedPrograms
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePrincipals
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Context.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Principal.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Entry.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Table.mk

/-! Actual checked artifacts retain unused direct lambda principals, including
empty native bundles, for-header lets and nested qualified contexts. This tests
compile-time metadata and allocation-key compatibility, not heap decoding,
emitted closure authentication, or dynamic view ancestry. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePrincipals
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallablePrincipals

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function unusedMono() returns (Word) { let mono: WordFunction = lam(item: Word) -> Word { return item; }; return 1; }",
    "function unusedPoly() returns (Word) { let unused = lam(item) { return item; }; return 2; }",
    "function header() returns (Word) { for (let headerLambda: WordFunction = lam(item: Word) -> Word { return item; }; false; ) {} return 3; }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); };",
    " let untouched = lam(other) { return other; }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function enclosing<T>(value: T) returns (T) where T: Mark { let ignored = lam(item) { return item; }; return keep(value); }",
    "function reachable(flag: Bool) returns (Word, Bool) { return (enclosing(1), enclosing(flag)); }"
  ]}] }

private def prepareBase (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let requests ← ["unusedMono", "unusedPoly", "header", "nested", "reachable"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | _ => throw (IO.userError s!"principal fixture missing {name}")
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"principal worklist failed: {reprStr result}")
  get "compatible principal artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    {context : Context program plan parents} (principal : Principal context) :
    SourceCoreAllocationContexts.BinderOrigin context.compilerSource principal.binder := principal.allocation_origin

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (table : Table program plan parents) (origin : Origin plan parents)
    (member : origin ∈ origins plan parents) {declaration : Declaration}
    (declared : declaration ∈ directDeclarations (originKey origin).originalSource) :
    ∃ entry ∈ table.entries,
      entry.metadata.owner = origin.owner ∧ entry.metadata.active = origin.active ∧
      entry.metadata.originalSource = (originKey origin).originalSource ∧
      entry.metadata.inherited = (originKey origin).inherited ∧
      entry.metadata.originalDeclaration = declaration :=
  table.origin_declaration_retained origin member declared

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (entry : Entry program plan parents) {key : SourceCoreAllocationLayouts.Key}
    (matching : entry.matchesLayout key) :
    SourceCoreAllocationContexts.BinderOrigin entry.context.compilerSource key.binder :=
  entry.layout_binder_origin matching

private def checkEntry {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (table : Table program plan parents) (entry : Entry program plan parents) : IO Unit := do
  let context := entry.context
  let principal := entry.principal
  assertTrue (decide (context.compilerSource = context.originalSource.applySubstitution context.active))
    "compiler source was replaced by the runtime requirement view"
  assertTrue (decide (context.source = SourceTypedRuntime.rewriteLocalRequirements context.inherited
    (context.originalSource.applySubstitution context.active))) "principal recipe changed"
  assertTrue (decide (principal.binder = principal.declaration.binder.applySubstitution context.active))
    "canonical allocation binder erased raw metadata"
  assertTrue (principal.binder.id.owner == context.owner.declaration && context.source.owner == context.owner.declaration)
    "principal owner metadata changed"
  assertTrue ((table.find? context.owner context.active principal.binder.id).isSome)
    "principal lookup lost a retained declaration"
  match insert [entry] entry with
  | .ok rows => assertTrue (rows.length == 1) "identical principal was duplicated"
  | .error error => throw (IO.userError s!"identical principal rejected: {reprStr error}")
  let wrongBinder := {principal.binder with name := principal.binder.name ++ "tampered"}
  let fakeKey : SourceCoreAllocationLayouts.Key :=
    ⟨context.owner, context.active, wrongBinder, [], .unit, true⟩
  assertTrue ((table.forLayout? fakeKey).isNone) "layout matched only a binder ID instead of full metadata"

private def checkLayouts {checked : Checked} (base : SourceCoreCompatibleFunctions.Prepared checked)
    (table : Table base.sourceProgram base.plan base.contexts) : IO Unit := do
  let marked ← get "marked principals" (SourceCoreCompatibleMarkedFunctions.prepare base 512)
  let relevant := marked.layouts.entries.filter fun layout =>
    ["mono", "unused", "outer", "inner", "untouched", "ignored", "headerLambda"].contains layout.key.binder.name
  assertTrue (!relevant.isEmpty) "no actual principal allocation layouts found"
  for layout in relevant do
    let entry ← match table.forLayout? layout.key with
      | some entry => pure entry
      | none => throw (IO.userError s!"real layout lost principal metadata: {reprStr layout.key}")
    assertTrue (decide (entry.principal.binder = layout.key.binder) &&
      decide (entry.context.active = layout.key.active) && decide (entry.context.owner = layout.key.owner))
      "actual layout matched a different principal context"
  let unused := relevant.filter (·.key.binder.name == "unused")
  assertTrue (unused.length == 1 && unused.all (fun layout => layout.key.payloadType == .unit))
    "unused generalized declaration did not keep its empty native bundle"

def run : IO Unit := do
  let program ← get "principal checker" (checkProgram workspace)
  let artifact ← prepareBase program
  let base := artifact.prepared
  let table ← get "principal inventory" (prepare base)
  for entry in table.entries do checkEntry table entry
  let named := fun name => table.entries.filter (·.principal.binder.name == name)
  assertTrue ((named "mono").length == 1 && (named "mono").all (fun entry => entry.principal.binder.scheme.quantified.isEmpty))
    "unused monomorphic principal was omitted"
  assertTrue ((named "unused").length == 1 && (named "unused").all (fun entry => !entry.principal.binder.scheme.quantified.isEmpty))
    "unused generalized principal was omitted"
  assertTrue ((named "headerLambda").length == 1) "for-header lambda declaration was omitted"
  let nested := (named "untouched").filter (fun entry => !entry.context.active.isEmpty)
  assertTrue (nested.length ≥ 2 && (nested.map (·.context.active)).eraseDups.length ≥ 2)
    "unused nested principal lost distinct full parent contexts"
  assertTrue (nested.any (fun entry => !entry.context.inherited.isEmpty))
    "qualified parent witnesses were not retained"
  assertTrue ((named "ignored").length == 2 && (named "ignored").all (fun entry => !entry.context.evidence.isEmpty))
    "actual specialized caller evidence was not retained"
  assertTrue ((table.entries.map (·.key)).length == (table.entries.map (·.key)).eraseDups.length)
    "principal keys were duplicated"
  checkLayouts base table
  IO.println "unused mono/poly/for principal metadata, parent contexts/evidence, exact allocation keys GREEN"
end Tests.SourceCoreCallablePrincipals
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableRuntimeBodyKernel
/-! The shared kernel consumes the original source/native grade and retains
an arbitrary protected entry. Concrete builtin leaves close both consumers
without an external execution law. A lambda receipt supplies the same static
fields at its original dictionary; no Code or source-attribution cast is used.
Runtime IO is provided by the existing operator suites. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableRuntimeBodyKernel
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload

abbrev finite_source := @CallableRuntimeBodyKernel.BodyFor.preserves_sized
abbrev finite_native := @CallableRuntimeBodyKernel.BodyFor.reflects_sized
abbrev old_body := @CallablePreparedMethodRuntimeMeaning.Body.mk

section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {output : Ty} {code : Expr} {fellThrough escaped : Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallablePreparedMethodRuntimeMeaning.Body layouts owner active frameLayout globals onError values function expressionSyntax readFuel solved reasonAt
    ambient administrative context scope output code fellThrough escaped registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)

variable {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry) (binders : ProtectedExpressionMeaning.Binds entry)

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault transport binders in
theorem closed_source [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      entry scope finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults entry) := by
    intro context valid child _
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child
  exact body.toKernel.preserves_sized functions definitions registered extension program faithful observations escapedFault
    transport binders (fun valid extended => valid.extend extended) (fun valid => valid)
    budget size within expressions environments heaps locals agrees typed reference read unmapped installed trace

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault transport binders in
theorem closed_native [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      entry scope finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults entry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime uninitialized missing)) budget
  exact body.toKernel.reflects_sized functions definitions registered extension program faithful observations functionTypes escapedFault
    transport binders (fun valid extended => valid.extend extended) (fun valid => valid)
    budget size within expressions environments heaps locals agrees typed reference read unmapped installed evaluated

theorem same_tree : body.toKernel.flow = body.flow ∧ HEq body.toKernel.tree body.tree ∧
    HEq body.toKernel.sites body.sites := ⟨rfl, HEq.rfl, HEq.rfl⟩

theorem full_runtime : body.toKernel.initialValid.ledger = body.valid.ledger ∧
    body.toKernel.initialValid.runtime = body.valid.runtime ∧
    body.toKernel.initialValid.covers = body.valid.covers := ⟨rfl, rfl, rfl⟩

/-- This existing dictionary transport is only the concrete builtin family. -/
theorem builtin_evidence (dictionary : Dynamic.EvidenceEnvironment) (covers : dictionary.Covers context) :
    (body.with_evidence dictionary covers).toKernel.flow = body.flow ∧
    HEq (body.with_evidence dictionary covers).toKernel.tree body.tree := ⟨rfl, HEq.rfl⟩
end Concrete

section Lambda
variable {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : CallableIndexedLambdaValues.Code prepared function scope administrative}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Actual/canonical source transport remains in BodyWith; the kernel consumes
only its already established canonical static fields at the same dictionary. -/
theorem lambda_fields
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults) :
    ∃ kernel : CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (expressionSyntax function.source) (certificates body.readFuel function.source)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared) administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults,
      kernel.flow = body.flow ∧ HEq kernel.tree body.tree ∧ HEq kernel.sites body.sites := by
  exact ⟨{
    flow := body.flow
    tree := body.tree
    sites := body.sites
    initialValid := body.valid
    projection := body.projection
    unique := body.unique
    emitted := body.emitted }, rfl, HEq.rfl, HEq.rfl⟩
end Lambda

-- A family indexed by its dictionary has no general Covers-only reindex API.
#check_failure CallableRuntimeBodyKernel.BodyFor.with_evidence

end Tests.SourceCoreCallableRuntimeBodyKernel
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableRuntimeBodyMutualMeaning
/-! Concrete builtin certificates close both neutral body contracts. The family
may contain different actual sources, dictionaries, code, and protected entries.
The named adapter retains the original source/native child grades and state.
This formal test adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableRuntimeBodyMutualMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins

abbrev source_family := @CallableRuntimeBodyMutualMeaning.preserves_at
abbrev native_family := @CallableRuntimeBodyMutualMeaning.reflects_at
abbrev named_source := @RecursiveNamedCatalogMutualMeaning.preserves_at_with_family
abbrev named_native := @RecursiveNamedCatalogMutualMeaning.reflects_at_with_family
abbrev actual_named_entry := @RecursiveNamedCatalogMutualMeaning.NamedFamily.entry

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} (origins : ι → Origin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (readFuel : ι → Nat) (reasonAt : ι → ExpressionId → Word)
  (certificates : ∀ i context, (origins i).certificates context =
    CompatibleExpressionBuiltinRuntime.Certificate (readFuel i) values (origins i).function.source context
      (origins i).solved (reasonAt i))
  (uninitialized : ∀ i id location, faults (.uninitializedLocation location) ((reasonAt i) id))
  (missing : ∀ i id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((reasonAt i) id).add tag))

include extension faithful observations functionTypes certificates uninitialized missing in
/-- The only semantic children come from the actual builtin certificate family. -/
theorem closed_builtin_preserves [FunctionCalls.FaultTokens faults] (size : Nat) : ∀ i, PreservesAt functions program (origins i) size := by
  apply CallableRuntimeBodyMutualMeaning.preserves_at origins functions extension program faithful observations
  intro i context valid budget child within _
  rw [certificates i context]
  have runtime := (origins i).runtimeOf valid
  intro scope id lowered
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed (origins i).protectedEntry
      (CompatibleExpressionBuiltinRuntime.preserves (fuel := readFuel i) (source := (origins i).function.source) functions extension faithful observations functionTypes
        program (origins i).function.evidence runtime.ledger runtime.runtime (origins i).body.unique
        (uninitialized i) (missing i))) child (scope := scope) (id := id) (lowered := lowered)

include extension faithful observations functionTypes certificates uninitialized missing in
/-- Reflection starts from each original native completion and returns an
independent source grade and the full retained entry. -/
theorem closed_builtin_reflects [FunctionCalls.FaultTokens faults] (size : Nat) : ∀ i, ReflectsAt functions program (origins i) size := by
  apply CallableRuntimeBodyMutualMeaning.reflects_at origins functions extension program faithful observations functionTypes
  intro i context valid budget child within _
  rw [certificates i context]
  have runtime := (origins i).runtimeOf valid
  intro scope id lowered
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed (origins i).protectedEntry
      (CompatibleExpressionBuiltinRuntime.reflects (fuel := readFuel i) (source := (origins i).function.source) functions extension faithful observations functionTypes
        program (origins i).function.evidence runtime.ledger runtime.runtime (uninitialized i) (missing i))) child (scope := scope) (id := id) (lowered := lowered)

/-- Selection keeps the strict original callee grade; it does not rebuild it. -/
theorem original_native_child {budget child : Nat} (strict : child < budget)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget (ReflectsAt functions program (origins i)))
    (i : ι) : ReflectsAt functions program (origins i) child := below i child strict

/-- Source and native budgets are independent interfaces. -/
theorem original_source_child {budget child : Nat} (strict : child < budget)
    (below : ∀ i, RecursiveNamedBoundedContracts.Below budget (PreservesAt functions program (origins i)))
    (i : ι) : PreservesAt functions program (origins i) child := below i child strict

/-- Static nesting rank is not a premise of either native or source decrease. -/
theorem equal_grade_not_strict (size : Nat) : ¬ size < size := Nat.lt_irrefl size

end Tests.SourceCoreCallableRuntimeBodyMutualMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableSharedHistory
set_option autoImplicit false
namespace Tests.SourceCoreCallableSharedHistory
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) { let shared = lam(item) { let probe: Word = 0; return item; }; let outer = lam(value) { keep(value); return shared(value); }; return outer(seed); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"shared ancestry fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let owner ← key program "sharedHistory"
  let plan ← match SourceSpecializationWorklist.run program [⟨owner.declaration, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"shared ancestry worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"shared ancestry base failed: {reprStr error}")
private def initial : SourceCoreAllocationLedger.SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

/-- Ground instances discovered under a read-parent are compiled at the
original lexical bundle-creation scope. Closures capture by value, so that scope
is the snapshot taken around the bundle's declaration. This is a positive
compiler regression; it does not claim the scoped single-parent ancestry table
covers this case. -/
def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"shared source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"shared compiler failed: {reprStr error}")
  for fuel in [0, 31, 100000] do
    let completion ← match prepared.runSource (← key program "sharedHistory") [.word (w 3)] fuel 500 with
      | .ok completion => pure (completion.resume 100000)
      | .error error => throw (IO.userError s!"shared native run failed: {reprStr error}")
    match completion.result.native.observation with
    | .succeeded (.word result) _ => assertTrue (result == w 3) "shared bundle candidate changed execution"
    | other => throw (IO.userError s!"shared bundle did not complete: {reprStr other}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"shared ledger failed: {reprStr error}")
    for name in ["shared", "item", "probe"] do
      assertTrue (ledger.ledger.rows.any (·.entry.key.binder.name == name)) s!"shared source allocation {name} disappeared"
    let shared ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some shared => pure shared | none => throw (IO.userError "shared bundle marker missing")
    assertTrue (shared.environment.map Prod.fst == shared.entry.key.scope.map Prod.fst)
      "read-parent preparation changed source lexical capture order"
    assertTrue (shared.environment.length == 1) "shared bundle captured a read-parent parameter"
    let capturedSeed ← match shared.environment.head? with
      | some binding => pure binding | none => throw (IO.userError "shared bundle dropped lexical seed capture")
    -- The snapshot around the declaration copies `seed` after the input and
    -- right before the bundle's own allocation.
    let [input, seed] := (ledger.ledger.rows.takeWhile (·.entry.key.binder.name != "shared")).filter
        (·.entry.key.binder.name == "seed")
      | throw (IO.userError "shared seed allocation or its snapshot missing")
    assertTrue (capturedSeed.1 == seed.entry.key.binder.id && capturedSeed.2 == seed.sourceLocation &&
        seed.payload == input.payload)
      "shared bundle selected the read parent's environment instead of its creation snapshot"
    assertTrue (SourceCoreCallableAncestryLedger.frame? completion == some .empty)
      "shared bundle left an active callable frame"
  IO.println "root-created generic bundle: authenticated read-parent recipe, lexical captures and typed Core resume GREEN"

/-- Read-only regression audit for a root-created generalized lambda invoked
inside another generalized lambda. An unavailable transition is reported as
false; this audit is separate from the read-wrapper authentication contract. -/
def auditShared : IO Bool := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"shared ancestry source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"shared ancestry compiler failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPreparation.prepare automatic.prepared with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"shared ancestry graph failed: {reprStr error}")
  let completion ← match prepared.runSource (← key program "sharedHistory") [.word (w 3)] 100000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"shared ancestry native run failed: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word result) _ => assertTrue (result == w 3) "shared ancestry changed execution"
  | other => throw (IO.userError s!"shared ancestry did not complete: {reprStr other}")
  let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"shared ancestry ledger failed: {reprStr error}")
  let mut available := true
  for row in ledger.ledger.rows do
    let snapshot ← match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot | .error error => throw (IO.userError s!"shared allocation snapshot failed: {reprStr error}")
    let state := (graph.table.lookup? snapshot.frame).map (·.map fun state => (state.owner, state.active))
    IO.println s!"shared ancestry allocation {row.entry.key.binder.name}: frame={reprStr snapshot.frame}, state={reprStr state}"
    if row.entry.key.binder.name == "probe" then available := state.isSome
  let current ← match SourceCoreCallableAncestryLedger.frame? completion with
    | some current => pure current | none => throw (IO.userError "shared ancestry final frame missing")
  assertTrue (graph.table.lookup? current == some none) "shared ancestry failed to restore empty current frame"
  IO.println s!"root-created shared lambda's nested read transition available: {available}"
  pure available

end Tests.SourceCoreCallableSharedHistory
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableViewWrappers
/-! Exact view manifests preserve native identity/contract words and execute
the original closure against the live shared store. Parser tests intentionally
separate structural recognition from external source/view ownership. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableViewWrappers
open Solcore Solcore.Core Solcore.Frontend.SourceCoreCallableViewWrappers
open Solcore.SourceSemantics.CoreLowering.CallableViewWrappers

private def w (value : Nat) : Word := Word.ofNatModulo value
private def identity : Value := .inRight .unit (.word (w 7))
private def parameter : Ty := .word
private def result : Ty := .word
private def contract : Word := w 11
private def view : Word := w 42
private def carrierType : Ty := CallableContract.functionType parameter result

private def code : Expr :=
  .letE (.storeCell (.var 1) (.var 0))
    (LanguageResult.success (.loadCell (.var 2)))
private def captured : Environment := [.cellRef .word 0]
private def payload : Value := .closure parameter (LanguageResult.resultType result) code captured
private def original : Value := originalValue identity payload contract
private def outer : Environment := [.cellRef .word 0, .closure .unit .unit .unit []]
private def wrapped : Value := wrappedValue parameter result view identity payload contract outer
private def before : Store := [.word (w 5)]
private def after : Store := [.word (w 9)]

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def runExpected (label : String) (expression : Expr) (environment : Environment)
    (store : Store) (value : Value) (finalStore : Store) : IO Unit :=
  match runStateful 500 (.initial expression environment store) with
  | .done actual actualStore =>
    assertTrue (decide (actual = value ∧ actualStore = finalStore)) s!"{label}: {reprStr actual}, {reprStr actualStore}"
  | result => throw (IO.userError s!"{label}: {reprStr result}")

private def rejects (label : String) (value : Value) : IO Unit :=
  assertTrue (parse? parameter result value).isNone s!"{label}: malformed wrapper accepted"

def run : IO Unit := do
  let decoded ← match parse? parameter result wrapped with
    | some parsed => pure parsed | none => throw (IO.userError "actual wrapper did not parse")
  assertTrue (decide (decoded.view = view ∧ decoded.original = original ∧ decoded.outer = outer))
    "parser lost exact original carrier or captured outer environment"
  assertTrue (decide (decoded.identity = identity ∧ decoded.contract = contract)) "parser changed copied tags"
  runExpected "successful read builds only a value"
    (lower parameter result view (LanguageResult.success (.var 0))) [original] before
    (.inRight .word (wrappedValue parameter result view identity payload contract [original])) before
  runExpected "read failure skips wrapper creation"
    (lower parameter result view (LanguageResult.failure carrierType (.word (w 19)))) [] before
    (.inLeft carrierType (.word (w 19))) before
  runExpected "wrapper invokes original code with the live captured cell"
    invoke [wrapped, .word (w 9)] before (.inRight .word (.word (w 9))) after
  runExpected "descriptor projection is unchanged" (.second (.var 0)) [wrapped] before (.word contract) before
  runExpected "identity projection is unchanged" (.first (.first (.var 0))) [wrapped] before identity before
  let failureCode := .letE (.storeCell (.var 1) (.var 0))
    (LanguageResult.failure .word (.word (w 23)))
  let failurePayload := .closure .word (LanguageResult.resultType .word) failureCode captured
  runExpected "language failure preserves original prefix write"
    invoke [wrappedValue .word .word view identity failurePayload contract outer, .word (w 9)] before
    (.inLeft .word (.word (w 23))) after
  let other := wrappedValue parameter result (w 99) identity payload (w 123) []
  runExpected "different views and descriptors preserve named equality"
    CallableContract.equalBody [other, wrapped] before (.bool true) before
  let anonymous := wrappedValue parameter result view (.inLeft .word .unit) payload contract outer
  runExpected "anonymous self equality remains false" CallableContract.equalBody [anonymous, anonymous]
    before (.bool false) before
  runExpected "existing descriptor stage rejection is unchanged"
    (CallableContract.dispatch [⟨contract, some (w 29), none⟩] .beforeArguments (w 31) (.second (.var 0)))
    [wrapped] before (.inLeft .unit (.word (w 29))) before
  let closure := .closure parameter (LanguageResult.resultType result) (body view) (original :: outer)
  rejects "changed copied identity" (.pair (.pair (.inRight .unit (.word (w 8))) closure) (.word contract))
  rejects "changed copied descriptor" (.pair (.pair identity closure) (.word (w 12)))
  rejects "wrong parameter annotation" (.pair (.pair identity
    (.closure .bool (LanguageResult.resultType result) (body view) (original :: outer))) (.word contract))
  rejects "wrong result annotation" (.pair (.pair identity
    (.closure parameter .word (body view) (original :: outer))) (.word contract))
  rejects "changed capture projection" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result)
      (.letE (.word view) (.apply (.second (.first (.var 3))) (.var 1))) (original :: outer))) (.word contract))
  rejects "empty captured environment" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result) (body view) [])) (.word contract))
  rejects "noncarrier captured original" (.pair (.pair identity
    (.closure parameter (LanguageResult.resultType result) (body view) (.unit :: outer))) (.word contract))
  let differentView := wrappedValue parameter result (w 44) identity payload contract outer
  let parsed ← match parse? parameter result differentView with
    | some parsed => pure parsed | none => throw (IO.userError "another structural manifest failed to parse")
  assertTrue (decide (parsed.view = w 44)) "parser must leave source view ownership to caller"
  assertTrue (Word.ofNat? wordModulus).isNone "out-of-range view IDs must not wrap"

private theorem code_typed : HasType [.word, .cell .word] code (LanguageResult.resultType .word) :=
  .letE (.storeCell (.var rfl) (.var rfl)) (.inRight .word (.loadCell (.var rfl)))

example : HasType [carrierType] (lower parameter result view (LanguageResult.success (.var 0)))
    (LanguageResult.resultType carrierType) := lower_hasType view .word .word (.inRight .word (.var rfl))

private theorem original_typed : RuntimeValueHasType [.word] original carrierType :=
  .pair (.pair (.inRight .word) (.closure (.cons (.cellRef rfl) .nil) code_typed)) .word

example : RuntimeValueHasType [.word] wrapped carrierType :=
  wrapped_runtime_typed view original_typed
    (.cons (.cellRef rfl) (.cons (.closure .nil .unit) .nil))

private theorem writes : Evaluates (.word (w 9) :: captured) before code
    (.inRight .word (.word (w 9))) after :=
  .letE (.storeCell (.var rfl) rfl (.var rfl) rfl) (.inRight (.loadCell (.var rfl) rfl))

example : Evaluates [wrapped, .word (w 9)] before invoke (.inRight .word (.word (w 9))) after :=
  invoke_evaluates view writes

example {value : Value} {finalStore : Store}
    (completed : ∃ fuel, runStateful fuel (.initial invoke [wrapped, .word (w 9)] before) = .done value finalStore) :
    Evaluates (.word (w 9) :: captured) before code value finalStore :=
  invoke_run_done_iff.mp completed

end Tests.SourceCoreCallableViewWrappers
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableViews
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableViews.Principal.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.View.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.Table.mk
#check_failure Solcore.Frontend.SourceCoreCallableViews.Entry.mk

/-! Actual compatible artifacts retain occurrence-specific local wrapper
metadata, including empty monomorphic views, distinct qualified witnesses and
nested cumulative contexts. This is static inventory, not closure export. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableViews
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallableViews
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function mono() returns (WordFunction) { let f: WordFunction = lam(item: Word) -> Word { return item; }; return f; }",
    "function repeated(flag: Bool) returns (Word, Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(2), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function nestedMono(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let f: WordFunction = lam(item: Word) -> Word { return item; }; return f(1); };",
    " return (outer(1), outer(flag)); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"callable views fixture missing: {name}")

private def artifact (program : CheckedProgram) (name : String) : IO SourceCoreCompatibleFunctions.Automatic := do
  let owner ← key program name
  let plan ← match SourceSpecializationWorklist.run program [⟨owner.declaration, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"callable views worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"callable views compatible artifact failed: {reprStr error}")

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.cumulative = view.ownSubstitution.compose view.parentActive := view.cumulativeExact

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.reference.witnesses = view.ownWitnesses := view.witnessesExact

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCoreLocalEvidence.authenticateReference program plan
      { caller := view.principal.owner, source := view.principal.originalSource,
        binder := view.principal.binder, initializer := view.principal.initializer, instances := [] }
      view.parent view.read = .ok view.reference := view.authenticatedReference

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    view.principal.source = SourceTypedRuntime.rewriteLocalRequirements view.inheritedWitnesses
      (view.principal.originalSource.applySubstitution view.parentActive) := view.exactPrincipalSource

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    ∃ node, view.principal.source.lookupExpression? view.principal.initializer = some node ∧
      node.form = .lambda view.principal.parameters view.principal.resultType view.principal.body :=
  view.principal.lambdaMetadata

example {program : CheckedProgram} {plan : Plan} (view : View program plan) :
    SourceCompilationPlan.localRequirementWitnesses view.compilerCaller view.principal.evidence
      (view.principal.binder.applySubstitution view.parentActive) view.rawRead =
      .ok (view.ownSubstitution, view.ownWitnesses) := view.exactFactory

private def table {checked : Checked} (prepared : Prepared checked) : IO (Table prepared.sourceProgram prepared.plan) :=
  match prepare prepared with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"callable views inventory rejected: {reprStr error}")

private def checks {checked : Checked} (prepared : Prepared checked) (table : Table prepared.sourceProgram prepared.plan) : IO Unit := do
  assertTrue (!table.entries.isEmpty) "callable view inventory unexpectedly empty"
  for entry in table.entries do
    let view := entry.view
    assertTrue (view.read.occurrence.owner == view.owner.declaration && view.principal.source.owner == view.owner.declaration)
      "callable view lost actual occurrence ownership"
    assertTrue (view.principal.source == SourceTypedRuntime.rewriteLocalRequirements view.inheritedWitnesses
      (view.principal.originalSource.applySubstitution view.parentActive)) "principal source used the compiler ledger instead of the runtime source metadata"
    assertTrue (view.compilerCaller.function.typedBody == view.principal.originalSource.applySubstitution view.parentActive)
      "compiler caller used occurrence wrapper substitution as parent context"
    assertTrue (view.wrapsPrincipal == !view.binding.binder.scheme.quantified.isEmpty)
      "monomorphic/generated wrapper decision changed"
    assertTrue ((table.viewAt? view.owner view.read view.parentActive).map (·.id) == some entry.id &&
      (table.entryAt? entry.id).map (·.id) == some entry.id) "callable view lookup/id changed"
    assertTrue (view.reference.witnesses.length == view.ownWitnesses.length)
      "view lost own occurrence witnesses"
    if view.wrapsPrincipal then
      let selected ← match view.selectedInstance with
        | some selected => pure selected | none => throw (IO.userError "wrapped read has no actual compiled local candidate")
      assertTrue (selected.origin.substitution == view.cumulative && selected.origin.initializer == view.principal.initializer)
        "read selected a candidate by final type rather than full cumulative context"
    else
      assertTrue (view.ownSubstitution.isEmpty && view.ownWitnesses.isEmpty && view.selectedInstance.isNone)
        "monomorphic principal unexpectedly acquired wrapper metadata"
  match prepare prepared {} 0 with
  | .error .zeroFirstId => pure () | _ => throw (IO.userError "zero callable view ID accepted")
  match prepare prepared {} (2 ^ 256) with
  | .error (.idSpaceExhausted _) => pure () | _ => throw (IO.userError "callable view Word ID wrapped")
  match prepare prepared {maxViews := 0} with
  | .error (.viewBudgetExhausted 0) => pure () | _ => throw (IO.userError "callable view count budget ignored")
  match prepare prepared {maxSourceNodes := 0} with
  | .error (.sourceNodeBudgetExhausted 0) => pure () | _ => throw (IO.userError "callable view source inventory budget ignored")

private def checkAuthenticationErrors {checked : Checked} (prepared : Prepared checked)
    (table : Table prepared.sourceProgram prepared.plan) : IO Unit := do
  let view ← match table.entries.head? with
    | some entry => pure entry.view | none => throw (IO.userError "callable view tamper fixture empty")
  let other ← key prepared.sourceProgram "keep"
  let foreign := {view.read with occurrence := {view.read.occurrence with owner := other.declaration}}
  match authenticate prepared.sourceProgram prepared.plan view.binding view.parent foreign with
  | .error _ => pure () | .ok _ => throw (IO.userError "foreign occurrence accepted as local view")
  let altered := {view.binding with initializer := foreign}
  match authenticate prepared.sourceProgram prepared.plan altered view.parent view.read with
  | .error (.evidence (.bindingMismatch _)) => pure ()
  | _ => throw (IO.userError "altered principal initializer accepted")
  let duplicateSource := {view.binding.source with nodes := view.binding.source.nodes ++ view.binding.source.nodes}
  let duplicate := {view.binding with source := duplicateSource}
  match authenticate prepared.sourceProgram prepared.plan duplicate view.parent view.read with
  | .error (.evidence (.originMismatch _)) => pure ()
  | _ => throw (IO.userError "duplicate foreign source table accepted")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"callable views source rejected: {reprStr error}")
  let mono ← artifact program "mono"
  let monoTable ← table mono.prepared
  checks mono.prepared monoTable
  checkAuthenticationErrors mono.prepared monoTable
  assertTrue (monoTable.entries.length == 1 && monoTable.entries.all (fun entry => !entry.view.wrapsPrincipal))
    "monomorphic direct lambda metadata missing or wrapped"
  let repeated ← artifact program "repeated"
  let repeatedTable ← table repeated.prepared
  checks repeated.prepared repeatedTable
  let f := repeatedTable.entries.filter (fun entry => entry.view.binding.binder.name == "f")
  assertTrue (f.length == 3 && f.all (fun entry => entry.view.parentActive.isEmpty && entry.view.ownWitnesses.length == 1))
    "same-type repeated reads lost occurrence-specific witnesses"
  let actualRequirements := f.flatMap (fun entry => entry.view.ownWitnesses.map (·.actualRequirement))
  assertTrue (actualRequirements.eraseDups.length == 3) "qualified read requirements merged by principal/type"
  let nested ← artifact program "nested"
  let nestedTable ← table nested.prepared
  match prepare nested.prepared {maxContexts := 0} with
  | .error (.contextBudgetExhausted 0) => pure ()
  | _ => throw (IO.userError "local context inventory budget ignored")
  checks nested.prepared nestedTable
  let inner := nestedTable.entries.filter (fun entry => entry.view.binding.binder.name == "inner")
  assertTrue (inner.length == 2 && inner.all (fun entry => !entry.view.parentActive.isEmpty &&
    !entry.view.ownSubstitution.isEmpty && entry.view.cumulative != entry.view.ownSubstitution))
    "nested parent active context collapsed into own wrapper substitution"
  assertTrue ((inner.map (fun entry => entry.view.parentActive)).eraseDups.length == 2)
    "equal inner result types erased distinct enclosing contexts"
  let nestedMono ← artifact program "nestedMono"
  let nestedMonoTable ← table nestedMono.prepared
  checks nestedMono.prepared nestedMonoTable
  let nestedF := nestedMonoTable.entries.filter (fun entry => entry.view.binding.binder.name == "f")
  assertTrue (nestedF.length == 2 && nestedF.all (fun entry => !entry.view.wrapsPrincipal &&
    !entry.view.parentActive.isEmpty && entry.view.ownSubstitution.isEmpty)) "nested monomorphic closure lost parent metadata"
  IO.println "static callable views, exact witnesses/principal sources, mono/nested context and rejection GREEN"
end Tests.SourceCoreCallableViews
end
