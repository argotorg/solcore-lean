import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Guarded equal assignments need no nonexistent operand diagnostic. Concrete
named expression Trees close both child interfaces while the returned Entry,
actual seven slots, world and effect prefix remain explicit. Actual named RHS
calls below verify the empty table, failure priority, source metadata and resume.
Whole statement Errors and unrelated fault interpretations remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedAssignmentReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open NamedAssignmentHeads CompatibleEquality CompatibleHeap CoreProof

/-- Exact decoding of an empty assignment table supplies the reachable law. -/
theorem empty_table_equal_law :
    AssignmentOperandDiagnostics.OperandsLaw
      (GenericAssignmentDiagnostics.OperandRep ⟨[]⟩) .equal Word.zero :=
  AssignmentOperandDiagnostics.equal _ _

/-- The old unconditional token premise cannot be fabricated from that table. -/
theorem empty_table_has_no_operand (operator : Syntax.ValueAssignOp) (token : Word) :
    ¬ GenericAssignmentDiagnostics.OperandRep ⟨[]⟩ (.invalidAssignmentOperands operator) token := by
  rintro ⟨diagnostic, rawType, decoded, error⟩
  cases decoded

section Static
variable {checked : CallableAncestryPairedLookup.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {source : TypedSource} {program : SourceSemantics.Program}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions assignment .equal rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (runtimeViews : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem equal_named_preserves_fault
    (placeMissing : ∀ {root resolved reason token count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
    (placeUninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target .equal rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentHeads.preserves_fault_reachable functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing (GenericAssignmentStatements.Head.ReachableErrors.equal placeMissing placeUninitialized) trace next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem equal_named_reflects
    (placeMissing : ∀ {root resolved reason token count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
    (placeUninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target .equal rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :=
  NamedAssignmentHeads.reflects_reachable functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing (GenericAssignmentStatements.Head.ReachableErrors.equal placeMissing placeUninitialized) completed

end Static

open Tests.SourceCompilerFeatureSupport in
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function first(value: Word) returns (Word) { let copied = value; return copied; }",
    "function bad(value: Word) returns (Word) { let copied = value; let gap: Word; return gap; }",
    "function equalNamed(seed: Word) returns (Word) { let root: Word; root = first(seed); return first(root); }",
    "function compoundNamed(seed: Word) returns (Word) { let root: Word; root += first(seed); return first(99); }",
    "function equalRhsFault(seed: Word) returns (Word) { let root: Word; root = bad(seed); return first(99); }",
    "function compoundRhsFault(seed: Word) returns (Word) { let root: Word; root += bad(seed); return first(99); }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) (name : String) : IO TypedSource := do
  let key ← match entry.cached.sourceProgram.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceSpecialization.SpecializationKey.mk signature.id [])
    | _ => throw (IO.userError s!"missing checked function {name}")
  let exact ← get "actual specialized source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan key)
  pure exact.function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def failure (entry : Entry) (expected : SourceCoreFaultSites.Diagnostic)
    (expectedCells : List (TypeSystem.Ty × Option SourceCoreExecution.Value)) : IO Unit := do
  let invocation ← entry.invoke [scalar 7]
  let token ← match invocation.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "expected a guarded language failure")
  require (token != Word.zero && decide ((← invocation.diagnostic token) = some expected))
    "guarded failure lost the exact decoded diagnostic"
  entry.checkCells [scalar 7] expectedCells
  let complete ← entry.audit [scalar 7]
  match complete.observation with
  | .fault error _ => require (decide (error = expected.error)) "guarded failure priority changed"
  | _ => throw (IO.userError "native source observation lost the failure")
  for fuel in [0, 7, 43] do
    let pending ← entry.audit [scalar 7] fuel
    let resumed ← get "native guarded resume" (pending.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation complete))
      "guarded resume changed the failure or actual store prefix"
    let pending ← entry.invoke [scalar 7] {executionOptions with executionFuel := fuel}
    match pending.outcome with
    | .outOfFuel checkpoint =>
      match ← checkpoint.resume 300000 1024 with
      | .failed resumedToken session =>
        let diagnostic ← get "resumed guarded diagnostic" (session.diagnostic entry.key resumedToken)
        require (resumedToken == token && decide (diagnostic = some expected))
          "public guarded resume changed the diagnostic"
      | _ => throw (IO.userError "public guarded resume lost the failure")
    | _ => throw (IO.userError "small guarded budget did not suspend")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "guarded reachable fixtures" (checkProgram workspace)
  let equal ← compileNamed program "equalNamed"
  let equalSource ← sourceFor equal "equalNamed"
  let equalTable ← get "actual guarded equal table" (SourceCoreAssignmentFaultSites.prepare equalSource Core.wordModulus)
  require equalTable.sites.isEmpty "guarded equal demanded an unused operand reason"
  require (equalTable.diagnostic? Word.zero == none) "empty equal table interpreted a nonexistent token"
  require ((← equal.run [scalar 7]) == scalar 7) "guarded equal failed to initialize absent root"
  equal.checkCells [scalar 7] ([7,7,7,7,7,7].map fun n => (.word, some (scalar n)))
  for fuel in [0,7,43] do equal.checkResume [scalar 7] (scalar 7) fuel
  let compound ← compileNamed program "compoundNamed"
  let source ← sourceFor compound "compoundNamed"
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some node => pure node | none => throw (IO.userError "compound assignment occurrence missing")
  failure compound {
      error := .invalidAssignmentOperands .add none (some .word),
      site := .occurrence node.id.occurrence, span := some node.span}
    [(.word,some (scalar 7)),(.word,none),(.word,some (scalar 7)),(.word,some (scalar 7))]
  for name in ["equalRhsFault","compoundRhsFault"] do
    let entry ← compileNamed program name
    let source ← sourceFor entry "bad"
    let (node, binder) ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
        | _ => none with
      | some selected => pure selected | none => throw (IO.userError "named RHS fault occurrence missing")
    failure entry {
        error := .uninitializedLocal binder,
        site := .occurrence node.id.occurrence, span := some node.span}
      [(.word,some (scalar 7)),(.word,none),(.word,some (scalar 7)),(.word,some (scalar 7)),(.word,none)]
  IO.println "guarded reachable assignment diagnostics: empty equal table, concrete named RHS, ordered effects/faults, exact decoded metadata and resume GREEN"

end Tests.SourceCoreProtectedAssignmentReachableDiagnostics
