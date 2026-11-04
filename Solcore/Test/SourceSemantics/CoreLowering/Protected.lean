import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
import Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
import Solcore.SourceSemantics.CoreLowering.NamedLexicalStatements
import Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
import Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
import Solcore.SourceSemantics.CoreLowering.NamedWhileStatements
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCompletion
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint

/-!
# Protected statement tests

Protected named statements, assignments, places and loops, with fault prefixes and resume.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedAssignmentReachableDiagnostics
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedBareNamedAssignments
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! The public named Head consumers close RHS/body meanings with concrete
recursive named Trees, preserving actual installed authority and typed slots.
Core-only admitted sources exercise absent/present scalars, post-write faults,
raw mapping copies, exact argument effects, opaque prefix and real resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedBareNamedAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup SourceCoreCompatibleDataPlaces
open NamedAssignmentHeads CompatibleEquality CompatibleHeap CoreProof
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
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions assignment operator rhs)
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
theorem concrete_named_preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) :=
  NamedAssignmentHeads.preserves_prefix functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing trace

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_preserves_fault (errors : head.Errors registry faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentHeads.preserves_fault functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors trace next output

include extension faithful observations environments heaps locals agrees actualTyped installed valid unique owners runtimeViews
  uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_reflects (errors : head.Errors registry faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target operator rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after written canonical ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) :=
  NamedAssignmentHeads.reflects functions extension evidence faithful observations head environments heaps locals agrees actualTyped installed valid unique owners runtimeViews uninitialized missing bodyUninitialized bodyMissing errors completed

end Static

private def content : String := String.intercalate "\n" [
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function key(value: Word) returns (Word) { let copied = value; return copied; }",
  "function same(raw: mapping(Word => Word)) returns (mapping(Word => Word)) { let copied = raw; return copied; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function absentEqual(seed: Word) returns (Word) { let root: Word; root = first(seed); return first(root); }",
  "function compoundPresent(seed: Word) returns (Word) { let root = first(10); root += first(seed); return first(root); }",
  "function absentCompound(seed: Word) returns (Word) { let root: Word; root += first(seed); return first(99); }",
  "function rhsFault(seed: Word) returns (Word) { let root = first(10); root += bad(seed); return first(99); }",
  "function lateFault(seed: Word) returns (Word) { let root = first(10); root += first(seed); return bad(root); }",
  "function assignmentUnit(seed: Word) { let root: Word; root = first(seed); first(root); }",
  "function rawEqual(raw: mapping(Word => Word)) returns (Word) { let root: mapping(Word => Word); root = same(raw); return first(root[key(1)]); }"
]
private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word,some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"guarded bare resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"guarded bare prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type,cell.value))) == reprStr expected)
    s!"guarded bare ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "guarded bare gap binder" (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "guarded bare exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected bare named assignments" content
    ["absentEqual","compoundPresent","absentCompound","rhsFault","lateFault","assignmentUnit","rawEqual"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word,none⟩,⟨.word,some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0,43,300000] do
    for (name,result,numbers) in [("absentEqual",7,[7,7,7,7,7,7]),("compoundPresent",17,[7,10,10,17,7,7,17,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .done value final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue result)) s!"guarded bare result {name}"
        cells initial final (numbers.map present) name
      | other => throw (IO.userError s!"guarded bare {name}: {reprStr other}")
    match ← finish compiled "absentCompound" [wordValue 7] fuel initial with
    | .fault (.invalidAssignmentOperands operator left right) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (operator == .add && left == none && right == some .word) "absent compound diagnostics changed"
      cells initial final [present 7,(.word,none),present 7,present 7] "absentCompound"
    | other => throw (IO.userError s!"guarded bare absent compound: {reprStr other}")
    for (name,numbers) in [("rhsFault",[7,10,10,10,7]),("lateFault",[7,10,10,17,7,7,17])] do
      match ← finish compiled name [wordValue 7] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"guarded bare fault binder {name}"
        cells initial final (numbers.map present ++ [(.word,none)]) name
      | other => throw (IO.userError s!"guarded bare written fault {name}: {reprStr other}")
    match ← finish compiled "assignmentUnit" [wordValue 7] fuel initial with
    | .done .unit final => cells initial final ([7,7,7,7,7,7].map present) "assignmentUnit"
    | other => throw (IO.userError s!"guarded bare Unit: {reprStr other}")
    let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
      [(wordValue 1,wordValue 37),(wordValue 1,wordValue 91)]
    match ← finish compiled "rawEqual" [raw] fuel initial with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr (wordValue 37)) "raw bare mapping order changed"
      let copied : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.mapping .word .word,some raw)
      cells initial final ([copied,copied,copied,copied] ++ [1,1,37,37].map present) "rawEqual"
    | other => throw (IO.userError s!"guarded bare raw mapping: {reprStr other}")
  IO.println "protected bare named assignments: concrete RHS/body guards, actual snapshots/typed seven slots, absent operands, write-before-fault, raw duplicate mappings/prefix and resume GREEN"
end Tests.SourceCoreProtectedBareNamedAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedForBodyContracts
/-! Actual guarded for endpoints consume the concrete named condition and
recursive body certificates. Empty post semantics are proved directly here;
full protected header/post Trees are a subsequent unit. Cached Core cases
retain ordered effects, exact faults, duplicate metadata, capture snapshots
and resume. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedForBodyContracts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
section Post
variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) (program : SourceSemantics.Program)
  (evidence : Dynamic.EvidenceEnvironment) {entry : ProtectedExpressionMeaning.Entry}
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
  {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
  {faults : FunctionCalls.FaultRep}

private theorem empty_post_evaluates (continued : Bool) (store : Store) :
    Evaluates (TypedImperativeFor.postValues type location continued ++ actual) store
      (ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ)) (LocalLoop.fallthroughValue type) store := by
  have shape : ForLoop.postCode ((LocalLoop.fallthrough type).rename ξ) = LocalLoop.fallthrough type := by
    simp only [ForLoop.postCode, Core.LoopExecution.conditionCode, ← Expr.rename_insertion, LoopRenaming.fallthrough]
  rw [shape]
  exact LocalLoop.fallthrough_evaluates _ _ _

theorem empty_post_preserves : ProtectedFor.Body.PostPreserves functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext finalEnvironment state continued trace
  cases trace
  exact ⟨store, mapping, world, empty_post_evaluates continued store,
    state.1.heaps, .refl _, .refl _, .refl _ _, .refl _⟩

theorem empty_post_faults : ProtectedFor.Body.PostFaults functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) [] (LocalLoop.fallthrough type) := by
  intro mapping world before after store finalContext reason state continued trace
  cases trace

theorem empty_post_reflects : ProtectedFor.Body.PostReflects functions program evidence
    (entry := entry) (registry := registry) (source := source) (context := context) (scope := scope)
    (administrative := administrative) (actualContext := actualContext) (frameLayout := frameLayout)
    (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
    (contextLocation := contextLocation) (location := location) (type := type)
    (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults [] (LocalLoop.fallthrough type) := by
  intro mapping world before store finalStore value state continued evaluated
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (empty_post_evaluates continued store)
  exact .inl ⟨context, environment, before, mapping, world, .nil, rfl,
    state.1.heaps, .refl _, .refl _, .refl _ _, .refl _⟩
end Post

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_empty_post_preserves {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopPreserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  apply ProtectedFor.Body.loop_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    conditionFound conditionTree nativeTyped unique
    (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    exact empty_post_preserves functions program evidence
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    exact empty_post_faults functions program evidence
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_empty_post_reflects {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code : Expr} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopReflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition [] statements expected type (LocalLoop.iterate type conditionCode code (LocalLoop.fallthrough type) reason) := by
  apply ProtectedFor.Body.loop_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    conditionFound conditionTree nativeTyped
    (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
    (fun executed => body.control_not_fault unique executed)
  intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
  exact empty_post_reflects functions program evidence
end Concrete

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 3) { return true; } let gap: Word; return gap == value; }",
  "function transfers(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 4); index += next(0)) { raw[next(0)] += copied(1); if (less(index, 2)) { continue; } raw[next(0)] += copied(1); } return copied(index + raw[next(0)]); }",
  "function breaks(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 4); raw[next(0)] += copied(10), index += next(0)) { raw[next(0)] += copied(1); break; } return copied(index + raw[next(0)]); }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(10), index += next(0)) { raw[next(0)] += copied(2); return copied(raw[next(0)]); } return copied(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; false; raw[next(0)] += bad(seed)) { bad(seed); } return copied(raw[next(0)]); }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; less(index, 2); index += next(0)) { let inner = 0; while (less(inner, 3)) { inner += next(0); if (less(inner, 2)) { continue; } raw[next(0)] += copied(1); break; } for (let local = 0; less(local, 2); local += next(0)) { if (less(local, 1)) { continue; } raw[next(0)] += copied(1); } } return copied(index + raw[next(0)]); }",
  "function bodyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(9), index += next(0)) { raw[next(0)] += copied(2); bad(seed); } return copied(99); }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; true; raw[next(0)] += copied(3), let failed = bad(seed), index += next(0)) { raw[next(0)] += copied(2); continue; } return copied(99); }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (; stopOrFail(index); index += next(0)) { raw[next(0)] += copied(2); } return copied(99); }",
  "function initializerFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (raw[next(0)] += copied(3), let failed = bad(seed); true; ) { raw[next(0)] += copied(99); } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected guarded for contracts resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected guarded for contracts fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected guarded for contracts exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected guarded for contracts inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected guarded for contracts missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected guarded for contracts raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected guarded for contracts missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected guarded for contracts writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected guarded for contracts captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected guarded for contracts captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected guarded for contracts captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected guarded for contracts lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected guarded for contracts" content
    ["transfers", "breaks", "early", "zero", "nested", "bodyFault", "postFault", "conditionFault", "initializerFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled "bad"
  let conditionGap ← gapBinder compiled "stopOrFail"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("transfers",20,16,4), ("breaks",11,11,0), ("early",12,12,0), ("zero",10,10,0), ("nested",16,14,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected guarded for result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected guarded for success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("bodyFault",gap,12,0), ("postFault",gap,15,0),
        ("conditionFault",conditionGap,16,3), ("initializerFault",gap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected guarded for exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected guarded for failure {name}: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected guarded for resume changed observations"
  IO.println "protected guarded for contracts: shared finite for proof, concrete guarded condition/body, nested for/while, break skips post, continue runs post, initializer/condition/body/post first faults, raw duplicate/capture snapshots and resume GREEN"

end Tests.SourceCoreProtectedForBodyContracts
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedForHeaders
/-! Concrete named expression Trees discharge the guarded header child meaning.
Actual marked locals, seven-slot assignments and six-slot post temporaries
retain installed observations and restore the original outer capture. Full
same-family for statement grammar remains a subsequent composition boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedForHeaders
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
open CallableIndexedHistory (NativeFrame)
section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_preserves {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop} {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : ProtectedForHeader.Tail (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  exact ProtectedForHeader.Tree.preserves_prefix functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations tree valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_reflects {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ProtectedForHeader.Result (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_loop_preserves {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {post : List ForItemForm} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopPreserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition post statements expected type (LocalLoop.iterate type conditionCode code postCode reason) := by
  apply ProtectedFor.Body.loop_preserves functions program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
    conditionFound conditionTree nativeTyped unique
    (NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    intro mapping world before after store finalContext finalEnvironment state continued executed
    exact ProtectedForHeader.post_preserves functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
      (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations postTree valid agrees reference state continued executed
  · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
    intro mapping world before after store finalContext reason state continued executed
    exact ProtectedForHeader.post_fault functions definitions registered extension program evidence
      (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
      (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
      (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations postTree postErrors valid agrees reference state continued executed

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_loop_reflects {context : SourceSemantics.Context} {scope : Scope}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {post : List ForItemForm} {reason : Word} {administrative : Core.Context}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type code)
    (postTree : ProtectedForHeader.Tree layouts owner active frame globals onError values source
      (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope post postCode)
    (postErrors : GenericForHeader.Tree.Errors registry faults postTree)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode reason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedFor.Body.LoopReflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      condition post statements expected type (LocalLoop.iterate type conditionCode code postCode reason) := by
  apply ProtectedFor.Body.loop_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    conditionFound conditionTree nativeTyped
    (NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing body)
    (fun executed => body.control_not_fault unique executed)
  intro actualContext environment canonical actual ξ contextLocation location agrees reference valid
  intro mapping world before store finalStore value state continued evaluated
  exact ProtectedForHeader.post_reflects functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews postTree postErrors valid agrees reference state continued evaluated

end Concrete

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function localsContinue(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); continue; } return copied(index + raw[next(0)]); }",
  "function localsFallthrough(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); } return copied(index + raw[next(0)]); }",
  "function postBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(1); break; } return copied(raw[next(0)]); }",
  "function postReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); return copied(raw[next(0)]); } return copied(99); }",
  "function bitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let mask = copied(0); less(index, 2); mask ~=, mask ~=, index += next(0)) { raw[next(0)] += copied(1); } return copied(index + raw[next(0)]); }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let staged = copied(3), raw[next(0)] += copied(staged), let missing: Word, raw[next(0)] += copied(missing), index += copied(9)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }",
  "function initialFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (raw[next(0)] += copied(3), let ready = copied(0), let missing: Word, let dead = copied(missing); true; ) { raw[next(0)] += copied(99); } return copied(99); }",
  "function bitNotFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let missing: Word; true; missing ~=, raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected for headers resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name binderName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected for headers fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == binderName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected for headers exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected for headers inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected for headers missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected for headers raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected for headers missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected for headers writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected for headers captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected for headers captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected for headers captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected for headers lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected for headers" content
    ["localsContinue", "localsFallthrough", "postBreak", "postReturn", "bitNot", "postFault", "initialFault", "bitNotFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let postGap ← gapBinder compiled "postFault" "missing"
  let initialGap ← gapBinder compiled "initialFault" "missing"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("localsContinue",19,16,3), ("localsFallthrough",19,16,3), ("postBreak",11,11,0), ("postReturn",12,12,0), ("bitNot",14,12,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected for headers result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected for headers success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("postFault",postGap,15,1), ("initialFault",initialGap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected for headers exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected for headers failure {name}: {reprStr other}")
    let unary ← finish compiled "bitNotFault" fuel initial
    match unary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bitNotFault" 12 1
      current := current ++ [reprStr unary]
    | other => throw (IO.userError s!"protected for headers exact absent unary fault: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected for headers resume changed observations"
  IO.println "protected for headers: concrete named prefix/post, fresh marked locals, outer entry restoration, continue/fallthrough, break/return skip, seven-slot assignments/unary, exact first faults, raw duplicates/capture snapshots and resume GREEN"

end Tests.SourceCoreProtectedForHeaders
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedAssignments
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete named expression trees supply all key/RHS/tail meanings. Real
installed/global/history guards remain entry facts. Cached checked-source
runs cover write-before-tail-fault, earlier key/RHS/default faults and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup TypedScopedStatements
open NamedAssignmentStatementTail
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Static named argument/body trees and the real installed entry close the
entire projected assignment and fixed-scope tail. All fault prefixes are
included; no runtime child/body meaning is an external premise. -/
theorem concrete_named_preserves {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentStatementTail.Tree.preserves functions extension faithful observations runtimeViews evidence valid unique owners
    uninitialized missing bodyUninitialized bodyMissing tree errors environments heaps locals agrees actualTyped installed trace

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Actual completed Core code supplies key, getter, RHS and tail outcomes in
source order. Installed closure payloads and frame history are retained from
the real administrative preservation receipts. -/
theorem concrete_named_reflects {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical :=
  NamedAssignmentStatementTail.Tree.reflects functions extension faithful observations runtimeViews evidence valid unique owners
    uninitialized missing bodyUninitialized bodyMissing tree errors environments heaps locals agrees actualTyped installed evaluated

end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { return value; }",
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function compound(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += first(seed); first(seed); return raw[key(seed)]; }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[bad(seed)] += first(seed); return seed; }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += bad(seed); return seed; }",
  "function tailFault(raw: mapping(Word => Word), seed: Word) returns (Word) { raw[key(seed)] += first(seed); return bad(seed); }",
  "function unitTail(raw: mapping(Word => Word), seed: Word) { raw[key(seed)] = first(seed); first(seed); }",
  "function getterFault(table: mapping(Word => mapping(Word => function(Word) returns (Word))), seed: Word, replacement: function(Word) returns (Word)) returns (Word) { table[key(seed)][first(seed)] = replacement; return seed; }"
]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected assignment resume {name}" (first.resume 300000)).observation

private def checkPrefix (initial final : SourceTypedRuntime.RuntimeState) : IO Unit :=
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "protected assignment source prefix changed"

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  checkPrefix initial final
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected assignment ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected assignment fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected assignment exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named assignments" content
    ["compound", "keyFault", "rhsFault", "tailFault", "unitTail", "getterFault"]
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 37)), (seven, .word (Word.ofNatModulo 91))]
  let updated : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 44)), (seven, .word (Word.ofNatModulo 91))]
  let replaced : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, seven), (seven, .word (Word.ofNatModulo 91))]
  let mapType : TypeSystem.Ty := .mapping .word .word
  let functionTy : TypeSystem.Ty := .function .word .word
  let innerTy : TypeSystem.Ty := .mapping (.comptime .word) (.comptime functionTy)
  let outer : SourceTypedRuntime.Value := .mapping (.comptime .word) innerTy []
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "key"
  let replacement : SourceTypedRuntime.Value := .global key []
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 300000] do
    match ← finish compiled "compound" [raw, seven] fuel initial with
    | .done (.word actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == Word.ofNatModulo 44) "compound named result changed"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven)] "compound"
    | other => throw (IO.userError s!"protected assignment compound: {reprStr other}")
    match ← finish compiled "keyFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "key fault lost source binder"
      cells initial final [(mapType, some raw), (.word, some seven), (.word, some seven), (.word, none)] "keyFault"
    | other => throw (IO.userError s!"protected assignment key fault: {reprStr other}")
    match ← finish compiled "rhsFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "RHS fault lost source binder"
      cells initial final [(mapType, some raw), (.word, some seven), (.word, some seven), (.word, some seven), (.word, none)] "rhsFault"
    | other => throw (IO.userError s!"protected assignment RHS fault: {reprStr other}")
    match ← finish compiled "tailFault" [raw, seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "tail fault lost source binder"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, none)] "tailFault"
    | other => throw (IO.userError s!"protected assignment written tail fault: {reprStr other}")
    match ← finish compiled "unitTail" [raw, seven] fuel initial with
    | .done .unit final =>
      cells initial final [(mapType, some replaced), (.word, some seven), (.word, some seven),
        (.word, some seven), (.word, some seven), (.word, some seven), (.word, some seven)] "unitTail"
    | other => throw (IO.userError s!"protected assignment Unit tail: {reprStr other}")
    match ← finish compiled "getterFault" [outer, seven, replacement] fuel initial with
    | .fault (.typeMismatch actual none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == .comptime functionTy) "getter fault raw default type changed"
      cells initial final [( .mapping .word (.mapping .word functionTy), some outer), (.word, some seven),
        (functionTy, some replacement), (.word, some seven), (.word, some seven), (.word, some seven)] "getterFault"
    | other => throw (IO.userError s!"protected assignment missing default: {reprStr other}")
  IO.println "protected named assignments: concrete guarded tail, all fault phases, ordered cells/raw metadata/duplicates, write-before-fault, default and resume GREEN"
end Tests.SourceCoreProtectedNamedAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedFor
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete consumers close named child/body meanings at the actual static
administrative context. Core-only fixtures combine source bindings, nested loop/transfer, scoped
control and bare/projected writes; ordered source cells, raw headers/duplicate keys,
first faults, retained writes and real resume are observed separately. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedFor
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedImperativeForStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Initializers and the nested body inhabit the same recursive grammar. The
head is followed by its concrete tail with no runtime endpoint premise. -/
theorem concrete_for_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.Errors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.Errors registry faults tail) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Completed initializers, finite iterations and post are inverted before the
tail. Break/return skip post and continue/fallthrough run it in source order. -/
theorem concrete_for_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.Errors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.Errors registry faults tail) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function bodyCallFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; raw[next(0)] += copied(99)) { raw[next(0)] += copied(5); index += copied(1); copied(bad(seed)); } return copied(99); }",
  "function nestedFor(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; let mask = copied(0); mask ~=; mask ~=; for (let outer = copied(0); less(outer, 2); let postLocal = next(outer), copied(postLocal), outer += copied(1)) { for (let inner: Word, inner = copied(0); less(inner, 3); let local = next(inner), copied(local), inner += copied(1)) { index += copied(1); if (less(inner, 1)) { continue; } raw[next(0)] += copied(2); if (less(outer, 1)) { break; } } } return copied(index + raw[next(0)]); }",
  "function forWhile(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); less(outer, 2); outer += copied(1)) { let inner = copied(0); while (less(inner, 2)) { inner += copied(1); index += copied(1); if (less(inner, 2)) { continue; } raw[next(0)] += copied(3); break; } } return copied(index + raw[next(0)]); }",
  "function whileFor(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; let outer = copied(0); while (less(outer, 2)) { outer += copied(1); for (let inner = copied(0); less(inner, 2); inner += copied(1)) { index += copied(1); raw[next(0)] += copied(2); if (less(outer, 2)) { continue; } break; } } return copied(index + raw[next(0)]); }",
  "function nestedReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); true; let dead = bad(seed)) { while (true) { for (let inner = copied(0); true; let dead = bad(seed)) { raw[next(0)] += copied(4); index += copied(1); return copied(index + raw[next(0)]); } } } return copied(99); }",
  "function bodyBitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let mask = copied(0), mask ~=, mask ~=; less(index, 2); index += copied(1), mask ~=, mask ~=) { mask ~=; mask ~=; raw[next(0)] += copied(2); } return copied(index + raw[next(0)]); }",
  "function bodyBitNotFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let outer = copied(0); true; raw[next(0)] += copied(99)) { let absent: Word; index += copied(1); raw[next(0)] += copied(3); absent ~=; } return copied(99); }",
  "function localsContinue(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); continue; } return copied(index + raw[next(0)]); }",
  "function localsFallthrough(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first: Word, first = copied(0), let header = next(0), copied(header); less(first, 3); let absent: Word, absent = next(first), let retained = copied(absent), copied(retained), raw[next(0)] += copied(retained), first += copied(1)) { index += copied(1); } return copied(index + raw[next(0)]); }",
  "function postBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(1); break; } return copied(raw[next(0)]); }",
  "function postReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let never = bad(seed), raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); return copied(raw[next(0)]); } return copied(99); }",
  "function bitNot(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let mask = copied(0); less(index, 2); mask ~=, mask ~=, index += next(0)) { raw[next(0)] += copied(1); } return copied(index + raw[next(0)]); }",
  "function postFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let first = copied(0); true; let staged = copied(3), raw[next(0)] += copied(staged), let missing: Word, raw[next(0)] += copied(missing), index += copied(9)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }",
  "function initialFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (raw[next(0)] += copied(3), let ready = copied(0), let missing: Word, let dead = copied(missing); true; ) { raw[next(0)] += copied(99); } return copied(99); }",
  "function bitNotFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; for (let missing: Word; true; missing ~=, raw[next(0)] += copied(99)) { raw[next(0)] += copied(2); index += copied(1); continue; } return copied(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named for resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name binderName : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named for fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == binderName) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named for exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected named for inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected named for missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected named for raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected named for missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected named for writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected named for captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected named for captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected named for captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected named for lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named for" content
    ["bodyCallFault", "nestedFor", "forWhile", "whileFor", "nestedReturn", "bodyBitNot", "bodyBitNotFault", "localsContinue", "localsFallthrough", "postBreak", "postReturn", "bitNot", "postFault", "initialFault", "bitNotFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let bodyGap ← gapBinder compiled "bad" "gap"
  let postGap ← gapBinder compiled "postFault" "missing"
  let initialGap ← gapBinder compiled "initialFault" "missing"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("nestedFor",21,16,5), ("forWhile",20,16,4), ("whileFor",19,16,3), ("nestedReturn",15,14,1), ("bodyBitNot",16,14,2), ("localsContinue",19,16,3), ("localsFallthrough",19,16,3), ("postBreak",11,11,0), ("postReturn",12,12,0), ("bitNot",14,12,2)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected named for result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named for success {name}: {reprStr other}")
    for (name, exactGap, updated, counter) in [("bodyCallFault",bodyGap,15,1), ("postFault",postGap,15,1), ("initialFault",initialGap,13,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected named for exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named for failure {name}: {reprStr other}")
    let bodyUnary ← finish compiled "bodyBitNotFault" fuel initial
    match bodyUnary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bodyBitNotFault" 13 1
      current := current ++ [reprStr bodyUnary]
    | other => throw (IO.userError s!"protected named for body unary fault: {reprStr other}")
    let unary ← finish compiled "bitNotFault" fuel initial
    match unary with
    | .fault (.invalidUnaryOperand .bitNot none) final =>
      observe initial final "bitNotFault" 12 1
      current := current ++ [reprStr unary]
    | other => throw (IO.userError s!"protected named for exact absent unary fault: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected named for resume changed observations"
  IO.println "protected named for: same statements/initializers grammar, nested for/while/break/continue/return, body/header/post unary, concrete named prefix/post, fresh marked locals, outer entry restoration, continue/fallthrough, break/return skip, seven-slot assignments/unary, exact first faults, raw duplicates/capture snapshots and resume GREEN"

end Tests.SourceCoreProtectedNamedFor
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedLexical
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! The concrete guarded consumer has no runtime child/body meaning premise.
Actual checked Core fixtures retain lexical allocation order, restore outer
bindings, skip unselected/faulted tails and resume with the same source prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedLexical
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLexicalStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings and condition
slots. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Preserves functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Reflects functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence uninitialized missing bodyUninitialized bodyMissing tree

end Static

private def content : String := String.intercalate "\n" [
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function predicate(value: Word) returns (Bool) { let copied = value; return copied > 0; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(seed: Word) returns (Word) { let saved = first(seed); { let hidden = first(saved + 1); hidden; } if (predicate(saved)) { let chosen = first(saved + 2); chosen; } else { let unused = bad(saved); unused; } return first(saved + 3); }",
  "function shadow(seed: Word) returns (Word) { let saved = first(seed); { let saved = first(4); if (predicate(saved)) { let inside = first(saved + 1); inside; } } return first(saved); }",
  "function branches(seed: Word) returns (Word) { let saved = first(seed); if (predicate(saved)) { return first(9); } else { return first(5); } return bad(saved); }",
  "function initializerFault(seed: Word) returns (Word) { let saved = first(seed); let failed = bad(saved); return first(99); }",
  "function conditionFault(seed: Word) returns (Word) { let saved = first(seed); if (predicate(bad(saved))) { let unreachable = first(99); unreachable; } return first(100); }",
  "function discardedFault(seed: Word) returns (Word) { let saved = first(seed); { let retained = first(4); bad(saved); } return first(99); }",
  "function unitTail(seed: Word) { let saved = first(seed); let gap: Word; { let hidden = first(saved + 1); hidden; } if (predicate(saved)) { first(saved + 2); } else { bad(saved); } }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected lexical resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected lexical prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected lexical ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected lexical fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected lexical exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named lexical" content
    ["nested", "shadow", "branches", "initializerFault", "conditionFault", "discardedFault", "unitTail"]
  let seven := wordValue 7
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  for fuel in [0, 43, 300000] do
    match ← finish compiled "nested" [seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 10)) "protected nested result changed"
      cells initial final (([7, 7, 7, 7, 8, 8, 8, 7, 7, 9, 9, 9, 10, 10]).map present) "nested"
    | other => throw (IO.userError s!"protected nested: {reprStr other}")
    match ← finish compiled "shadow" [seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr seven) "protected outer scope was not restored"
      cells initial final (([7, 7, 7, 7, 4, 4, 4, 4, 4, 5, 5, 5, 7, 7]).map present) "shadow"
    | other => throw (IO.userError s!"protected shadow restore: {reprStr other}")
    for (seed, result) in [(7, 9), (0, 5)] do
      match ← finish compiled "branches" [wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) "protected branch result changed"
        cells initial final (([seed, seed, seed, seed, seed, seed, result, result]).map present) "branches"
      | other => throw (IO.userError s!"protected selected branch: {reprStr other}")
    for (name, observedCells) in [("initializerFault", [7, 7, 7, 7, 7]), ("conditionFault", [7, 7, 7, 7, 7]),
        ("discardedFault", [7, 7, 7, 7, 4, 4, 4, 7])] do
      match ← finish compiled name [seven] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"protected {name} fault binder changed"
        cells initial final (observedCells.map present ++ [(.word, none)]) name
      | other => throw (IO.userError s!"protected lexical fault {name}: {reprStr other}")
    match ← finish compiled "unitTail" [seven] fuel initial with
    | .done .unit final =>
      cells initial final (([7, 7, 7, 7]).map present ++ [(.word, none)] ++ ([8, 8, 8, 7, 7, 9, 9]).map present) "unitTail"
    | other => throw (IO.userError s!"protected lexical Unit: {reprStr other}")
  IO.println "protected named lexical: concrete guards through real allocations, nested/selected scopes, outer restore, fault prefixes, Unit/fallthrough and resume GREEN"
end Tests.SourceCoreProtectedNamedLexical
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedLexicalAssignments
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete consumers close named child/body meanings at the actual static
administrative context. Core-only fixtures combine source bindings, scoped
control and bare/projected writes; ordered source cells, raw headers/duplicate keys,
first faults, retained writes and real resume are observed separately. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedLexicalAssignments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLexicalAssignments
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- A real head, including an empty projection path, composes with the same
concrete recursive tail. No projected-path or runtime child premise is needed. -/
theorem concrete_named_assignment_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Whole completed code is reflected through a bare or projected head before
the recursive tail; its seven real slots and protected entry come from the head. -/
theorem concrete_named_assignment_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)

end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { let copied = value; return copied; }",
  "function first(value: Word) returns (Word) { let copied = value; return copied; }",
  "function predicate(value: Word) returns (Bool) { let copied = value; return copied > 0; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(saved + 1); raw[key(1)] += first(delta); } if (predicate(saved)) { let delta = first(saved + 2); raw[key(1)] += first(delta); } else { raw[key(bad(saved))] += first(99); } return first(raw[key(1)]); }",
  "function shadow(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let saved = first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { raw[key(1)] += first(2); } else { raw[key(1)] += first(5); } return first(saved); }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { let delta = first(2); raw[key(1)] += bad(delta); } return first(99); }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { raw[bad(saved)] += first(99); } return first(100); }",
  "function earlyReturn(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); if (predicate(saved)) { let delta = first(2); raw[key(1)] += first(delta); return first(raw[key(1)]); } else { return first(6); } return bad(99); }",
  "function tailFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let delta = first(4); raw[key(1)] += first(delta); } if (predicate(saved)) { raw[key(1)] += first(2); } return bad(saved); }",
  "function unitTail(raw: mapping(Word => Word), seed: Word) { let saved = first(seed); let gap: Word; { let delta = first(4); raw[key(1)] = first(delta); } if (predicate(saved)) { raw[key(1)] += first(2); } }",
  "function getterFault(table: mapping(Word => mapping(Word => function(Word) returns (Word))), seed: Word, replacement: function(Word) returns (Word)) returns (Word) { { let chosen = first(seed); table[key(chosen)][first(chosen)] = replacement; } return seed; }",
  "function bareMixed(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: Word; saved = first(seed); { let delta = first(saved + 1); saved += first(delta); raw[key(1)] += first(saved); } if (predicate(saved)) { saved = first(saved + 2); raw[key(1)] += first(saved); } else { saved = first(99); } return first(saved + raw[key(1)]); }",
  "function bareBranch(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { let saved: Word; saved = first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { saved += first(2); } else { saved = first(5); } return first(saved); }",
  "function bareOperandFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: Word; { raw[key(1)] += first(4); saved += first(seed); } return first(99); }",
  "function bareRhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved = first(seed); { saved += first(4); raw[key(1)] += first(saved); } if (predicate(saved)) { saved = bad(saved); } return first(99); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def present (n : Nat) : TypeSystem.Ty × Option SourceTypedRuntime.Value := (.word, some (wordValue n))
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected lexical assignment resume {name}" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected lexical assignment prefix changed {name}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected lexical assignment ordered cells {name}: {reprStr final.heap}"

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "bad"
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected lexical assignment fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected lexical assignment exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named lexical assignments" content
    ["nested", "shadow", "rhsFault", "keyFault", "earlyReturn", "tailFault", "unitTail", "getterFault",
      "bareMixed", "bareBranch", "bareOperandFault", "bareRhsFault"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled
  let mapType : TypeSystem.Ty := .mapping .word .word
  for fuel in [0, 43, 300000] do
    match ← finish compiled "nested" [table 10, wordValue 3] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 19)) "nested assignment result changed"
      cells initial final ((mapType, some (table 19)) :: ([3,3,3,3,4,4,4,1,1,4,4,3,3,5,5,5,1,1,5,5,1,1,19,19]).map present) "nested"
    | other => throw (IO.userError s!"protected nested assignment: {reprStr other}")
    for (seed, updated) in [(3,16), (0,19)] do
      match ← finish compiled "shadow" [table 10, wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue seed)) "assignment inner binding escaped"
        let chosen := if seed = 0 then 5 else 2
        cells initial final ((mapType, some (table updated)) ::
          ([seed,seed,seed,seed,4,4,4,1,1,4,4,seed,seed,1,1,chosen,chosen,seed,seed]).map present) "shadow"
      | other => throw (IO.userError s!"protected assignment restored branch: {reprStr other}")
    for (name, numbers, written) in [
        ("rhsFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,2,2,2,1,1,2],14),
        ("keyFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,3],14),
        ("tailFault", [3,3,3,3,4,4,4,1,1,4,4,3,3,1,1,2,2,3],16)] do
      match ← finish compiled name [table 10, wordValue 3] fuel initial with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) s!"assignment fault binder changed {name}"
        cells initial final ((mapType, some (table written)) :: (numbers.map present ++ [(.word,none)])) name
      | other => throw (IO.userError s!"protected lexical assignment fault {name}: {reprStr other}")
    for (seed, result, updated, numbers) in [
        (3,12,12,[3,3,3,3,3,3,2,2,2,1,1,2,2,1,1,12,12]),
        (0,6,10,[0,0,0,0,0,0,6,6])] do
      match ← finish compiled "earlyReturn" [table 10,wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) "assignment early return changed"
        cells initial final ((mapType,some (table updated)) :: numbers.map present) "earlyReturn"
      | other => throw (IO.userError s!"protected assignment early return: {reprStr other}")
    match ← finish compiled "unitTail" [table 10,wordValue 3] fuel initial with
    | .done .unit final =>
      cells initial final ((mapType,some (table 6)) ::
        (([3,3,3,3]).map present ++ [(.word,none)] ++ ([4,4,4,1,1,4,4,3,3,1,1,2,2]).map present)) "unitTail"
    | other => throw (IO.userError s!"protected lexical assignment Unit: {reprStr other}")
    let functionTy : TypeSystem.Ty := .function .word .word
    let outer : SourceTypedRuntime.Value := .mapping (.comptime .word) (.mapping (.comptime .word) (.comptime functionTy)) []
    let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "first"
    let replacement : SourceTypedRuntime.Value := .global key []
    match ← finish compiled "getterFault" [outer,wordValue 3,replacement] fuel initial with
    | .fault (.typeMismatch actual none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == .comptime functionTy) "nested default raw header changed"
      cells initial final [( .mapping .word (.mapping .word functionTy),some outer), present 3,
        (functionTy,some replacement), present 3,present 3,present 3,present 3,present 3,present 3,present 3] "getterFault"
    | other => throw (IO.userError s!"protected lexical assignment default: {reprStr other}")
    match ← finish compiled "bareMixed" [table 10, wordValue 3] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 35)) "mixed bare/projected result changed"
      cells initial final ((mapType,some (table 26)) :: present 3 :: present 9 ::
        ([3,3,4,4,4,4,4,1,1,7,7,7,7,9,9,1,1,9,9,1,1,35,35]).map present) "bareMixed"
    | other => throw (IO.userError s!"protected mixed bare/projected: {reprStr other}")
    for (seed, chosen) in [(3,2), (0,5)] do
      match ← finish compiled "bareBranch" [table 10,wordValue seed] fuel initial with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue 5)) "bare scoped branch result changed"
        cells initial final ((mapType,some (table 14)) ::
          ([seed,seed,seed,5,4,4,4,1,1,4,4,seed,seed,chosen,chosen,5,5]).map present) "bareBranch"
      | other => throw (IO.userError s!"protected bare restored branch: {reprStr other}")
    match ← finish compiled "bareOperandFault" [table 10,wordValue 3] fuel initial with
    | .fault (.invalidAssignmentOperands .add none (some .word)) final =>
      cells initial final ((mapType,some (table 14)) :: present 3 :: (.word,none) ::
        ([1,1,4,4,3,3]).map present) "bareOperandFault"
    | other => throw (IO.userError s!"protected bare fault after projected write: {reprStr other}")
    match ← finish compiled "bareRhsFault" [table 10,wordValue 3] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap) "bare RHS exact fault binder changed"
      cells initial final ((mapType,some (table 17)) ::
        (([3,3,3,7,4,4,1,1,7,7,7,7,7]).map present ++ [(.word,none)])) "bareRhsFault"
    | other => throw (IO.userError s!"protected bare RHS after retained writes: {reprStr other}")
  IO.println "protected named lexical assignments: recursive bindings/scopes/bare and projected writes, exact ordered cells/raw metadata/duplicates, first faults/retained writes, guarded consumers and resume GREEN"
end Tests.SourceCoreProtectedNamedLexicalAssignments
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedLoops
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete consumers close named child/body meanings at the actual static
administrative context. Core-only fixtures combine source bindings, nested loop/transfer, scoped
control and bare/projected writes; ordered source cells, raw headers/duplicate keys,
first faults, retained writes and real resume are observed separately. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedLoops
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open NamedLoopStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLoopStatements.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- A real head, including an empty projection path, composes with the same
concrete recursive tail. No projected-path or runtime child premise is needed. -/
theorem concrete_named_assignment_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Whole completed code is reflected through a bare or projected head before
the recursive tail; its seven real slots and protected entry come from the head. -/
theorem concrete_named_assignment_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : ProtectedAssignmentHeads.Head values source context
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope administrative ambient.definitions assignment operator rhs)
    (errors : head.Errors registry faults)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type body) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.assignment found form head errors tail)


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Both the loop body and the enclosing tail belong to this same tree. The
finite native loop proof receives the body IH, not a supplied runtime theorem. -/
theorem concrete_nested_preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {conditionCode loopCode tailCode : Expr} {reason : Word} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) ambient.definitions)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type tailCode) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) tailCode) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing
    (.whileLoop found form conditionFound conditionType conditionTree body nativeTyped tail)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- A whole native completion reflects the same recursively certified loop
body and tail, with the source control/fault distinction derived internally. -/
theorem concrete_nested_reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
    {conditionCode loopCode tailCode : Expr} {reason : Word} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (body : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope false statements expected type loopCode)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode loopCode reason) (LocalLoop.resultType type) ambient.definitions)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode rest expected type tailCode) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.whileLoop type conditionCode loopCode reason) tailCode) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing
    (.whileLoop found form conditionFound conditionType conditionTree body nativeTyped tail)

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function nested(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 4)) { index += copied(1); if (less(index, 2)) { continue; } let inner = 0; while (less(inner, 4)) { inner += next(0); if (less(inner, 2)) { continue; } raw[next(0)] += copied(1); if (less(1, inner)) { break; } } } return copied(index + raw[next(0)]); }",
  "function outerBreak(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { raw[next(0)] += copied(2); index += next(0); if (less(2, index)) { break; } } return copied(index + raw[next(0)]); }",
  "function nestedFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); let inner = 0; while (less(inner, 3)) { inner += next(0); raw[next(0)] += copied(1); if (less(1, inner)) { bad(index); } } } return copied(99); }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 3) { return true; } let gap: Word; return gap == value; }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); let inner = 0; while (less(inner, 4)) { inner += next(0); raw[next(0)] += copied(1); if (less(1, inner)) { return copied(raw[next(0)] + index); } } } return bad(seed); }",
  "function unitLoop(raw: mapping(Word => Word), seed: Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 4)) { index += next(0); if (less(index, 2)) { continue; } { let delta = copied(2); raw[next(0)] += delta; } if (less(2, index)) { break; } } }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (stopOrFail(index)) { raw[next(0)] += copied(3); index += next(0); } return copied(99); }",
  "function keyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); if (less(0, index)) { raw[bad(index)] += copied(99); } } return copied(99); }",
  "function rhsFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { index += next(0); { let chosen = copied(2); raw[next(0)] += chosen; raw[next(0)] += bad(index); } } return copied(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 0)) { while (less(index, 4)) { bad(seed); break; } } return copied(raw[next(0)]); }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named recursive loops resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named recursive loops fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named recursive loops exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected named recursive loops inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected named recursive loops missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected named recursive loops raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected named recursive loops missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected named recursive loops writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected named recursive loops captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected named recursive loops captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected named recursive loops captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected named recursive loops lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named recursive loops contracts" content
    ["nested", "outerBreak", "nestedFault", "early", "unitLoop", "conditionFault", "keyFault", "rhsFault", "zero"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let gap ← gapBinder compiled "bad"
  let conditionGap ← gapBinder compiled "stopOrFail"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("nested",17,13,4), ("outerBreak",19,16,3), ("early",13,12,1), ("zero",10,10,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected named recursive result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named recursive success {name}: {reprStr other}")
    let completed ← finish compiled "unitLoop" fuel initial
    match completed with
    | .done .unit final =>
      observe initial final "unitLoop" 14 3
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected named recursive Unit transfer: {reprStr other}")
    for (name, exactGap, updated, counter) in [("nestedFault",gap,12,1), ("conditionFault",conditionGap,19,3),
        ("keyFault",gap,10,1), ("rhsFault",gap,12,1)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == exactGap) s!"protected named recursive exact fault {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected named recursive failure {name}: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected named recursive resume changed observations"
  IO.println "protected named recursive loops contracts: same recursive Tree consumers, nested loops/break/continue/return, condition/key/RHS/body first faults, raw duplicate/capture snapshots and resume GREEN"

end Tests.SourceCoreProtectedNamedLoops
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedPlaces
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Actual lexical binding and guarded key/RHS consumers retain the installed
named globals and caller frame. Native source fixtures additionally exercise
writeback, earlier effects on failure, raw headers/duplicates and escaped
captures through the cached Core pipeline. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedPlaces
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup

section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (leaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (caller : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context caller)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

variable {scope : SourceCoreLocalCell.Scope} {projections : List PlaceProjection}
  {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Core.Environment}
  {before : Dynamic.Heap} {store : Core.Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
    scope mapping world before store canonical)

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- The concrete recursive Tree eliminates every child/body runtime premise.
The actual protected entry still has to be supplied at the key phase. -/
theorem named_key_preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {evaluated : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
    (trace : Dynamic.SourceProjectionsEvaluate program context caller source environment before projections evaluated after) :
    ∃ sources native finalStore finalMap finalWorld,
      DataPlaceKeyOrder.Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues native)) finalStore ∧
      DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types (codes.map (·.type)) sources native ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.preserves
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    environments heaps locals agrees typed installed trace

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments heaps locals agrees typed installed in
/-- Key completion reconstructs source projection evaluation/fault in order,
using protected lookup/current-frame facts at the actual current key prefix. -/
theorem named_key_reflects
    (tree : DataExpressionSequence.Tree source
      (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
      scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    {value : Core.Value} {finalStore : Core.Store}
    (complete : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      DataPlaceKeyOrder.OutcomeTrace program context caller source environment before projections outcome after ∧
      DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  ProtectedPlaceKeys.reflects
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix) tree
    (NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing)
    environments heaps locals agrees typed installed complete

variable {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
  {preparedPlace : SourceCoreCompatibleDataPlaces.Prepared} {leaf : TypeSystem.Ty}
  {targetHeap : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}
  (resolution : CompatiblePlaceResolution.Execution values.checked registry functions preparedPlace
    (CompatibleRenamedPlace.renamedCodes codes ξ) types place leaf target actual store mapping world before targetHeap)

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments locals agrees typed installed in
/-- The concrete named Tree supplies RHS meaning after the real key/getter
prefix, including all three hidden slots and the live post-RHS root. -/
theorem named_rhs_preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context caller source environment targetHeap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := caller)
        (source := source) (faults := faults) resolution id node (CompatibleRenamedPlace.renamed lowered ξ)
        environment outcome after value finalStore finalMap finalWorld :=
  ProtectedPlaceRhs.preserves resolution
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree found environments agrees typed locals installed trace

include extension faithful leaves runtimeViews valid uninitialized missing bodyUninitialized bodyMissing
  environments locals agrees typed installed in
/-- Actual RHS completion yields its independent source outcome and exact
post-prefix heap. No source execution or body meaning is a premise. -/
theorem named_rhs_reflects
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node)
    {value : Core.Value} {finalStore : Core.Store}
    (complete : Evaluates
      (DataPlaceExecution.snapshotEnvironment preparedPlace.route.rootType resolution.target
        (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) actual)
      resolution.store (SourceCoreCompatibleDataPlaces.shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := caller)
        (source := source) (faults := faults) resolution id node (CompatibleRenamedPlace.renamed lowered ξ)
        environment outcome after value finalStore finalMap finalWorld :=
  ProtectedPlaceRhs.reflects resolution
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful leaves runtimeViews caller valid
      uninitialized missing bodyUninitialized bodyMissing)
    tree found environments agrees typed locals installed complete

/-- Scope removal restores variable attribution and retains the new store,
world, source map, exact captured closure and administrative histories. -/
theorem bind_restore {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Core.Store} {canonical : Core.Environment}
    (entry : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world heap store canonical)
    (id : Resolved.LocalId) (type : Core.Ty) (value : Core.Value) :
    NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world heap store canonical := by
  have binding := NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix
  exact binding.restore (id := id) (type := type) (value := value) (binding.prepend entry)
end Static

private def content : String := String.intercalate "\n" [
  "function key(value: Word) returns (Word) { return value; }",
  "function first(value: Word) returns (integer) { let copied = wordToInteger(value); return copied; }",
  "function normal(seed: Word) returns (integer) { let saved = seed; let other = first(saved); let m: mapping(Word => Word); m[key(saved)] = wordFromInteger(integerAdd(first(saved), first(3))); return wordToInteger(m[key(saved)]); }",
  "function scoped(seed: Word) returns (integer) { let saved = seed; { let hidden = first(saved); hidden; } let m: mapping(Word => Word); m[key(saved)] = wordFromInteger(integerAdd(first(saved), 1)); return wordToInteger(m[key(saved)]); }",
  "function failing(seed: Word) returns (integer) { let saved = seed; let m: mapping(Word => Word); let gap: Word; m[key(saved)] = wordFromInteger(integerAdd(first(saved), first(gap))); return wordToInteger(m[saved]); }",
  "function keyFail(seed: Word) returns (integer) { let saved = seed; let m: mapping(Word => Word); let gap: Word; m[key(gap)] = wordFromInteger(first(saved)); return wordToInteger(m[saved]); }",
  "function rawUpdate(raw: mapping(Word => Word), seed: Word) returns (mapping(Word => Word)) { raw[key(seed)] = key(seed) + 1; return raw; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let saved = seed; return lam(delta: Word) -> Word { let m: mapping(Word => Word); m[key(saved)] = key(saved) + key(delta); return m[key(saved)]; }; }",
  "function escaped(seed: Word, delta: Word) returns (integer) { let apply = make(seed); return wordToInteger(apply(delta)); }"
]
private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) :
    IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected named resume {name}" (first.resume 300000)).observation

private def checkPrefix (initial final : SourceTypedRuntime.RuntimeState) : IO Unit :=
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    "protected named source prefix changed"

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (name : String) : IO Unit := do
  checkPrefix initial final
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"protected named ordered cells {name}: {reprStr final.heap}"

private def faultBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected named fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected named exact fault binder missing")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named places" content
    ["normal", "scoped", "failing", "keyFail", "rawUpdate", "escaped"]
  let seven : SourceTypedRuntime.Value := .word (Word.ofNatModulo 7)
  let three : SourceTypedRuntime.Value := .word (Word.ofNatModulo 3)
  let eight : SourceTypedRuntime.Value := .word (Word.ofNatModulo 8)
  let ten : SourceTypedRuntime.Value := .word (Word.ofNatModulo 10)
  let mapType : TypeSystem.Ty := .mapping .word .word
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, .word (Word.ofNatModulo 37)), (seven, .word (Word.ofNatModulo 91))]
  let updated : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word)
    [(seven, eight), (seven, .word (Word.ofNatModulo 91))]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let failingGap ← faultBinder compiled "failing"
  let keyGap ← faultBinder compiled "keyFail"
  for fuel in [0, 43, 300000] do
    match ← finish compiled "normal" [seven] fuel initial with
    | .done (.integer 10) final =>
      cells initial final [(.word, some seven), (.word, some seven), (.word, some seven),
        (.integer, some (.integer 7)), (.integer, some (.integer 7)),
        (mapType, some (.mapping .word .word [(seven, ten)])), (.word, some seven),
        (.word, some seven), (.integer, some (.integer 7)), (.word, some three),
        (.integer, some (.integer 3)), (.word, some seven)] "normal"
    | other => throw (IO.userError s!"protected named normal: {reprStr other}")
    match ← finish compiled "scoped" [seven] fuel initial with
    | .done (.integer 8) final => checkPrefix initial final
    | other => throw (IO.userError s!"protected named scope restore: {reprStr other}")
    match ← finish compiled "rawUpdate" [raw, seven] fuel initial with
    | .done actual final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr updated)
        "protected named raw header/duplicates changed"
      cells initial final [(mapType, some updated), (.word, some seven), (.word, some seven),
        (.word, some seven)] "rawUpdate"
    | other => throw (IO.userError s!"protected named raw update: {reprStr other}")
    match ← finish compiled "escaped" [seven, three] fuel initial with
    | .done (.integer 10) final =>
      checkPrefix initial final
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.any fun cell => reprStr cell.value == reprStr (some (.mapping .word .word [(seven, ten)]) : Option SourceTypedRuntime.Value))
        "protected named escaped capture lost written map"
    | other => throw (IO.userError s!"protected named escaped: {reprStr other}")
    match ← finish compiled "failing" [seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == failingGap) "protected named RHS fault lost source binder"
      cells initial final [(.word, some seven), (.word, some seven), (mapType, none),
        (.word, none), (.word, some seven), (.word, some seven), (.integer, some (.integer 7))] "failing"
    | other => throw (IO.userError s!"protected named RHS fault: {reprStr other}")
    match ← finish compiled "keyFail" [seven] fuel initial with
    | .fault (.uninitializedLocal actual) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == keyGap) "protected named key fault lost source binder"
      cells initial final [(.word, some seven), (.word, some seven), (mapType, none), (.word, none)] "keyFail"
    | other => throw (IO.userError s!"protected named key fault: {reprStr other}")
  IO.println "protected named places: bindings/restore, guarded key/RHS, writeback/raw metadata, caller histories/captures, earlier faults and resume GREEN"
end Tests.SourceCoreProtectedNamedPlaces
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedWhileEdges
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Concrete protected loop-edge consumers and Core-only regressions.
Conditions and lexical bodies call real named code while mutable source cells,
raw duplicate mappings and a pre-existing captured closure remain observable.
Whole while iteration/finish meaning is a later unit. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedWhileEdges
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open TypedScopedStatements (Executes)
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

open NamedWhileEdges
variable {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition child/body meaning follows from concrete accepted named Trees. -/
theorem concrete_condition_preserves
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  NamedWhileEdges.condition_preserves functions extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree found valid agrees state trace

include extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Actual condition completion reconstructs its source trace and retained entry. -/
theorem concrete_condition_reflects
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  NamedWhileEdges.condition_reflects functions extension faithful observations runtimeViews evidence uninitialized missing bodyUninitialized bodyMissing tree found valid agrees state evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem concrete_body_preserves
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  NamedWhileEdges.body_preserves functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree valid agrees reference state trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem concrete_body_reflects
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  NamedWhileEdges.body_reflects functions definitions registered extension faithful observations runtimeViews evidence unique owners uninitialized missing bodyUninitialized bodyMissing tree valid agrees reference state evaluated

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 2) { return true; } let gap: Word; return gap == value; }",
  "function count(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { { let delta = next(0); raw[next(0)] += copied(delta); } if (less(index, 1)) { index += next(0); } else { index += next(0); } } return copied(index + raw[next(0)]); }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (stopOrFail(index)) { raw[next(0)] += copied(4); index += next(0); } return copied(99); }",
  "function bodyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { raw[next(0)] += copied(4); index += next(0); bad(index); } return copied(99); }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 3)) { raw[next(0)] += copied(4); return copied(raw[next(0)]); } return bad(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 0)) { bad(index); } return copied(raw[next(0)]); }",
  "function unitLoop(raw: mapping(Word => Word), seed: Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 2)) { raw[next(0)] += copied(1); index += next(0); copied(index); } }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected while resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected while fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected while exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected while inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected while missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected while raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected while missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected while writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected while captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected while captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected while captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected while lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let names := ["count", "conditionFault", "bodyFault", "early", "zero", "unitLoop"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named while edges" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let conditionGap ← gapBinder compiled "stopOrFail"
  let bodyGap ← gapBinder compiled "bad"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("count",16,13,3), ("early",14,14,0), ("zero",10,10,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected while result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected while success {name}: {reprStr other}")
    for (name, fault, updated, counter) in [("conditionFault",conditionGap,18,2), ("bodyFault",bodyGap,14,1)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == fault) s!"protected while fault site {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected while failure {name}: {reprStr other}")
    let completed ← finish compiled "unitLoop" fuel initial
    match completed with
    | .done .unit final =>
      observe initial final "unitLoop" 12 2
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected while Unit body: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected while resume changed exact source observations"
  IO.println "protected named while edges: concrete condition/body consumers, actual hidden slots, raw duplicate mapping writes, captured snapshots, first faults/Unit/early return and resume GREEN"

end Tests.SourceCoreProtectedNamedWhileEdges
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedNamedWhileStatements
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.Certificate.mk
/-! Whole finite protected while consumers with no external runtime child/body
meaning contract. Actual checked Core runs cover many frame-restored iterations,
raw mapping duplicate order, captured snapshots, first faults and real resume.
Break/continue and nested loops are outside the concrete body profile here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreProtectedNamedWhileStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

variable {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition and body runtime obligations are discharged by the concrete
named Trees. The actual native head type is retained as a separate static fact. -/
theorem concrete_whole_preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadPreserves functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  exact NamedWhileStatements.preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing found form conditionFound conditionTree bodyTree typed

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Native completion reconstructs the independent source head and its effects.
Successful body control excludes faults by static Tree inversion, rather than
by a caller-supplied body execution or universal semantic contract. -/
theorem concrete_whole_reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadReflects functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  exact NamedWhileStatements.reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing found form conditionFound conditionTree bodyTree typed

end Static

private def content : String := String.intercalate "\n" [
  "function next(value: Word) returns (Word) { return value + 1; }",
  "function copied(value: Word) returns (Word) { let local = value; return local; }",
  "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
  "function bad(value: Word) returns (Word) { let gap: Word; return gap; }",
  "function stopOrFail(value: Word) returns (Bool) { if (value < 4) { return true; } let gap: Word; return gap == value; }",
  "function count(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { { let delta = next(0); raw[next(0)] += copied(delta); } if (less(index, 1)) { index += next(0); } else { index += next(0); } } return copied(index + raw[next(0)]); }",
  "function conditionFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (stopOrFail(index)) { raw[next(0)] += copied(4); index += next(0); } return copied(99); }",
  "function bodyFault(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { raw[next(0)] += copied(4); index += next(0); bad(index); } return copied(99); }",
  "function early(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 7)) { raw[next(0)] += copied(4); return copied(raw[next(0)]); } return bad(99); }",
  "function zero(raw: mapping(Word => Word), seed: Word) returns (Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 0)) { bad(index); } return copied(raw[next(0)]); }",
  "function unitLoop(raw: mapping(Word => Word), seed: Word) { let saved: function(Word) returns (Word) = lam(value: Word) -> Word { return seed + value; }; let index = 0; while (less(index, 5)) { raw[next(0)] += copied(1); index += next(0); copied(index); } }"
]

private def wordValue (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def table (n : Nat) : SourceTypedRuntime.Value :=
  .mapping (.comptime .word) (.comptime .word) [(wordValue 1, wordValue n), (wordValue 1, wordValue 91)]

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [table 10, wordValue 7] fuel initial
  pure (← SourceCoreUnifiedCorpusSupport.get s!"protected finite while resume {name}" (first.resume 400000)).observation

private def gapBinder (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) : IO Resolved.LocalId := do
  let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
  let specialized ← SourceCoreUnifiedCorpusSupport.get "protected finite while fault binder"
    (SourceCompilationPlan.exactSpecialization compiled.validationPlan key)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == "gap") with
  | [binder] => pure binder.id
  | _ => throw (IO.userError "protected finite while exact fault binder missing")

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected finite while inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected finite while missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected finite while raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected finite while missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected finite while writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected finite while captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected finite while captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected finite while captured snapshot locations changed {name}"
  | other => throw (IO.userError s!"protected finite while lost stored captured closure {name}: {reprStr other}")

def run : IO Unit := do
  let names := ["count", "conditionFault", "bodyFault", "early", "zero", "unitLoop"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "protected named finite while" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (wordValue 819)⟩]}
  let conditionGap ← gapBinder compiled "stopOrFail"
  let bodyGap ← gapBinder compiled "bad"
  let mut baseline : List String := []
  for fuel in [400000, 0, 43, 211] do
    let mut current : List String := []
    for (name, result, updated, counter) in [("count",24,17,7), ("early",14,14,0), ("zero",10,10,0)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .done actual final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (reprStr actual == reprStr (wordValue result)) s!"protected finite while result {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected finite while success {name}: {reprStr other}")
    for (name, fault, updated, counter) in [("conditionFault",conditionGap,26,4), ("bodyFault",bodyGap,14,1)] do
      let completed ← finish compiled name fuel initial
      match completed with
      | .fault (.uninitializedLocal actual) final =>
        SourceCoreUnifiedCorpusSupport.assertTrue (actual == fault) s!"protected finite while fault site {name}"
        observe initial final name updated counter
        current := current ++ [reprStr completed]
      | other => throw (IO.userError s!"protected finite while failure {name}: {reprStr other}")
    let completed ← finish compiled "unitLoop" fuel initial
    match completed with
    | .done .unit final =>
      observe initial final "unitLoop" 15 5
      current := current ++ [reprStr completed]
    | other => throw (IO.userError s!"protected finite while Unit body: {reprStr other}")
    if fuel == 400000 then baseline := current
    else SourceCoreUnifiedCorpusSupport.assertTrue (current == baseline) "protected finite while resume changed exact source observations"
  IO.println "protected named finite while: whole-head preservation/reflection, retained entry, repeated raw mapping/capture snapshots, condition/body faults, Unit/early return and real resume GREEN"


end Tests.SourceCoreProtectedNamedWhileStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedStateSequence
/-! Effectful consumers of the existing ordered sequence induction. The head
lazily initializes an ordinary mapping cell; the next read observes that write.
Records are determined by the actual initialized source/native cells, so the
original witness cannot be reused at the reached heap. Repeated labels remain
ordered list entries. A nonmapping uninitialized read exercises tail failure. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
namespace Tests.SourceCoreProtectedStateSequence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof GenericExpressionMeaning DataExpressionSequence
open ProtectedDataExpressionSequence ProtectedStateTransition

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"protected_sequence", by decide⟩], by decide⟩⟩, 0⟩
private def id (n : Nat) : ExpressionId := ⟨⟨owner, n⟩⟩
private def binder (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "protected_sequence.solc"⟩, 0, 1⟩
private def mapType : TypeSystem.Ty := .mapping .word .word
private def emptyMap : Dynamic.Value := .mapping .word .word []
private def token : Word := Word.ofNatModulo 7
private def payload : Value := .word (Word.ofNatModulo 42)
private def sourceNode (n : Nat) : ExpressionNode := {
  id := id n, span, type := if n = 2 then .word else mapType,
  form := .reference "local" (.local (binder n)) }
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0), .expression (id 1), .expression (id 2)],
  nodes := [.expression (sourceNode 0), .expression (sourceNode 1), .expression (sourceNode 2)] }
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def projects : GenericHeap.Projection := fun source native =>
  native = .word ∧ (source = mapType ∨ source = .word)
private def model : GenericHeap.PayloadModel catalog projects [] where
  Represents _ _ source value native type :=
    source = mapType ∧ value = emptyMap ∧ native = payload ∧ type = .word
  projection := by rintro _ _ _ _ _ _ ⟨rfl, _, _, rfl⟩; exact ⟨rfl, Or.inl rfl⟩
  runtime_hasType := by rintro _ _ _ _ _ _ ⟨_, _, rfl, rfl⟩; exact .word
  extend := fun represented _ _ => represented
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def scheme (type : TypeSystem.Ty) : TypeSystem.Scheme := { quantified := [], body := type }
private def context : SourceSemantics.Context := {
  Context.ofSignatures signatures with
  locals := [(binder 0, scheme mapType), (binder 1, scheme mapType), (binder 2, scheme .word)] }
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnv : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def scope : SourceCoreLocalCell.Scope := [(binder 0, .word), (binder 1, .word), (binder 2, .word)]
private def world : StoreTyping := List.replicate 3 (OptionalCell.cellType .word)
private def mapping : LocationMap := [0, 1, 2]
private def canonical : Environment := [.cellRef (OptionalCell.cellType .word) 0,
  .cellRef (OptionalCell.cellType .word) 1, .cellRef (OptionalCell.cellType .word) 2]
private structure Stage where
  first : Bool
  second : Bool
private def heapAt (stage : Stage) : Dynamic.Heap := ⟨[
  ⟨mapType, if stage.first then some emptyMap else none, none⟩,
  ⟨mapType, if stage.second then some emptyMap else none, none⟩,
  ⟨.word, none, none⟩]⟩
private def storeAt (stage : Stage) : Store := [
  if stage.first then .inRight .unit payload else .inLeft .word .unit,
  if stage.second then .inRight .unit payload else .inLeft .word .unit,
  .inLeft .word .unit]
private def indexAt (stage : Stage) : Index := ⟨scope, mapping, world, heapAt stage, storeAt stage, canonical⟩
private def recordsAt (stage : Stage) : List Nat :=
  (if stage.first then [42] else []) ++ (if stage.second then [42] else [])
private def Advance (before after : Stage) : Prop :=
  (before.first = true → after.first = true) ∧ (before.second = true → after.second = true)
private def protocol : Protocol (List Nat) where
  State index := { stage : Stage // indexAt stage = index }
  records state := recordsAt state.val
  Relates first last := Advance first.val last.val
  refl _ := ⟨fun h => h, fun h => h⟩
  trans first last := ⟨fun value => last.1 (first.1 value), fun value => last.2 (first.2 value)⟩
private def atStage (stage : Stage) : protocol.State (indexAt stage) := ⟨stage, rfl⟩
private def nextStage (stage : Stage) (slot : Fin 3) : Stage :=
  if slot.val = 0 then ⟨true, stage.second⟩ else if slot.val = 1 then ⟨stage.first, true⟩ else stage
private def codeAt (slot : Fin 3) : SourceCoreBasic.LoweredExpr := ⟨.word,
  if slot.val = 2 then OptionalCell.read .word (.var 2) token
  else SourceCoreCompatibleDataExpressions.readMapping (.var slot.val) (.word (Word.ofNatModulo 42))⟩
private def faultRep : FaultRep := fun reason value => reason = .uninitializedLocation ⟨2⟩ ∧ value = token
private inductive Child : Certificate where
  | read (slot : Fin 3) : Child scope (id slot.val) (codeAt slot)

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, sourceNode, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]
private theorem found (slot : Fin 3) : source.lookupExpression? (id slot.val) = some (sourceNode slot.val) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk] <;> decide
private theorem mapped_index {n target : Nat} (found : mapping[n]? = some target) : n = target := by
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  change n < 3 at bounded
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp [mapping] at found <;> omega
private theorem environment_exact {admin environment stage}
    (represented : DataHeap.EnvRepresents catalog mapping world admin scope environment canonical [])
    (locals : Dynamic.EnvironmentAgrees (heapAt stage) context.locals environment) : environment = sourceEnv := by
  cases locals with
  | @cons _ _ _ _ location0 _ _ _ _ tail =>
    cases tail with
    | @cons _ _ _ _ location1 _ _ _ _ tail =>
      cases tail with
      | @cons _ _ _ _ location2 _ _ _ _ tail =>
        cases tail
        cases represented with
        | internal _ absent _ => exact (absent location0 .head).elim
        | cons first rest =>
          cases rest with
          | internal _ absent _ => exact (absent location1 .head).elim
          | cons second rest =>
            cases rest with
            | internal _ absent _ => exact (absent location2 .head).elim
            | cons third rest =>
              cases rest
              have zero := mapped_index first.mapped
              have one := mapped_index second.mapped
              have two := mapped_index third.mapped
              cases location0; cases location1; cases location2
              simp only at zero one two
              subst_vars
              rfl
private theorem source_lookup (slot : Fin 3) : Dynamic.Environment.LooksUp sourceEnv (binder slot.val) ⟨slot.val⟩ := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk]
  · exact .head
  · exact .tail (by decide) .head
  · exact .tail (by decide) (.tail (by decide) .head)
private theorem source_read (stage : Stage) (slot : Fin 3) :
    Dynamic.Heap.Reads (heapAt stage) ⟨slot.val⟩
      (if slot.val = 2 then ⟨.word, none, none⟩ else
        ⟨mapType, if (if slot.val = 0 then stage.first else stage.second) then some emptyMap else none, none⟩) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp only [Fin.val_mk]
  · exact .intro .head
  · exact .intro (.tail .head)
  · exact .intro (.tail (.tail .head))

private theorem mapping_cell (flag : Bool) (locations : LocationMap) (typing : StoreTyping) :
    GenericHeap.CellRepresents model locations typing
      ⟨mapType, if flag then some emptyMap else none, none⟩
      (if flag then .inRight .unit payload else .inLeft .word .unit) .word := by
  cases flag
  · exact .uninitialized ⟨rfl, Or.inl rfl⟩
  · exact .initialized ⟨rfl, rfl, rfl, rfl⟩
private theorem heap_rep (stage : Stage) :
    GenericHeap.HeapRepresents model mapping world (heapAt stage) (storeAt stage) := by
  have first := (GenericHeap.HeapRepresents.empty (model := model)).allocate
    (mapping_cell stage.first [] []) Dynamic.Heap.Allocates.append
  have second := first.1.allocate
    (mapping_cell stage.second _ _) Dynamic.Heap.Allocates.append
  have third := second.1.allocate
    (GenericHeap.CellRepresents.uninitialized (model := model) ⟨rfl, Or.inr rfl⟩) Dynamic.Heap.Allocates.append
  exact third.1
private def sourceOutcome (slot : Fin 3) : Dynamic.ExpressionOutcome :=
  if slot.val = 2 then .fault (.uninitializedLocation ⟨2⟩) else .value emptyMap
private def coreOutcome (slot : Fin 3) : Value :=
  if slot.val = 2 then .inLeft .word (.word token) else .inRight .word payload
private def traceSize (slot : Fin 3) : Nat := if slot.val = 2 then 2 else 3
private theorem advance (stage : Stage) (slot : Fin 3) : Advance stage (nextStage stage slot) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl <;> simp [Advance, nextStage]
private theorem raw_source (stage : Stage) (slot : Fin 3) :
    ExpressionTraceAt program (traceSize slot) context [] source sourceEnv (heapAt stage)
      (id slot.val) (sourceOutcome slot) (heapAt (nextStage stage slot)) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · cases first : stage.first
    · refine .value (.intro (lookupExpression?_sound (found ⟨0, by decide⟩)) ?_ .nil)
      exact .localEmptyMapping rfl (source_lookup ⟨0, by decide⟩)
        (source_read stage ⟨0, by decide⟩) rfl rfl (by simp [first])
        (.intro (source_read stage ⟨0, by decide⟩) (by simpa [heapAt, nextStage, first, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
          (Dynamic.Heap.CellsWrite.head : Dynamic.Heap.CellsWrite (heapAt stage).cells 0
            ⟨mapType, some emptyMap, none⟩ (heapAt ⟨true, stage.second⟩).cells)))
    · refine .value (.intro (lookupExpression?_sound (found ⟨0, by decide⟩)) ?_ .nil)
      simpa [heapAt, nextStage, first, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
        (SourceExecutionSize.ExpressionFormEvaluates.local (program := program) (context := context)
          (evidence := []) (source := source) (value := emptyMap) (name := "local") (requirements := []) (coercions := []) rfl (source_lookup ⟨0, by decide⟩)
          (source_read stage ⟨0, by decide⟩) rfl (by simp [first]))
  · cases second : stage.second
    · refine .value (.intro (lookupExpression?_sound (found ⟨1, by decide⟩)) ?_ .nil)
      exact .localEmptyMapping rfl (source_lookup ⟨1, by decide⟩)
        (source_read stage ⟨1, by decide⟩) rfl rfl (by simp [second])
        (.intro (source_read stage ⟨1, by decide⟩) (by simpa [heapAt, nextStage, second, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
          (Dynamic.Heap.CellsWrite.tail Dynamic.Heap.CellsWrite.head : Dynamic.Heap.CellsWrite (heapAt stage).cells 1
            ⟨mapType, some emptyMap, none⟩ (heapAt ⟨stage.first, true⟩).cells)))
    · refine .value (.intro (lookupExpression?_sound (found ⟨1, by decide⟩)) ?_ .nil)
      simpa [heapAt, nextStage, second, emptyMap, sourceNode, SourceExecutionSize.stepSize] using
        (SourceExecutionSize.ExpressionFormEvaluates.local (program := program) (context := context)
          (evidence := []) (source := source) (value := emptyMap) (name := "local") (requirements := []) (coercions := []) rfl (source_lookup ⟨1, by decide⟩)
          (source_read stage ⟨1, by decide⟩) rfl (by simp [second]))
  · exact .fault (.form (lookupExpression?_sound (found ⟨2, by decide⟩))
      (.localUninitialized (owned := []) rfl (source_lookup ⟨2, by decide⟩)
        (source_read stage ⟨2, by decide⟩) rfl rfl (by intro ⟨_, _, impossible⟩; cases impossible)))
private theorem native (stage : Stage) (slot : Fin 3) {actual : Environment} {ξ : Renaming}
    (layout : EnvironmentsAgree ξ canonical actual) :
    Evaluates actual (storeAt stage) ((codeAt slot).expression.rename ξ)
      (coreOutcome slot) (storeAt (nextStage stage slot)) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · change Evaluates actual (storeAt stage)
      ((SourceCoreCompatibleDataExpressions.readMapping (.var 0) (.word (Word.ofNatModulo 42))).rename ξ)
      (.inRight .word payload) (storeAt ⟨true, stage.second⟩)
    rw [CompatibleExpressionReadCompletion.mapping_rename (CompatibleMapping.VirtualRoot.Quoted.word (Word.ofNatModulo 42))]
    cases first : stage.first
    · simpa [storeAt, payload, first, List.set] using
        SourceCoreCompatibleDataExpressions.readMapping_initializes (payload := .word)
          (before := storeAt stage) (middle := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 0) rfl)) (by simp [storeAt, Store.read?, first])
          (by simpa [Expr.weakenAt, Expr.rename, payload] using
            (Core.Evaluates.word : Evaluates _ (storeAt stage) (Expr.word (Word.ofNatModulo 42))
              (.word (Word.ofNatModulo 42)) (storeAt stage)))
          (by simp [storeAt, Store.read?, first])
    · simpa [storeAt, first] using
        SourceCoreCompatibleDataExpressions.readMapping_present (payload := .word)
          (before := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 0) rfl)) (by simp [storeAt, Store.read?, first])
  · change Evaluates actual (storeAt stage)
      ((SourceCoreCompatibleDataExpressions.readMapping (.var 1) (.word (Word.ofNatModulo 42))).rename ξ)
      (.inRight .word payload) (storeAt ⟨stage.first, true⟩)
    rw [CompatibleExpressionReadCompletion.mapping_rename (CompatibleMapping.VirtualRoot.Quoted.word (Word.ofNatModulo 42))]
    cases second : stage.second
    · simpa [storeAt, payload, second, List.set] using
        SourceCoreCompatibleDataExpressions.readMapping_initializes (payload := .word)
          (before := storeAt stage) (middle := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 1) rfl)) (by simp [storeAt, Store.read?, second])
          (by simpa [Expr.weakenAt, Expr.rename, payload] using
            (Core.Evaluates.word : Evaluates _ (storeAt stage) (Expr.word (Word.ofNatModulo 42))
              (.word (Word.ofNatModulo 42)) (storeAt stage)))
          (by simp [storeAt, Store.read?, second])
    · simpa [storeAt, second] using
        SourceCoreCompatibleDataExpressions.readMapping_present (payload := .word)
          (before := storeAt stage) (after := storeAt stage) (mapping := payload)
          (.var (layout (index := 1) rfl)) (by simp [storeAt, Store.read?, second])
  · change Evaluates actual (storeAt stage) ((OptionalCell.read .word (.var 2) token).rename ξ)
      (.inLeft .word (.word token)) (storeAt stage)
    simpa [OptionalCell.read, LanguageResult.failure, LanguageResult.success, Expr.rename, Renaming.lift] using
      OptionalCell.read_failure token (.var (layout (index := 2) rfl)) (by simp [storeAt, Store.read?])

private theorem metadata (first last : Stage) : Dynamic.HeapMetadataExtend (heapAt first) (heapAt last) := by
  intro location cell read
  cases location
  cases read with
  | intro read =>
    cases read with
    | head => exact ⟨_, .intro .head, rfl, rfl⟩
    | tail read =>
      cases read with
      | head => exact ⟨_, .intro (.tail .head), rfl, rfl⟩
      | tail read =>
        cases read with
        | head => exact ⟨_, .intro (.tail (.tail .head)), rfl, rfl⟩
        | tail read => cases read
private theorem frame (first last : Stage) : AdministrativePreserved mapping (storeAt first) mapping (storeAt last) := by
  intro location absent bounded
  change location < 3 at bounded
  change Nat at location
  have choices : location = 0 ∨ location = 1 ∨ location = 2 := by
    have small : location ≤ 2 := Nat.le_of_lt_succ bounded
    rcases Nat.le_succ_iff.mp small with small | last
    · rcases Nat.le_succ_iff.mp small with zero | one
      · exact Or.inl (Nat.eq_zero_of_le_zero zero)
      · exact Or.inr (Or.inl one)
    · exact Or.inr (Or.inr last)
  rcases choices with rfl | rfl | rfl <;> exact (absent (by decide)).elim
private theorem result (_stage : Stage) (slot : Fin 3) :
    ResultRepresents model mapping world (sourceNode slot.val).type (codeAt slot).type faultRep
      (sourceOutcome slot) (coreOutcome slot) := by
  rcases slot with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact .value ⟨rfl, rfl, rfl, rfl⟩
  · exact .value ⟨rfl, rfl, rfl, rfl⟩
  · exact .fault ⟨rfl, rfl⟩
private theorem child_preserves (size : Nat) :
    Stateful.ExpressionPreservesAt protocol size model program context [] source Child faultRep := by
  intro selectedScope expression lowered generated foundNode foundNodeEq locations typing admin environment oldCanonical
    actual actualContext before store ξ outcome after environments heaps locals layout actualTyped initial trace
  cases generated with
  | read slot =>
    have sameNode : foundNode = sourceNode slot.val := Option.some.inj (foundNodeEq.symm.trans (found slot))
    subst foundNode
    rcases initial with ⟨stage, sameIndex⟩
    have sameMap := congrArg Index.mapping sameIndex
    have sameWorld := congrArg Index.world sameIndex
    have sameHeap := congrArg Index.heap sameIndex
    have sameStore := congrArg Index.store sameIndex
    have sameCanonical := congrArg Index.canonical sameIndex
    dsimp [indexAt] at sameMap sameWorld sameHeap sameStore sameCanonical
    subst locations; subst typing; subst before; subst store; subst oldCanonical
    have sameEnvironment := environment_exact environments locals
    subst environment
    have same := CompatibleExpressionReads.source_outcome_unique unique (lookupExpression?_sound (found slot))
      (show (sourceNode slot.val).form = .reference "local" (.local (binder slot.val)) from rfl) rfl
      (source_lookup slot) (source_read stage slot) (by split <;> rfl) trace.sound (raw_source stage slot).sound
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨coreOutcome slot, storeAt (nextStage stage slot), mapping, world, native stage slot layout,
      result stage slot, heap_rep (nextStage stage slot), .refl _, .refl _, frame stage _, metadata stage _,
      ⟨atStage (nextStage stage slot), advance stage slot⟩⟩
private theorem child_reflects (size : Nat) :
    Stateful.ExpressionReflectsAt protocol size model program context [] source Child faultRep := by
  intro selectedScope expression lowered generated foundNode foundNodeEq locations typing admin environment oldCanonical
    actual actualContext before store ξ value finalStore environments heaps locals layout actualTyped initial evaluated
  cases generated with
  | read slot =>
    have sameNode : foundNode = sourceNode slot.val := Option.some.inj (foundNodeEq.symm.trans (found slot))
    subst foundNode
    rcases initial with ⟨stage, sameIndex⟩
    have sameMap := congrArg Index.mapping sameIndex
    have sameWorld := congrArg Index.world sameIndex
    have sameHeap := congrArg Index.heap sameIndex
    have sameStore := congrArg Index.store sameIndex
    have sameCanonical := congrArg Index.canonical sameIndex
    dsimp [indexAt] at sameMap sameWorld sameHeap sameStore sameCanonical
    subst locations; subst typing; subst before; subst store; subst oldCanonical
    have sameEnvironment := environment_exact environments locals
    subst environment
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (native stage slot layout)
    exact ⟨traceSize slot, sourceOutcome slot, heapAt (nextStage stage slot), mapping, world,
      raw_source stage slot, result stage slot, heap_rep (nextStage stage slot), .refl _, .refl _,
      frame stage _, metadata stage _, ⟨atStage (nextStage stage slot), advance stage slot⟩⟩

private def start : Stage := ⟨false, false⟩
private def middle : Stage := ⟨true, false⟩
private def finish : Stage := ⟨true, true⟩
private theorem environments : DataHeap.EnvRepresents catalog mapping world [] scope sourceEnv canonical [] :=
  .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil .nil)))
private theorem locals (stage : Stage) : Dynamic.EnvironmentAgrees (heapAt stage) context.locals sourceEnv :=
  .cons (source_read stage ⟨0, by decide⟩) rfl (.ordinary rfl rfl)
    (.cons (source_read stage ⟨1, by decide⟩) rfl (.ordinary rfl rfl)
      (.cons (source_read stage ⟨2, by decide⟩) rfl (.ordinary rfl rfl) .nil))
private theorem layout : EnvironmentsAgree Renaming.id canonical canonical := fun same => same
private theorem actualTyped : RuntimeEnvironmentHasTypes world canonical (SourceCoreLocalCell.coreContext scope) [] :=
  environments.runtime_hasTypes
private theorem stage_of_heap {first last : Stage} (same : heapAt first = heapAt last) : first = last := by
  rcases first with ⟨a, b⟩
  rcases last with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [heapAt] <;> rfl
private theorem records_from_heap {index : Index} (state : protocol.State index) (stage : Stage)
    (same : index.heap = heapAt stage) : protocol.records state = recordsAt stage := by
  obtain ⟨earlier, found⟩ := state
  have equal := stage_of_heap ((congrArg Index.heap found).trans same)
  cases equal
  rfl
private theorem source_success : SourceExecutionSize.ExpressionsEvaluate program 9 context [] source sourceEnv
    (heapAt start) [id 0, id 1] [emptyMap, emptyMap] (heapAt finish) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨1, by decide⟩
  cases first with
  | value first =>
    cases last with
    | value last => exact .cons first (.cons last .nil)
private theorem source_fault : SourceExecutionSize.ExpressionsFault program 7 context [] source sourceEnv
    (heapAt start) [id 0, id 2] (.uninitializedLocation ⟨2⟩) (heapAt middle) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨2, by decide⟩
  cases first with
  | value first =>
    cases last with
    | fault last => exact .tail first (.head last)
private theorem source_duplicate : SourceExecutionSize.ExpressionsEvaluate program 9 context [] source sourceEnv
    (heapAt start) [id 0, id 0] [emptyMap, emptyMap] (heapAt middle) := by
  have first := raw_source start ⟨0, by decide⟩
  have last := raw_source middle ⟨0, by decide⟩
  cases first with
  | value first =>
    cases last with
    | value last => exact .cons first (.cons last .nil)
private theorem pair_tree (last : Fin 3) : DataExpressionSequence.Tree source Child scope
    [id 0, id last.val] [(sourceNode 0).type, (sourceNode last.val).type]
    [codeAt ⟨0, by decide⟩, codeAt last] :=
  .cons (found ⟨0, by decide⟩) (.read ⟨0, by decide⟩) (.single (found last) (.read last))
private theorem native_pair (last : Fin 3) :
    Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt last]).expression
      (if last.val = 2 then .inLeft (.product .word .word) (.word token)
        else .inRight .word (.pair payload payload)) (storeAt (nextStage middle last)) := by
  have first := native start ⟨0, by decide⟩ layout
  have lastEval := native middle last (agree_prefix layout payload)
  rw [rename_prefix] at lastEval
  simp only [Expr.rename_id] at first lastEval
  rcases last with ⟨n, bounded⟩
  have choices : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact LocalSequence.pair_success _ _ first lastEval
  · exact LocalSequence.pair_success _ _ first lastEval
  · exact LocalSequence.pair_right_failure _ _ first lastEval

/-- The head's list append is tied to real source/native initialization. -/
theorem head_appends_42 :
    ExpressionTraceAt program 3 context [] source sourceEnv (heapAt start) (id 0)
      (.value emptyMap) (heapAt middle) ∧
    Evaluates canonical (storeAt start) (codeAt ⟨0, by decide⟩).expression
      (.inRight .word payload) (storeAt middle) ∧
    protocol.records (atStage middle) = protocol.records (atStage start) ++ [42] ∧
    protocol.Relates (atStage start) (atStage middle) := by
  exact ⟨raw_source start ⟨0, by decide⟩, by simpa [coreOutcome, nextStage, start, middle] using native start ⟨0, by decide⟩ layout,
    rfl, advance start ⟨0, by decide⟩⟩
/-- Reusing the original state after the head would contradict its real heap index. -/
theorem original_witness_cannot_reach_middle :
    ¬ indexAt start = indexAt middle := by
  intro same
  have impossible := stage_of_heap (congrArg Index.heap same)
  cases impossible

/-- The tail input at the head's reached index is exactly its concrete
initialization witness, including the [42] observation. -/
theorem middle_witness_is_exact (reached : protocol.State (indexAt middle)) :
    reached = atStage middle := by
  apply Subtype.ext
  exact stage_of_heap (congrArg Index.heap reached.property)

/-- At the exact inclusive source budget, both effects survive in order. The
identical labels come from different real mapping initialization writes. -/
theorem successful_cons_preserves_duplicate_records :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt finish, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, mapType]
        [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩] faultRep (.ok [emptyMap, emptyMap]) value ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42, 42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 9 (pair_tree ⟨1, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.values source_success) (Nat.le_refl 9)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, represented, related,
    records_from_heap final finish rfl⟩
/-- A tail failure retains the witness produced by the successful head. -/
theorem tail_fault_retains_head_record :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt middle, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, .word]
        [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩] faultRep (.error (.uninitializedLocation ⟨2⟩)) value ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 7 (pair_tree ⟨2, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.fault source_fault) (Nat.le_refl 7)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, represented, related,
    records_from_heap final middle rfl⟩
/-- Duplicate expression IDs are evaluated in sequence; the second read sees
the initialized cell and creates no second record for that same write. -/
theorem repeated_child_uses_reached_heap :
    ∃ value finalStore finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, heapAt middle, finalStore, canonical⟩,
      Evaluates canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨0, by decide⟩]).expression value finalStore ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.preserves_bounded protocol 9 (pair_tree ⟨0, by decide⟩)
      (fun size _ => child_preserves size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (.values source_duplicate) (Nat.le_refl 9)
  obtain ⟨final, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, final, by simpa using evaluated, related,
    records_from_heap final middle rfl⟩

private theorem stage_of_store {first last : Stage} (same : storeAt first = storeAt last) : first = last := by
  rcases first with ⟨a, b⟩
  rcases last with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [storeAt] <;> rfl
private theorem records_from_store {index : Index} (state : protocol.State index) (stage : Stage)
    (same : index.store = storeAt stage) : protocol.records state = recordsAt stage := by
  obtain ⟨earlier, found⟩ := state
  have equal := stage_of_store ((congrArg Index.store found).trans same)
  cases equal
  rfl
/-- Native completion, measured strictly below its budget, reconstructs a
source trace and the two records fixed by its real final store. -/
theorem successful_cons_reflects_duplicate_records :
    ∃ nativeSize sourceSize outcome after finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, after, storeAt finish, canonical⟩,
      EvaluationSize nativeSize canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression
        (.inRight .word (.pair payload payload)) (storeAt finish) ∧
      nativeSize < nativeSize + 1 ∧
      TraceAt program sourceSize context [] source sourceEnv (heapAt start) [id 0, id 1] outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld [mapType, mapType]
        [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩] faultRep outcome (.inRight .word (.pair payload payload)) ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42, 42] := by
  have completed : Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨1, by decide⟩]).expression
      (.inRight .word (.pair payload payload)) (storeAt finish) := native_pair ⟨1, by decide⟩
  obtain ⟨nativeSize, sized⟩ := evaluation_has_size completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.reflects_bounded protocol (nativeSize + 1) (pair_tree ⟨1, by decide⟩)
      (fun size _ => child_reflects size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (by simpa using sized) (Nat.lt_succ_self nativeSize)
  obtain ⟨final, related⟩ := transition
  exact ⟨nativeSize, sourceSize, outcome, after, finalMap, finalWorld, final, sized, Nat.lt_succ_self nativeSize,
    trace, represented, related, records_from_store final finish rfl⟩
/-- A real native right-branch fault reflects to the same source failure and
retains the record from the earlier initialization write. -/
theorem tail_fault_reflects_head_record :
    ∃ nativeSize sourceSize after finalMap finalWorld, ∃ final : protocol.State
        ⟨scope, finalMap, finalWorld, after, storeAt middle, canonical⟩,
      EvaluationSize nativeSize canonical (storeAt start)
        (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression
        (.inLeft (.product .word .word) (.word token)) (storeAt middle) ∧
      nativeSize < nativeSize + 1 ∧
      TraceAt program sourceSize context [] source sourceEnv (heapAt start) [id 0, id 2]
        (.error (.uninitializedLocation ⟨2⟩)) after ∧
      protocol.Relates (atStage start) final ∧ protocol.records final = [42] := by
  have completed : Evaluates canonical (storeAt start)
      (SourceCoreCalls.packArguments [codeAt ⟨0, by decide⟩, codeAt ⟨2, by decide⟩]).expression
      (.inLeft (.product .word .word) (.word token)) (storeAt middle) := native_pair ⟨2, by decide⟩
  obtain ⟨nativeSize, sized⟩ := evaluation_has_size completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    Stateful.reflects_bounded protocol (nativeSize + 1) (pair_tree ⟨2, by decide⟩)
      (fun size _ => child_reflects size) environments (heap_rep start) (locals start) layout actualTyped
      (atStage start) (by simpa using sized) (Nat.lt_succ_self nativeSize)
  obtain ⟨final, related⟩ := transition
  cases represented with
  | fault matched =>
    obtain ⟨rfl, _⟩ := matched
    exact ⟨nativeSize, sourceSize, after, finalMap, finalWorld, final, sized, Nat.lt_succ_self nativeSize,
      trace, related, records_from_store final middle rfl⟩

#print axioms child_preserves
#print axioms child_reflects
#print axioms raw_source
#print axioms native_pair
#print axioms head_appends_42
#print axioms original_witness_cannot_reach_middle
#print axioms middle_witness_is_exact
#print axioms successful_cons_preserves_duplicate_records
#print axioms tail_fault_retains_head_record
#print axioms repeated_child_uses_reached_heap
#print axioms successful_cons_reflects_duplicate_records
#print axioms tail_fault_reflects_head_record
end Tests.SourceCoreProtectedStateSequence
end

section
-- leanmerge: from Solcore.Test.SourceCoreProtectedWhileBodyContracts
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

/-- Cells after the inert prefix: `raw`, `seed`, the snapshot of `seed` and
`raw` that `saved` takes when it is created, `saved` and `index`. -/
private def observe (initial final : SourceTypedRuntime.RuntimeState) (name : String)
    (updated counter : Nat) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"protected five-way while inert prefix changed {name}"
  let raw ← match final.heap[initial.heap.length]? with
    | some cell => pure cell | none => throw (IO.userError "protected five-way while missing root mapping")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr raw.value == reprStr (some (table updated)))
    s!"protected five-way while raw mapping/default/duplicate order changed {name}"
  let index ← match final.heap[initial.heap.length + 5]? with
    | some cell => pure cell | none => throw (IO.userError "protected five-way while missing index")
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr index.value == reprStr (some (wordValue counter)))
    s!"protected five-way while writes changed {name}"
  let snapshot := ((final.heap.drop (initial.heap.length + 2)).take 2).map (·.value)
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr snapshot == reprStr [some (wordValue 7), some (table 10)])
    s!"protected five-way while captured snapshot values changed {name}"
  match final.heap[initial.heap.length + 4]? with
  | some ⟨_, some (.closure parameters result body source owner captures _)⟩ =>
    SourceCoreUnifiedCorpusSupport.assertTrue (parameters.length == 1 && result == .word && !body.isEmpty && source.owner == owner.declaration)
      s!"protected five-way while captured closure metadata changed {name}"
    SourceCoreUnifiedCorpusSupport.assertTrue ((captures.map (fun capture => capture.2.index)) == [initial.heap.length + 2, initial.heap.length + 3])
      s!"protected five-way while captured snapshot locations changed {name}"
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
  IO.println "protected five-way while contracts: lexical embeddings, closed break/continue reflection, actual nested loops/transfer/fault effects, raw duplicate/capture snapshots and resume GREEN"

end Tests.SourceCoreProtectedWhileBodyContracts
end
