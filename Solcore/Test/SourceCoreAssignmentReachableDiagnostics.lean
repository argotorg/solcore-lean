import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Test.SourceCoreAssignmentFaultSites

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Equal assignment needs no invalid-operand diagnostic. The independent failure
relation proves that condition unreachable. Concrete recursive builtin trees
close both semantic consumers; actual checked fixtures retain RHS effects,
fault priority, diagnostic locations and resumable native execution. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace Tests.SourceCoreAssignmentReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

/-- The new condition can hold even when no fault token is interpreted. -/
theorem equal_without_interpretation :
    AssignmentOperandDiagnostics.OperandsLaw (fun _ _ => False) .equal Word.zero :=
  AssignmentOperandDiagnostics.equal _ _

/-- The omitted old condition is genuinely unavailable in this model. -/
theorem old_equal_law_false : ¬ (fun (_ : Dynamic.SemanticFault) (_ : Word) => False)
    (.invalidAssignmentOperands .equal) Word.zero := by
  intro impossible
  exact impossible

/-- Reachable compound errors still require their exact token interpretation. -/
theorem compound_requires_token (faults : FunctionCalls.FaultRep) (token : Word) :
    AssignmentOperandDiagnostics.OperandsLaw faults .add token ↔
      faults (.invalidAssignmentOperands .add) token := by
  constructor
  · intro law
    exact law none .unit (.uninitialized (by decide))
  · exact AssignmentOperandDiagnostics.of_unconditional

namespace ConcreteEqual
variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context
    (CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt)
    scope administrative ambient.definitions assignment .equal rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

  (placeMissing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (placeUninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)
include extension valid unique uninitialized missing faithful observations functionTypes environments heaps locals agrees actualTyped placeMissing placeUninitialized in
theorem preserves_fault
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target .equal rhs reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact GenericAssignmentStatements.Head.preserves_fault_reachable functions extension program evidence
    (CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    faithful observations head environments heaps locals agrees actualTyped
    (GenericAssignmentStatements.Head.ReachableErrors.equal placeMissing placeUninitialized) trace next output

include extension valid unique uninitialized missing faithful observations functionTypes environments heaps locals agrees actualTyped placeMissing placeUninitialized in
theorem reflects
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before assignment.target .equal rhs reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
        environment before assignment.target rhs updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  exact GenericAssignmentStatements.Head.reflects_reachable functions extension program evidence
    (CompatibleExpressionBuiltins.preserves functions extension faithful observations functionTypes program evidence valid unique uninitialized missing)
    (CompatibleExpressionBuiltins.reflects functions extension faithful observations functionTypes program evidence valid uninitialized missing)
    faithful observations head environments heaps locals agrees actualTyped functionTypes
    (GenericAssignmentStatements.Head.ReachableErrors.equal placeMissing placeUninitialized) completed

end ConcreteEqual

open Tests.SourceCompilerFeatureSupport in
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function plain() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root = vals[false] + 2; let later: Bool = true; return root; }",
    "function compound() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root += vals[false] + 2; let later: Bool = true; return root; }",
    "function rhsFault() returns (Word) { let root: Word; let vals: mapping(Bool => Word); let missing: Word; root += vals[false] + missing; let later: Bool = true; return root; }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def actualFault (program : CheckedProgram) (name : String)
    (expected : SourceCoreFaultSites.Diagnostic) : IO Unit := do
  let entry ← compileNamed program name
  let invocation ← entry.invoke []
  let reason ← match invocation.outcome with
    | .failed reason _ => pure reason
    | _ => throw (IO.userError "expected a language failure")
  require (reason != Word.zero && decide ((← invocation.diagnostic reason) = some expected))
    "reachable failure lost its actual diagnostic token, location or span"
  let complete ← entry.audit []
  match complete.observation with
  | .fault error _ => require (decide (error = expected.error)) "RHS failure priority changed"
  | _ => throw (IO.userError "cached Core observation did not retain the failure")
  let pending ← entry.audit [] 7
  match ← nativeObservation pending with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "small native budget did not suspend")
  let resumed ← get "fault resume" (pending.resume 300000)
  require ((← nativeObservation resumed) == (← nativeObservation complete))
    "resume changed the fault token or complete native effect prefix"
  let invocation ← entry.invoke [] {executionOptions with executionFuel := 7}
  match invocation.outcome with
  | .outOfFuel checkpoint =>
    match ← checkpoint.resume 300000 1024 with
    | .failed resumedReason session =>
      let diagnostic ← get "resumed diagnostic" (session.diagnostic entry.key resumedReason)
      require (resumedReason == reason && decide (diagnostic = some expected))
        "public checkpoint changed reachable failure diagnostics"
    | _ => throw (IO.userError "public resume lost language failure")
  | _ => throw (IO.userError "small public budget did not suspend")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  Tests.SourceCoreAssignmentFaultSites.run
  let program ← get "reachable diagnostics fixtures" (checkProgram workspace)
  let plain ← compileNamed program "plain"
  require ((← plain.run []) == scalar 2) "plain assignment failed to initialize absent root"
  plain.checkResume [] (scalar 2) 7
  plain.checkCells [] [(.word, some (scalar 2)), (.mapping .bool .word, some (.mapping .bool .word [])), (.bool, some (.bool true))]
  let function ← match program.functions.find? (·.declaration == plain.key.declaration) with
    | some function => pure function | none => throw (IO.userError "plain checked body absent")
  let table ← get "actual equal prepare" (SourceCoreAssignmentFaultSites.prepare function.typedBody 100)
  require table.sites.isEmpty "actual prepare allocated unreachable equal operands token"
  let compound ← compileNamed program "compound"
  let function ← match program.functions.find? (·.declaration == compound.key.declaration) with
    | some function => pure function | none => throw (IO.userError "compound checked body absent")
  let assignment ← match function.typedBody.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some node => pure node | none => throw (IO.userError "compound site missing")
  actualFault program "compound" {
    error := .invalidAssignmentOperands .add none (some .word),
    site := .occurrence assignment.id.occurrence, span := some assignment.span }
  compound.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word []))]
  let rhsFault ← compileNamed program "rhsFault"
  let function ← match program.functions.find? (·.declaration == rhsFault.key.declaration) with
    | some function => pure function | none => throw (IO.userError "RHS checked body absent")
  let (node, binder) ← match function.typedBody.nodes.findSome? fun
      | .expression node => match node.form with | .reference "missing" (.local binder) => some (node, binder) | _ => none
      | _ => none with
    | some result => pure result | none => throw (IO.userError "RHS missing read site absent")
  actualFault program "rhsFault" {error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span}
  rhsFault.checkCells [] [(.word, none), (.mapping .bool .word, some (.mapping .bool .word [])), (.word, none)]

end Tests.SourceCoreAssignmentReachableDiagnostics
