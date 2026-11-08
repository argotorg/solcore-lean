import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericAssignments
import Solcore.Test.SourceSemantics.CoreLowering.Foundations.EntryPoints
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ControlStatements
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Core.Safety
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForFinite
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.PrimitiveExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.Frontend.Internal.RuntimeValues
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors

/-!
# Basic statement tests

Certificates and meaning of basic statements, control, loops, for headers, assignments, primitive
expressions and scalars.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreAssignmentDiagnosticCertificates
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual prepare and compiler receipts supply tokens. Retained malformed raw
header variants below test the pure table fold only; they are not claimed to
pass the source checker or to admit executable assignments. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace Tests.SourceCoreAssignmentDiagnosticCertificates
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces GenericAssignmentStatements GenericAssignmentDiagnostics

/-- Runtime normalization alone cannot establish the raw table eligibility. -/
theorem normalized_word_is_not_raw_scalar :
    SourceCoreRawMetadata.runtimeType (.comptime .word) = .word ∧
      ¬ ((TypeSystem.Ty.comptime .word) = .word ∨ (TypeSystem.Ty.comptime .word) = .integer) := by
  constructor
  · rfl
  · decide

theorem actual_compiler_operand_diagnostic
    {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {node : StatementNode}
    {next code : Expr} {output result : Ty}
    {solved : List SolvedRequirement} {table : SourceCoreAssignmentFaultSites.Table} {first : Nat}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {owner : SourceSpecialization.SpecializationKey}
    {sourceCells : Option SourceCoreSourceCells.Allocator} {ambientDefinitions : Option DataEnvironment}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder → WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ id lowered, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope id reasonAt = .ok lowered → ∃ child,
      source.lookupExpression? id = some child ∧ certificate scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression (LanguageResult.resultType lowered.type) definitions)
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : SourceCoreAssignmentFaultSites.Certificates.OperandAt node assignment operator)
    (accepted : SourceCoreLoops.assignValue
      (SourceCoreCompatibleDataMatches.loopPolicy values solved table diagnostics owner expression sourceCells ambientDefinitions)
      fuel source scope (.occurrence node.id.occurrence) assignment operator rhs output next reasonAt = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment operator rhs,
      code = head.emit next output ∧
      (operator = .equal → head.invalid = Word.zero) ∧
      (∀ previous right, Dynamic.AssignmentOperandsInvalid operator previous right →
        ∃ diagnostic rawType, table.diagnostic? head.invalid = some diagnostic ∧
          diagnostic.error = .invalidAssignmentOperands operator none (some rawType)) := by
  obtain ⟨head, emitted, same, law⟩ := Head.of_prepared_policy unique signatures sourceTyped writable rightTyped rawProfile
    extract prepared member occurs (fun _ _ proof => proof) accepted typed
  refine ⟨head, emitted, ?_, law⟩
  intro equal
  simpa [token, equal] using same

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function header(value: Word, rhs: Word) returns (Word) { for (value += rhs, value += rhs; false; value -= rhs) { } return value; }",
    "function equalOnly(value: Word, rhs: Word) returns (Word) { value = rhs; return value; }"
  ]}]
}

private def body (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "fixture signature missing")
  match program.functions.find? (·.declaration == signature.id) with
  | some function => pure function.typedBody | none => throw (IO.userError "fixture source missing")

/-- Pure retained-record probe: preserve IDs and source order, change only raw
header target metadata. It is deliberately not a checked-program replacement. -/
private def headerTypes (source : TypedSource) (first second : TypeSystem.Ty) : TypedSource :=
  { source with nodes := source.nodes.map fun
    | .statement node => match node.form with
      | .forLoop initializer condition post body =>
        let initializer := initializer.zipIdx.map fun (item, index) => match item with
          | .assignValue assignment operator rhs =>
            .assignValue {assignment with target := {assignment.target with type := if index = 0 then first else second}} operator rhs
          | item => item
        .statement {node with form := .forLoop initializer condition post body}
      | _ => .statement node
    | node => node }

def run : IO Unit := do
  Tests.SourceCoreAssignmentFaultSites.run
  let program ← get "diagnostic certificate fixtures" (checkProgram workspace)
  let source ← body program "header"
  let table ← get "header prepare" (SourceCoreAssignmentFaultSites.prepare source 100)
  require (table.sites.length == 2 && table.sites.map (·.reason.val) == [100, 101])
    "actual header fold lost first-key deduplication or insertion order"
  let first ← match table.sites[0]? with
    | some first => pure first | none => throw (IO.userError "first header diagnostic missing")
  require (first.kind == .value .add && first.rhsType == .word &&
    table.reasonAt first.site first.binder first.kind == first.reason &&
    decide (table.diagnostic? first.reason = some first.diagnostic))
    "actual table lookup lost its original raw metadata or exact diagnostic"
  let assignment ← match source.nodes.findSome? fun
      | .statement node => match node.form with
        | .forLoop (.assignValue assignment .add _ :: _) _ _ _ => some assignment
        | _ => none
      | _ => none with
    | some assignment => pure assignment | none => throw (IO.userError "header assignment missing")
  let initialSites ← get "first add" (SourceCoreAssignmentFaultSites.add source.owner 200 [] first.site first.span assignment (.value .add))
  let laterSpan := {first.span with startByte := first.span.startByte + 7, endByte := first.span.endByte + 7}
  let laterAssignment := {assignment with target := {assignment.target with type := .integer}}
  let retained ← get "same-key add" (SourceCoreAssignmentFaultSites.add source.owner 200 initialSites first.site laterSpan laterAssignment (.value .add))
  require (decide (retained = initialSites)) "same-key add replaced the first complete record, including span or raw type"
  for (one, two, expected) in [(.word, .integer, TypeSystem.Ty.word), (.integer, .word, .integer)] do
    let retained ← get "retained collision prepare" (SourceCoreAssignmentFaultSites.prepare (headerTypes source one two) 100)
    require (retained.sites.length == 2 && retained.sites[0]?.map (·.rhsType) == some expected)
      "same-key later target metadata replaced the first diagnostic"
    require (retained.sites[0]?.map (·.reason) == some first.reason)
      "same-key metadata collision allocated another operand reason"
  let rawAlias ← get "raw alias prepare" (SourceCoreAssignmentFaultSites.prepare (headerTypes source (.comptime .word) (.comptime .word)) 100)
  require (rawAlias.sites.length == 1 && rawAlias.sites[0]?.map (·.kind) == some (.value .subtract))
    "normalized target type incorrectly passed the raw diagnostic guard"
  let equalOnly ← body program "equalOnly"
  let equalTable ← get "equal exhausted-space prepare" (SourceCoreAssignmentFaultSites.prepare equalOnly Core.wordModulus)
  require equalTable.sites.isEmpty "equal assignment unexpectedly requested a reason at exhausted capacity"
  IO.println "actual assignment diagnostic certificates: tokens, raw guards, first metadata and deduplication GREEN"

end Tests.SourceCoreAssignmentDiagnosticCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreAssignmentReachableDiagnostics
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicCorrespondence
/-! Concrete proof consumption for source `let value: Word; return value;`.
All occurrence, binder and compiler premises are discharged here. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicCorrespondence

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_correspondence", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "value", scheme := .mono .word }
private def letId : StatementId := ⟨⟨owner, 0⟩⟩
private def readId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def returnId : StatementId := ⟨⟨owner, 2⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_correspondence.solc" }
  startByte := 0
  endByte := 1
}
private def letNode : StatementNode := { id := letId, span, type := .unit, form := .letDecl binder none }
private def readNode : ExpressionNode := {
  id := readId
  span
  type := .word
  form := .reference "value" (.local binder.id)
}
private def returnNode : StatementNode := {
  id := returnId
  span
  type := .word
  form := .returnStmt (some readId)
}
private def source : TypedSource := {
  owner
  inputs := []
  roots := [.statement letId, .statement returnId]
  nodes := [.statement letNode, .expression readNode, .statement returnNode]
}
private def context : SourceSemantics.Context := .ofSignatures {
  functions := []
  implRules := []
  traits := []
  implementations := []
}
private def localContext : SourceSemantics.Context := context.withLocal binder.id binder.scheme

private theorem extension : BinderExtends owner context binder localContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, context, Context.ofSignatures]

private def site : CoreLowering.LocalCell.ReadSite source [(binder.id, .word)] readId .word := {
  node := readNode
  binder := binder.id
  name := "value"
  index := 0
  contains := ⟨by simp [source], rfl⟩
  form := rfl
  owner := rfl
  requirements := rfl
  coercions := rfl
  slot := rfl
  types := .word
}
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private def reason : Core.Word := Core.Word.ofNatModulo 41
private def expression : Core.Expr :=
  Core.LocalSequence.letUninitialized .word (Core.OptionalCell.read .word (.var 0) reason)
private def finalHeap : Dynamic.Heap := ⟨[{ type := .word, value := none }]⟩
private def finalStore : Core.Store := [.inLeft .word .unit]

/-- This witness comes from the executable lowerer and independent source
rules together; typed completion is a language failure, never a machine fault. -/
example (program : Program) (trailing : List StatementId) :
    Frontend.SourceCoreBasic.lowerStatements 3 source [] (letId :: returnId :: trailing) .word reason =
        .ok expression ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        (letId :: returnId :: trailing) localContext
        (.fault (.uninitializedLocation ⟨0⟩)) finalHeap ∧
      Core.HasType [] expression (Core.LanguageResult.resultType .word) ∧
      ∃ required,
        (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial expression [] []) =
          .done (.inLeft .word (.word reason)) finalStore) ∧
        (∀ fuel value store, Core.runStateful fuel (.initial expression [] []) = .done value store →
          value = .inLeft .word (.word reason) ∧ store = finalStore) := by
  have letContains : ContainsStatement source letId letNode := ⟨by simp [source], rfl⟩
  have returnContains : ContainsStatement source returnId returnNode := ⟨by simp [source], rfl⟩
  obtain ⟨lowered, faults, _, _, typed, required, completes, reflects⟩ :=
    CoreLowering.BasicStatements.uninitialized_then_return
      (program := program) (context := context) (localContext := localContext) (evidence := [])
      (scope := []) (environment := []) (coreEnvironment := [])
      (heap := ⟨[]⟩) (store := []) (world := []) trailing reason unique
      letContains (by rfl) (by rfl) (by rfl) (by rfl) extension .word
      returnContains (by rfl) (by rfl) site (by rfl) (by rfl) .nil
  exact ⟨lowered, faults, typed [], required, completes, reflects⟩

end Tests.SourceCoreBasicCorrespondence
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicExpressionCertificates
/-! Proof consumers start from actual accepted lowering, not a hand-built Tree.
One nested expression exercises every currently accepted expression form. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicExpressionCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"expression_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "expression_certificates.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 71
private def scope : SourceCoreLocalCell.Scope := [(binder, .word)]
private def resultType : Core.Ty := .product (.product .word .bool) (.product .unit .word)
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : ExpressionNode :=
  { id := id index, span, type, form }

/-- `((7, true), ((), local))`, with a group node around the left pair. -/
private def source : TypedSource := {
  owner
  inputs := [{ id := binder, name := "local", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [
    .expression (node 0 (.product (.product .word .bool) (.product .unit .word)) (.tuple [id 1, id 5])),
    .expression (node 1 (.product .word .bool) (.group (id 2))),
    .expression (node 2 (.product .word .bool) (.tuple [id 3, id 4])),
    .expression (node 3 .word (.literal (.decimal "7"))),
    .expression (node 4 .bool (.reference "true" (.builtinBoolean true))),
    .expression (node 5 (.product .unit .word) (.tuple [id 6, id 7])),
    .expression (node 6 .unit (.tuple [])),
    .expression (node 7 .word (.reference "local" (.local binder)))
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair (.product .word .bool) (.product .unit .word)
    (Core.LocalSequence.pair .word .bool
      (Core.LanguageResult.success (.word (word 7))) (Core.LanguageResult.success (.bool true)))
    (Core.LocalSequence.pair .unit .word (Core.LanguageResult.success .unit)
      (Core.OptionalCell.read .word (.var 0) reason))

private theorem accepted : SourceCoreBasic.lowerExpression 4 source scope (id 0) reason =
    .ok ⟨resultType, code⟩ := by rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The exact compiler result produces a bounded structural certificate. -/
example : ∃ depth, depth ≤ 4 ∧ BasicExpressions.Tree source scope reason (id 0) resultType code depth :=
  BasicExpressions.tree_of_lowerExpression accepted

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType resultType) :=
  BasicExpressions.lowerExpression_hasType accepted

private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .word) 0]
private def environment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def world : Core.StoreTyping := [Core.OptionalCell.cellType .word]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl .nil

private def initializedHeap : Dynamic.Heap := ⟨[{ type := .word, value := some (.word (word 13)) }]⟩
private def initializedStore : Core.Store := [.inRight .unit (.word (word 13))]
private theorem initialized : LocalCell.HeapRepresents initializedHeap.cells initializedStore world :=
  .cons (.initialized (.word (word 13))) .nil
private def absentHeap : Dynamic.Heap := ⟨[{ type := .word, value := none }]⟩
private def absentStore : Core.Store := [.inLeft .word .unit]
private theorem absent : LocalCell.HeapRepresents absentHeap.cells absentStore world :=
  .cons (.uninitialized .word) .nil

private def Correspondence (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (heap : Dynamic.Heap) (store : Core.Store) : Prop :=
  Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType resultType) ∧
  ∃ sourceOutcome coreValue required,
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap (id 0) sourceOutcome heap ∧
    BasicExpressions.OutcomeRepresents resultType reason sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) = .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel (.initial code coreEnvironment store) = .done result finalStore →
      result = coreValue ∧ finalStore = store)

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence initializedHeap initializedStore :=
  BasicExpressions.lowerExpression_run_preserves accepted unique program context evidence environments initialized

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence absentHeap absentStore :=
  BasicExpressions.lowerExpression_run_preserves accepted unique program context evidence environments absent

example : Core.runStateful 100 (.initial code coreEnvironment initializedStore) =
    .done (.inRight .word (.pair (.pair (.word (word 7)) (.bool true)) (.pair .unit (.word (word 13)))))
      initializedStore := by
  simp [code, Core.LocalSequence.pair, Core.OptionalCell.read, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment absentStore) =
    .done (.inLeft resultType (.word reason)) absentStore := by
  simp [code, Core.LocalSequence.pair, Core.OptionalCell.read, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Missing and mismatched local slots cannot be turned into a certificate. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 source [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 source [(binder, .bool)] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

private def only (expression : ExpressionNode) : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 0)], nodes := [.expression expression] }

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.literal (.decimal "invalid"))))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4
      (only { node 0 .bool (.reference "true" (.builtinBoolean true)) with requirements := [⟨0⟩] })
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.tuple [id 0])))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

/-- A cyclic occurrence edge exhausts compilation depth; it cannot forge Tree. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreBasic.lowerExpression 4 (only (node 0 .word (.group (id 0))))
      [] (id 0) reason ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreBasicExpressionCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicExpressions
/-! Concrete certificates for grouping, tuple order, and local-cell reads.
The same failure token deliberately represents two different source locations;
the source derivations below identify the actual first faulting location. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_expression_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def leftBinder : Resolved.LocalId := ⟨owner, 0⟩
private def rightBinder : Resolved.LocalId := ⟨owner, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_expression_certificate.solc" }
  startByte := 0
  endByte := 1
}
private def leftNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .reference "left" (.local leftBinder) }
private def rightNode : ExpressionNode := {
  id := id 1, span, type := .bool, form := .reference "right" (.local rightBinder) }
private def groupNode : ExpressionNode := {
  id := id 2, span, type := .word, form := .group (id 0) }
private def pairNode : ExpressionNode := {
  id := id 3, span, type := .product .word .bool, form := .tuple [id 2, id 1] }
private def rootNode : ExpressionNode := {
  id := id 4, span, type := .product .word .bool, form := .group (id 3) }
private def source : TypedSource := {
  owner
  inputs := [
    { id := leftBinder, name := "left", scheme := .mono .word },
    { id := rightBinder, name := "right", scheme := .mono .bool }]
  roots := [.expression (id 4)]
  nodes := [.expression leftNode, .expression rightNode, .expression groupNode,
    .expression pairNode, .expression rootNode]
}

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def token : Core.Word := word 87
private def scope : SourceCoreLocalCell.Scope := [(rightBinder, .bool), (leftBinder, .word)]
private def resultType : Core.Ty := .product .word .bool
private def code : Core.Expr := Core.LocalSequence.pair .word .bool
  (Core.OptionalCell.read .word (.var 1) token)
  (Core.OptionalCell.read .bool (.var 0) token)

private theorem leftMetadata : BasicExpressions.Metadata source (id 0) leftNode .word := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .word
  requirements := rfl
  coercions := rfl
}
private theorem rightMetadata : BasicExpressions.Metadata source (id 1) rightNode .bool := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .bool
  requirements := rfl
  coercions := rfl
}
private theorem groupMetadata : BasicExpressions.Metadata source (id 2) groupNode .word := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .word
  requirements := rfl
  coercions := rfl
}
private theorem pairMetadata : BasicExpressions.Metadata source (id 3) pairNode resultType := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .product .word .bool
  requirements := rfl
  coercions := rfl
}
private theorem rootMetadata : BasicExpressions.Metadata source (id 4) rootNode resultType := {
  contains := ⟨by simp [source], rfl⟩
  owned := rfl
  types := .product .word .bool
  requirements := rfl
  coercions := rfl
}

private theorem tree : BasicExpressions.Tree source scope token (id 4) resultType code 4 :=
  .group rootMetadata rfl (.pair pairMetadata rfl
    (.group groupMetadata rfl (.localRead leftMetadata rfl rfl rfl))
    (.localRead rightMetadata rfl rfl rfl))

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, leftNode, rightNode,
    groupNode, pairNode, rootNode, Node.occurrenceId, Node.id, NodeId.occurrenceId, id]

private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def environment : Dynamic.Environment := [(rightBinder, ⟨1⟩), (leftBinder, ⟨0⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 1,
    .cellRef (Core.OptionalCell.cellType .word) 0]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl (.cons rfl .nil)

private def presentWord : Dynamic.Cell := { type := .word, value := some (.word (word 5)) }
private def absentWord : Dynamic.Cell := { type := .word, value := none }
private def presentBool : Dynamic.Cell := { type := .bool, value := some (.bool true) }
private def absentBool : Dynamic.Cell := { type := .bool, value := none }
private def successHeap : Dynamic.Heap := ⟨[presentWord, presentBool]⟩
private def leftFailureHeap : Dynamic.Heap := ⟨[absentWord, absentBool]⟩
private def rightFailureHeap : Dynamic.Heap := ⟨[presentWord, absentBool]⟩
private def successStore : Core.Store := [.inRight .unit (.word (word 5)), .inRight .unit (.bool true)]
private def leftFailureStore : Core.Store := [.inLeft .word .unit, .inLeft .bool .unit]
private def rightFailureStore : Core.Store := [.inRight .unit (.word (word 5)), .inLeft .bool .unit]
private def successValue : Core.Value := .inRight .word (.pair (.word (word 5)) (.bool true))
private def failureValue : Core.Value := .inLeft resultType (.word token)

private theorem successHeaps : LocalCell.HeapRepresents successHeap.cells successStore world :=
  .cons (.initialized (.word (word 5))) (.cons (.initialized (.bool true)) .nil)
private theorem leftFailureHeaps : LocalCell.HeapRepresents leftFailureHeap.cells leftFailureStore world :=
  .cons (.uninitialized .word) (.cons (.uninitialized .bool) .nil)
private theorem rightFailureHeaps : LocalCell.HeapRepresents rightFailureHeap.cells rightFailureStore world :=
  .cons (.initialized (.word (word 5))) (.cons (.uninitialized .bool) .nil)

private def Correspondence (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (heap : Dynamic.Heap) (store : Core.Store) : Prop :=
  SourceCoreBasic.lowerExpression 4 source scope (id 4) token = .ok ⟨resultType, code⟩ ∧
  Core.infer? (SourceCoreLocalCell.coreContext scope) code = some (Core.LanguageResult.resultType resultType) ∧
  ∃ sourceOutcome coreValue required,
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap (id 4) sourceOutcome heap ∧
    BasicExpressions.OutcomeRepresents resultType token sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment store) = .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel (.initial code coreEnvironment store) = .done result finalStore →
      result = coreValue ∧ finalStore = store)

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence successHeap successStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments successHeaps

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence leftFailureHeap leftFailureStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments leftFailureHeaps

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) : Correspondence program context evidence rightFailureHeap rightFailureStore :=
  tree.lower_run_preserves unique 4 (by decide) program context evidence environments rightFailureHeaps

private theorem leftRead (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (tail : List Dynamic.Cell) :
    Dynamic.ExpressionEvaluates program context evidence source environment ⟨presentWord :: tail⟩
      (id 0) (.word (word 5)) ⟨presentWord :: tail⟩ := by
  apply Dynamic.ExpressionEvaluates.intro leftMetadata.contains
  · exact .local rfl (.tail (by decide) .head) (.intro .head) rfl rfl
  · exact .nil

private theorem groupedLeftRead (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (tail : List Dynamic.Cell) :
    Dynamic.ExpressionEvaluates program context evidence source environment ⟨presentWord :: tail⟩
      (id 2) (.word (word 5)) ⟨presentWord :: tail⟩ := by
  apply Dynamic.ExpressionEvaluates.intro groupMetadata.contains
  · exact .group rfl (leftRead program context evidence tail)
  · exact .nil

/-- Independent source success for the nested grouped tuple. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionEvaluates program context evidence source environment successHeap (id 4)
      (.product (.word (word 5)) (.bool true)) successHeap := by
  have right : Dynamic.ExpressionEvaluates program context evidence source environment successHeap
      (id 1) (.bool true) successHeap := by
    apply Dynamic.ExpressionEvaluates.intro rightMetadata.contains
    · exact .local rfl .head (.intro (.tail .head)) rfl rfl
    · exact .nil
  have paired : Dynamic.ExpressionEvaluates program context evidence source environment successHeap
      (id 3) (.product (.word (word 5)) (.bool true)) successHeap := by
    apply Dynamic.ExpressionEvaluates.intro pairMetadata.contains
    · exact .tuple rfl (.cons (groupedLeftRead program context evidence [presentBool])
        (.cons right .nil)) (.cons (.singleton _))
    · exact .nil
  apply Dynamic.ExpressionEvaluates.intro rootMetadata.contains
  · exact .group rfl paired
  · exact .nil

/-- Both cells are absent, but the left child faults at location zero. Its
tuple-fault derivation has no premise evaluating the right child. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap (id 4)
      (.uninitializedLocation ⟨0⟩) leftFailureHeap := by
  have left : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 0) (.uninitializedLocation ⟨0⟩) leftFailureHeap := by
    apply Dynamic.ExpressionFaults.form leftMetadata.contains
    exact .localUninitialized (owned := []) rfl (.tail (by decide) .head)
      (.intro .head) rfl rfl LocalCell.TypeRepresents.word.not_mapping
  have grouped : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 2) (.uninitializedLocation ⟨0⟩) leftFailureHeap :=
    .form groupMetadata.contains (.group rfl left)
  have paired : Dynamic.ExpressionFaults program context evidence source environment leftFailureHeap
      (id 3) (.uninitializedLocation ⟨0⟩) leftFailureHeap :=
    .form pairMetadata.contains (.tuple rfl (.head grouped))
  exact .form rootMetadata.contains (.group rfl paired)

/-- A successful left read allows the right child to fault at location one. -/
example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap (id 4)
      (.uninitializedLocation ⟨1⟩) rightFailureHeap := by
  have right : Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap
      (id 1) (.uninitializedLocation ⟨1⟩) rightFailureHeap := by
    apply Dynamic.ExpressionFaults.form rightMetadata.contains
    exact .localUninitialized (owned := []) rfl .head (.intro (.tail .head)) rfl rfl
      LocalCell.TypeRepresents.bool.not_mapping
  have paired : Dynamic.ExpressionFaults program context evidence source environment rightFailureHeap
      (id 3) (.uninitializedLocation ⟨1⟩) rightFailureHeap :=
    .form pairMetadata.contains (.tuple rfl
      (.tail (groupedLeftRead program context evidence [absentBool]) (.head right)))
  exact .form rootMetadata.contains (.group rfl paired)

example : Core.runStateful 100 (.initial code coreEnvironment successStore) = .done successValue successStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment leftFailureStore) = .done failureValue leftFailureStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

example : Core.runStateful 100 (.initial code coreEnvironment rightFailureStore) = .done failureValue rightFailureStore := by
  simp only [code, Core.LocalSequence.pair, Core.Expr.weakenAt, Core.LanguageResult.bind,
    Core.LanguageResult.success, Core.LanguageResult.failure, Core.OptionalCell.read]
  rfl

end Tests.SourceCoreBasicExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicStatementCertificates
/-! Certificates are obtained from actual compiler success. No statement tree
or evaluation derivation is supplied by these tests. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"statement_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "statement_certificates.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 73
private def resultType : Core.Ty := .product .word .bool
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := (List.range 6).map stmtId

/-- `let a: Word; let b = 7; a = b; b; return (a, true); { ... }`.
The unsupported final block is skipped by the actual explicit return branch. -/
private def source : TypedSource := {
  owner
  inputs := []
  roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.reference "b" (.local (binder 1).id)),
    expressionNode 2 .word (.reference "a" (.local (binder 0).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 (.product .word .bool) (.tuple [exprId 2, exprId 3]),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.assignValue assignment .equal (exprId 1)),
    statementNode 3 .unit (.expression (exprId 1) true),
    statementNode 4 (.product .word .bool) (.returnStmt (some (exprId 4))),
    statementNode 5 .unit (.block [])
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized resultType .word (Core.LanguageResult.success (.word (word 7)))
      (Core.LocalSequence.assign resultType (.var 1) (Core.OptionalCell.read .word (.var 0) reason)
        (Core.LocalSequence.discard resultType (Core.OptionalCell.read .word (.var 0) reason)
          (Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
            (Core.LanguageResult.success (.bool true))))))

private theorem accepted : SourceCoreBasic.lowerStatements 8 source [] statements resultType reason =
    .ok code := by rfl

example : Core.HasType [] code (Core.LanguageResult.resultType resultType) :=
  BasicStatements.lowerStatements_hasType accepted

example : Core.infer? [] code = some (Core.LanguageResult.resultType resultType) :=
  BasicStatements.lowerStatements_infer accepted

example : Core.CellPayload resultType :=
  (BasicStatements.lowerStatements_typing accepted).2

example : BasicStatements.BinderCertificate source [] (binder 0) .word :=
  BasicStatements.lowerBinder_certificate (by rfl)

example : BasicStatements.AssignmentCertificate source [((binder 1).id, .word), ((binder 0).id, .word)]
    assignment .equal 1 .word :=
  BasicStatements.lowerAssignment_certificate (by rfl)

/-- The three Unit/implicit completion branches use the same universal theorem. -/
private def returnUnit : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)], nodes := [statementNode 0 .unit (.returnStmt none)]
}
private def implicitReturn : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)], nodes := [expressionNode 0 .bool (.reference "true" (.builtinBoolean true)),
    statementNode 0 .bool (.expression (exprId 0) false)]
}
example : Core.HasType [] (Core.LanguageResult.success .unit) (Core.LanguageResult.resultType .unit) :=
  BasicStatements.lowerStatements_hasType
    (source := source) (scope := []) (fuel := 0) (statements := []) (reason := reason) (by rfl)
example : Core.HasType [] (Core.LanguageResult.success .unit) (Core.LanguageResult.resultType .unit) :=
  BasicStatements.lowerStatements_hasType
    (source := returnUnit) (scope := []) (fuel := 1) (statements := [stmtId 0]) (reason := reason) (by rfl)
example : Core.HasType [] (Core.LanguageResult.success (.bool true)) (Core.LanguageResult.resultType .bool) :=
  BasicStatements.lowerStatements_hasType
    (source := implicitReturn) (scope := []) (fuel := 2) (statements := [stmtId 0]) (reason := reason) (by rfl)

/-- Rejected scope and annotation cases cannot feed typing extraction. -/
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [((binder 0).id, .word)] statements resultType reason ≠
      .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [] statements .bool reason ≠ .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 implicitReturn [] [stmtId 0, stmtId 0] .bool reason ≠
      .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 0 source [] [] .word reason ≠ .ok output := by
  intro impossible
  cases impossible
example (output : Core.Expr) :
    SourceCoreBasic.lowerStatements 8 source [] [stmtId 5] .unit reason ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreBasicStatementCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicStatementMeaning
/-! A complete source/Core statement derivation is obtained from the structural
certificate. No child source or Core evaluation is provided. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementMeaning

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"statement_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "statement_certificates.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 73
private def resultType : Core.Ty := .product .word .bool
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := (List.range 6).map stmtId

/-- `let a: Word; let b = 7; a = b; b; return (a, true); { ... }`.
The unsupported final block is skipped by the actual explicit return branch. -/
private def source : TypedSource := {
  owner
  inputs := []
  roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.reference "b" (.local (binder 1).id)),
    expressionNode 2 .word (.reference "a" (.local (binder 0).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 (.product .word .bool) (.tuple [exprId 2, exprId 3]),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.assignValue assignment .equal (exprId 1)),
    statementNode 3 .unit (.expression (exprId 1) true),
    statementNode 4 (.product .word .bool) (.returnStmt (some (exprId 4))),
    statementNode 5 .unit (.block [])
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized resultType .word (Core.LanguageResult.success (.word (word 7)))
      (Core.LocalSequence.assign resultType (.var 1) (Core.OptionalCell.read .word (.var 0) reason)
        (Core.LocalSequence.discard resultType (Core.OptionalCell.read .word (.var 0) reason)
          (Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
            (Core.LanguageResult.success (.bool true))))))

private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private def firstContext : SourceSemantics.Context :=
  context.withLocal (binder 0).id (binder 0).scheme
private def secondContext : SourceSemantics.Context :=
  firstContext.withLocal (binder 1).id (binder 1).scheme

private theorem firstExtension : BinderExtends owner context (binder 0) firstContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, context, Context.ofSignatures]

private theorem secondExtension : BinderExtends owner firstContext (binder 1) secondContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, firstContext, context, Context.ofSignatures, Context.withLocal]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, firstContext, context, Context.ofSignatures, Context.withLocal, binder]

private def statement (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : StatementNode :=
  { id := stmtId index, span, type, form }
private def bothScope : SourceCoreBasic.Scope := [((binder 1).id, .word), ((binder 0).id, .word)]

private theorem certificate : ∃ depth, BasicStatements.Tree source reason [] context
    statements resultType code depth := by
  obtain ⟨initializerDepth, _, initializer⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.LanguageResult.success (.word (word 7))⟩) (by rfl)
  obtain ⟨localDepth, _, localRead⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := bothScope) (id := exprId 1) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  obtain ⟨pairDepth, _, pair⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 2) (source := source) (scope := bothScope) (id := exprId 4) (reason := reason)
    (lowered := ⟨resultType, Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
      (Core.LanguageResult.success (.bool true))⟩) (by rfl)
  have returned := BasicStatements.Tree.returnValue (context := secondContext) [stmtId 5]
    ((BasicStatements.readStatement_certificate
      (id := stmtId 4) (node := statement 4 (.product .word .bool) (.returnStmt (some (exprId 4)))) (by rfl)).2)
    (by rfl) pair
  have discarded := BasicStatements.Tree.discard
    ((BasicStatements.readStatement_certificate
      (id := stmtId 3) (node := statement 3 .unit (.expression (exprId 1) true)) (by rfl)).2)
    (by rfl) localRead returned
  have assigned := BasicStatements.Tree.assign
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.assignValue assignment .equal (exprId 1))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerAssignment_certificate (index := 1) (by rfl)) localRead discarded
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension initializer assigned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The complete source result and final heap follow from the certificate,
including allocation, assignment and the inserted initializer payload. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason resultType outcome result ∧
      Core.Evaluates [] [] code result finalStore ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends [] finalWorld := by
  obtain ⟨depth, tree⟩ := certificate
  exact tree.preserves unique program [] .nil .nil

example (program : Program) :
    ∃ compilationFuel finalContext outcome after result finalStore finalWorld required,
      SourceCoreBasic.lowerStatements compilationFuel source [] statements resultType reason = .ok code ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason resultType outcome result ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code [] []) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code [] []) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨lowered, _, finalContext, outcome, after, result, finalStore, finalWorld, required,
    sourceExecution, related, heaps, _, _, completes, reflects⟩ :=
    tree.lower_run_preserves unique depth (Nat.le_refl _) program [] .nil .nil
  exact ⟨_, _, _, _, _, _, _, _, lowered, sourceExecution, related, heaps, completes, reflects⟩

/-- A concrete kernel run fixes both mutable cells to the assigned value. -/
example : Core.runStateful 200 (.initial code [] []) =
    .done (.inRight .word (.pair (.word (word 7)) (.bool true)))
      [.inRight .unit (.word (word 7)), .inRight .unit (.word (word 7))] := by
  simp [code, resultType, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.LocalSequence.assign, Core.LocalSequence.discard, Core.LocalSequence.pair,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- A failed initializer must leave only the first allocation and skip both
the second allocation and the return. The same general body theorem applies. -/
private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 2].map .statement
  nodes := [expressionNode 0 .word (.reference "a" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.returnStmt none)]
}
private def failedCode : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized .unit .word (Core.OptionalCell.read .word (.var 0) reason)
      (Core.LanguageResult.success .unit))
private theorem failedCertificate : ∃ depth, BasicStatements.Tree failedSource reason [] context
    [stmtId 0, stmtId 1, stmtId 2] .unit failedCode depth := by
  obtain ⟨valueDepth, _, value⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := failedSource) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  have returned := BasicStatements.Tree.returnUnit (source := failedSource) (reason := reason)
    (context := secondContext) (scope := bothScope) []
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.returnStmt none)) (by rfl)).2) (by rfl)
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension value returned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

example (program : Program) :
    ∃ finalContext outcome after result finalStore finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩
        [stmtId 0, stmtId 1, stmtId 2] finalContext outcome after ∧
      BasicStatements.OutcomeRepresents finalWorld reason .unit outcome result ∧
      Core.Evaluates [] [] failedCode result finalStore ∧
      LocalCell.HeapRepresents after.cells finalStore finalWorld ∧ Core.WorldExtends [] finalWorld := by
  obtain ⟨depth, tree⟩ := failedCertificate
  have unique : NodeOccurrencesUnique failedSource := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  exact tree.preserves unique program [] .nil .nil

example : Core.runStateful 100 (.initial failedCode [] []) =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreBasicStatementMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicStatementTreeCertificates
/-! Actual successful basic compilation supplies whole statement certificates,
including declarative binder extensions. No Tree is constructed by the tests. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatementTreeCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "general_statements.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 73
private def resultType : Core.Ty := .product .word .bool
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := (List.range 6).map stmtId

/-- `let a: Word; let b = 7; a = b; b; return (a, true); { ... }`.
The unsupported final block is skipped by the actual explicit return branch. -/
private def source : TypedSource := {
  owner
  inputs := []
  roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.reference "b" (.local (binder 1).id)),
    expressionNode 2 .word (.reference "a" (.local (binder 0).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 (.product .word .bool) (.tuple [exprId 2, exprId 3]),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.assignValue assignment .equal (exprId 1)),
    statementNode 3 .unit (.expression (exprId 1) true),
    statementNode 4 (.product .word .bool) (.returnStmt (some (exprId 4))),
    statementNode 5 .unit (.block [])
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized resultType .word (Core.LanguageResult.success (.word (word 7)))
      (Core.LocalSequence.assign resultType (.var 1) (Core.OptionalCell.read .word (.var 0) reason)
        (Core.LocalSequence.discard resultType (Core.OptionalCell.read .word (.var 0) reason)
          (Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
            (Core.LanguageResult.success (.bool true))))))

private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}

private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _

private theorem accepted : SourceCoreBasic.lowerStatements 20 source [] statements resultType reason = .ok code := by
  rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- Both declarations, assignment, discard and explicit return are recovered
from the compiler result. The unreachable unsupported block needs no Tree. -/
example : ∃ depth, depth ≤ 20 ∧ BasicStatements.Tree source reason [] context statements resultType code depth :=
  BasicStatements.tree_of_lowerStatements aligned accepted

/-- One typed administrative function cell forms a cycle through its captured
reference. It is not associated with any source heap location. -/
private def functionType : Core.Ty := .function .unit .unit
private def administrativeValue : Core.Value := .closure .unit .unit
  (.apply (.loadCell (.var 1)) (.var 0)) [.cellRef functionType 0]
private def initialWorld : Core.StoreTyping := [functionType]
private def initialStore : Core.Store := [administrativeValue]
private def initialEnvironment : Core.Environment := [.cellRef functionType 0]
private def administrativeContext : Core.Context := [.cell functionType]
private theorem administrativeTyped : Core.RuntimeValueHasType initialWorld administrativeValue functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.apply (.loadCell (.var rfl)) (.var rfl))
private theorem initialHeaps : GeneralHeap.HeapRepresents [] initialWorld ⟨[]⟩ initialStore := by
  refine ⟨rfl, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro index type found
    cases index with
    | zero =>
        have same : functionType = type := by simpa [initialWorld] using found
        subst type
        exact ⟨administrativeValue, rfl, administrativeTyped⟩
    | succ index => simp [initialWorld] at found
  · intro source target impossible; simp at impossible
private theorem initialEnvironments : GeneralHeap.EnvRepresents [] initialWorld administrativeContext
    [] [] initialEnvironment := .nil (.cons (.cellRef rfl) .nil)


/-- Actual acceptance directly supplies the independent source execution and
Core runner correspondence with a cyclic administrative function installed. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason resultType outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) =
        .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) =
        .done actual actualStore → actual = result ∧ actualStore = finalStore) :=
  (BasicStatements.lowerStatements_run_preserves aligned unique accepted program [] initialEnvironments initialHeaps).2

/-- Initial ambient locals may be populated; the checked freshness condition
is transported across both paired source lexical tables. -/
example : BinderExtends owner
    (context.withLocal (binder 0).id (binder 0).scheme)
    (binder 1)
    ((context.withLocal (binder 0).id (binder 0).scheme).withLocal (binder 1).id (binder 1).scheme) := by
  exact (BasicStatements.lowerBinder_certificate
    (show SourceCoreBasic.lowerBinder source [((binder 0).id, .word)] (binder 1) = .ok .word from by rfl)).extends
      (aligned.bind (binder 0) .word)

/-- A compiler success cannot manufacture freshness for a malformed source
context containing an extra stale qualified-scheme entry. -/
example : ¬ BasicStatements.ScopeContextAligned []
    { context with localSchemeRequirements := [((binder 0).id, [])] } := by
  intro invalid
  have impossible := invalid.requirements
  simp at impossible

private def returnUnitSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit (.returnStmt none)]
}
example : ∃ depth, depth ≤ 1 ∧ BasicStatements.Tree returnUnitSource reason [] context
    [stmtId 0, stmtId 99] .unit (Core.LanguageResult.success .unit) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

/-- Empty fallthrough is admitted even at zero traversal fuel. -/
example : ∃ depth, depth ≤ 0 ∧ BasicStatements.Tree source reason [] context [] .unit
    (Core.LanguageResult.success .unit) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)]
}
example : ∃ depth, depth ≤ 2 ∧ BasicStatements.Tree tailSource reason [] context
    [stmtId 0] .word (Core.LanguageResult.success (.word (word 7))) depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

/-- A non-final implicit return is rejected, rather than producing a Tree
which skips its remaining statements. -/
example : SourceCoreBasic.lowerStatements 2 tailSource [] [stmtId 0, stmtId 1] .word reason =
    .error (.nonTailExpression (stmtId 0)) := by rfl

/-- Duplicate binder identities are rejected before a second lexical extension. -/
example : SourceCoreBasic.lowerBinder source [((binder 0).id, .word)] (binder 0) =
    .error (.duplicateBinding (binder 0).id) := by rfl

private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 2].map .statement
  nodes := [expressionNode 0 .word (.reference "a" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.returnStmt none)]
}
private def failedCode : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized .unit .word (Core.OptionalCell.read .word (.var 0) reason)
      (Core.LanguageResult.success .unit))

/-- Extraction does not assume initialized locals or successful source values.
This admitted list fails in its initializer before the second allocation. -/
example : ∃ depth, depth ≤ 4 ∧ BasicStatements.Tree failedSource reason [] context
    [stmtId 0, stmtId 1, stmtId 2] .unit failedCode depth :=
  BasicStatements.tree_of_lowerStatements aligned (by rfl)

example : Core.runStateful 100 (.initial failedCode initialEnvironment initialStore) =
    .done (.inLeft .unit (.word reason)) [administrativeValue, .inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreBasicStatementTreeCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreBasicStatements
/-! A complete compiler/source-semantics consumer for allocation, plain
assignment and return. The source heap and Core store agree after the write;
the generated program is checked and executed, rather than replaced by a
hand-written equivalent for the correspondence claim. -/

set_option autoImplicit false

namespace Tests.SourceCoreBasicStatements

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"basic_statement_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binderId : Resolved.LocalId := ⟨owner, 0⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def expression (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "basic_statement_meaning.solc" }
  startByte := 0
  endByte := 1
}
private def binder : TypedBinder := { id := binderId, name := "value", scheme := .mono .bool }
private def assignment : AssignmentResolution := {
  target := { root := binderId, projections := [], type := .bool }
}
private def letNode : StatementNode := {
  id := statement 0, span, type := .unit, form := .letDecl binder none
}
private def assignNode : StatementNode := {
  id := statement 1, span, type := .unit, form := .assignValue assignment .equal (expression 3)
}
private def returnNode : StatementNode := {
  id := statement 2, span, type := .bool, form := .returnStmt (some (expression 4))
}
private def trueNode : ExpressionNode := {
  id := expression 3, span, type := .bool, form := .reference "true" (.builtinBoolean true)
}
private def readNode : ExpressionNode := {
  id := expression 4, span, type := .bool, form := .reference "value" (.local binderId)
}
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement (statement 0), .statement (statement 1),
    .statement (statement 2)]
  nodes := [.statement letNode, .statement assignNode, .statement returnNode,
    .expression trueNode, .expression readNode]
}
private def statements : List StatementId := [statement 0, statement 1, statement 2]
private def reason : Core.Word := Core.Word.ofNatModulo 81
private def code : Core.Expr := Core.LocalSequence.letUninitialized .bool
  (Core.LocalSequence.assign .bool (.var 0) (Core.LanguageResult.success (.bool true))
    (Core.OptionalCell.read .bool (.var 0) reason))
private def coreProgram : Core.Program := {
  resultType := Core.LanguageResult.resultType .bool
  body := code
}

private theorem compiled : SourceCoreBasic.lowerStatements 6 source [] statements .bool reason =
    .ok coreProgram.body := by rfl
private theorem checked : coreProgram.check = true := by
  simp [coreProgram, code, Core.LocalSequence.letUninitialized,
    Core.LocalSequence.assign, Core.OptionalCell.allocate, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
    Core.Expr.weakenAt]
  decide
private theorem completed : coreProgram.runStateful 100 =
    .done (.inRight .word (.bool true)) [.inRight .unit (.bool true)] := by
  simp [coreProgram, code, Core.LocalSequence.letUninitialized,
    Core.LocalSequence.assign, Core.OptionalCell.allocate, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure,
    Core.Expr.weakenAt]
  rfl

private theorem letContains : ContainsStatement source (statement 0) letNode :=
  ⟨.head _, rfl⟩
private theorem assignContains : ContainsStatement source (statement 1) assignNode :=
  ⟨.tail _ (.head _), rfl⟩
private theorem returnContains : ContainsStatement source (statement 2) returnNode :=
  ⟨.tail _ (.tail _ (.head _)), rfl⟩
private theorem trueContains : ContainsExpression source (expression 3) trueNode :=
  ⟨.tail _ (.tail _ (.tail _ (.head _))), rfl⟩
private theorem readContains : ContainsExpression source (expression 4) readNode :=
  ⟨.tail _ (.tail _ (.tail _ (.tail _ (.head _)))), rfl⟩

private def absentHeap : Dynamic.Heap := ⟨[{ type := .bool, value := none }]⟩
private def presentHeap : Dynamic.Heap := ⟨[{ type := .bool, value := some (.bool true) }]⟩
private def environment : Dynamic.Environment := [(binderId, ⟨0⟩)]

private theorem source_evaluates (program : SourceSemantics.Program)
    (context localContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (extension : BinderExtends owner context binder localContext) :
    Dynamic.FunctionStatementsExecute program context evidence source [] ⟨[]⟩ statements localContext
      (.returned (.bool true)) presentHeap := by
  have allocated : Dynamic.StatementExecutes program context evidence source [] ⟨[]⟩ (statement 0)
      localContext (.fallthrough environment) absentHeap :=
    .letUninitialized letContains rfl rfl extension .append
  have rhs : Dynamic.ExpressionEvaluates program localContext evidence source environment absentHeap
      (expression 3) (.bool true) absentHeap :=
    .intro trueContains (.builtinBoolean rfl) .nil
  have initial : Dynamic.RootInitialValue ({ type := .bool, value := none } : Dynamic.Cell) none :=
    .uninitialized (by rintro ⟨_, _, impossible⟩; cases impossible)
  have assigned : Dynamic.StatementExecutes program localContext evidence source environment absentHeap
      (statement 1) localContext (.fallthrough environment) presentHeap := by
    apply Dynamic.StatementExecutes.assignValue assignContains rfl
    apply Dynamic.SourcePlaceAssignment.intro
    · exact .intro .head (.intro .head) .nil (.intro .head) initial .nil
    · exact rhs
    · exact .intro (.intro .head) rfl initial (.leaf (.equal none (.bool true)))
        (.intro (.intro .head) .head)
  have returned : Dynamic.StatementExecutes program localContext evidence source environment presentHeap
      (statement 2) localContext (.returned (.bool true)) presentHeap :=
    .returnValue returnContains rfl
      (.intro readContains (.local rfl .head (.intro .head) rfl rfl) .nil)
  exact .cons allocated (.cons assigned
    (.singleton returnContains (by intro value impossible; cases impossible) returned))

/-- The exact actual compiler output has independent source and Core finite
derivations, and their initialized final heaps are structurally related. -/
example (program : SourceSemantics.Program) (context localContext : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment)
    (extension : BinderExtends owner context binder localContext) :
    SourceCoreBasic.lowerStatements 6 source [] statements .bool reason = .ok coreProgram.body ∧
    Dynamic.FunctionStatementsExecute program context evidence source [] ⟨[]⟩ statements localContext
      (.returned (.bool true)) presentHeap ∧
    Core.Evaluates [] [] coreProgram.body (.inRight .word (.bool true)) [.inRight .unit (.bool true)] ∧
    CoreLowering.LocalCell.HeapRepresents presentHeap.cells [.inRight .unit (.bool true)]
      [Core.OptionalCell.cellType .bool] :=
  ⟨compiled, source_evaluates program context localContext evidence extension,
    Core.runStateful_evaluation_sound completed, .cons (.initialized (.bool true)) .nil⟩

example (fuel : Nat) : (coreProgram.runStateful fuel).HasType coreProgram.resultType :=
  Core.Program.checked_runStateful_has_type checked fuel

example (fuel additional : Nat) (checkpoint : Core.State)
    (exhausted : coreProgram.runStateful fuel = .outOfFuel checkpoint) :
    Core.runStateful additional checkpoint = coreProgram.runStateful (fuel + additional) :=
  Core.runStateful_resume exhausted additional

end Tests.SourceCoreBasicStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreContractedFunctions
/-! Actual decorated lambda compilation and independent source formation.
A sealed descriptor is a static input. The real emitted wrapper and guards
preserve the actual capture environment, including an inserted integer slot.
No interpretation of rejected stage guards as old Dynamic faults is assumed. -/

set_option autoImplicit false
namespace Tests.SourceCoreContractedFunctions
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap FunctionCaptures

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"contracted_functions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "contracted_functions.solc"⟩, 0, 1⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def program : Program := ⟨signatures, [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { callableContracts := true }
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.CallableContract.functionType .unit .unit
private def node : ExpressionNode := { id, span, type := sourceType, form := .lambda [] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression node] }
private def context : SourceSemantics.Context := {
  SourceSemantics.Context.ofSignatures signatures with
  currentDeclaration := some owner, residualTypeVariables := true }
private def function : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def compilation : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0
  solvedRequirements := [], internalReason := Core.Word.zero }
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun _ budget source scope statements result _ reason _ =>
    SourceCoreBasic.lowerStatements budget source scope statements result reason
private def bodyCertificate : FunctionCode.BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = Core.LanguageResult.success .unit

private def policy {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id [])) : SourceCoreFunctions.Policy := {
  readExpression := fun _ _ => pure (node, functionType)
  callables := {
    functionType := Core.CallableContract.functionType
    decorateCallable := fun _ _ _ _ _ _ raw => match raw with
      | .inRight .word value => pure (Core.LanguageResult.success (descriptor.wrap value))
      | _ => .error (.unsupportedExpression id node.form) } }
private def emitted {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id [])) : SourceCoreBasic.LoweredExpr :=
  ⟨functionType, Core.LanguageResult.success (descriptor.wrap (Core.TaggedFunction.anonymous
    (.lambda .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit))))⟩

variable {table : SourceCoreStageCodebook.Table}
  (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id []))

private theorem artifact_exists : Nonempty
    (DecoratedFunctionCode.LambdaCertificate bodyCertificate (policy descriptor) compilation source [] id node
      [] .unit [] functionType (emitted descriptor)) := by
  apply DecoratedFunctionCode.lambda_of_accepted (ordinaryCells := rfl) (ordinaryBody := rfl) (ordinaryExpression := rfl) (lowerBody := lowerBody) (fuel := 0)
    (policy := policy descriptor) (context := compilation) (source := source) (scope := []) (id := id) (node := node)
    (reasonAt := fun _ => Core.Word.zero) rfl rfl rfl rfl rfl
  · intro budget bodyScope type code accepted
    simp only [lowerBody, SourceCoreBasic.lowerStatements] at accepted
    split at accepted
    · next same => cases accepted; exact ⟨rfl, same, rfl⟩
    · cases accepted
  · cbv

private noncomputable def artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate (policy descriptor)
    compilation source [] id node [] .unit [] functionType (emitted descriptor) := Classical.choice (artifact_exists descriptor)

private theorem parameter_type : (artifact descriptor).raw.parameterCore = .unit := by
  have selected := (artifact descriptor).raw.parameterProjection
  rw [← (artifact descriptor).raw.bundle] at selected
  exact Except.ok.inj selected.symm
private theorem result_type : (artifact descriptor).raw.resultCore = .unit :=
  Except.ok.inj (artifact descriptor).raw.resultProjection.symm

private theorem graph : OccurrenceGraphWellFormed source := by
  constructor
  · unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  · intro selected member
    simp only [source, List.mem_singleton] at member
    subst selected; rfl
  · intro root member
    simp only [source, List.mem_singleton] at member
    subst root; rfl
  · intro root member
    simpa [source, nodeIds, Node.id, node] using member
  · intro selected member child childMember
    simp only [source, List.mem_singleton] at member
    subst selected; cases childMember

private theorem frame : Dynamic.ClosureFrame program function := by
  have unique : RequirementIdsUnique context := by simp [RequirementIdsUnique, context, Context.ofSignatures]
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence impossible; cases impossible
    · intro predicate impossible; cases impossible
  refine ⟨rfl, rfl, ?_, unique, covers⟩
  refine ⟨rfl, rfl, rfl, rfl, graph, ⟨unique, ?_⟩, ?_⟩
  · intro row evidence member; cases member
  · refine ⟨id, node, ⟨by change Node.expression node ∈ [Node.expression node]; exact List.mem_singleton_self _, rfl⟩, rfl, rfl, ?_⟩
    exact .lambda (by decide) (.nil _) (.nil _ _) ⟨rfl, rfl, .inr rfl⟩

private def canonical : Core.Environment := [.word Core.Word.zero]
private def actual : Core.Environment := [.integer 11, .word Core.Word.zero]
private def layout : Layout catalog [] [] [] function.captured actual where
  administrativeContext := [.word]
  canonical := canonical
  actualContext := [.integer, .word]
  embedding := Core.Renaming.insertion 0
  represented := .nil (.cons .word .nil)
  lookups := Core.ReadOnly.EnvironmentsAgree.insertion canonical 0 (.integer 11)
  types := Core.Renaming.insertion_respects_insertAt [.word] 0 .integer
  actualTyped := .cons .integer (.cons .word .nil)

private noncomputable def code : ContractedFunctionValues.Code catalog program bodyCertificate (policy descriptor)
    compilation table [] function [] [.word] where
  id := id
  node := node
  reportedType := functionType
  lowered := emitted descriptor
  artifact := artifact descriptor
  owner := rfl
  descriptor := descriptor
  decoration := fun _ => rfl
  frame := frame
  projection := by rw [parameter_type descriptor, result_type descriptor]; rfl
  outputTyped := by
    rw [parameter_type descriptor, result_type descriptor]
    exact .inRight .word (.pair (Core.TaggedFunction.anonymous_hasType (.lambda .unit (.sum .word .unit)
      (.inRight .word .unit))) .word)

private def generated : Core.Value := .pair (FunctionValues.value .unit .unit
  (Core.LanguageResult.success .unit) layout.embedding actual) (.word descriptor.id)

private theorem raw_body : (artifact descriptor).raw.rawBody = Core.LanguageResult.success .unit := by
  have binders := (artifact descriptor).raw.parametersTree.binders
  have noParameters : (artifact descriptor).raw.loweredParameters = [] := List.map_eq_nil_iff.mp binders
  simp only [FunctionCode.LambdaCertificate.rawBody, SourceCoreSourceCells.copyScopePlain_nil, noParameters,
    SourceCoreFunctions.bindParameters, List.zipIdx_nil, List.foldr_nil, List.length_nil,
    (artifact descriptor).raw.bodyTree.2.2]
  simp only [Core.LanguageResult.success, Core.Expr.weakenAt]

private def model : GenericHeap.PayloadModel catalog :=
  ContractedFunctionValues.model catalog program bodyCertificate table

/-- With no captures there is nothing to copy, so the emitted wrapper
evaluates directly to the generated value without changing the store. -/
private theorem formed : Core.Evaluates actual [] ((emitted descriptor).expression.rename layout.embedding)
    (.inRight .word (generated descriptor)) [] := by
  simpa only [emitted, generated, FunctionValues.value, Core.LanguageResult.success,
    Core.TaggedFunction.anonymous, SourceCoreCallableContracts.Descriptor.wrap, Core.CallableContract.wrap,
    Core.Expr.rename] using
    (Core.Evaluates.inRight (.pair (.pair (.inLeft .unit) .lambda) .word) :
      Core.Evaluates actual [] _ _ [])

/-- Formation over the empty capture copies nothing: the source closure keeps
its empty capture and the heap, and the emitted wrapper is `formed`. -/
example : Dynamic.ExpressionEvaluates program context [] source [] ⟨[]⟩ id (.closure function) ⟨[]⟩ ∧
    Core.Evaluates actual [] ((emitted descriptor).expression.rename layout.embedding)
      (.inRight .word (generated descriptor)) [] := by
  refine ⟨?_, formed descriptor⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound (code descriptor).artifact.raw.found)
  · rw [(code descriptor).artifact.raw.form]
    exact .lambda rfl (.nil _)
  · exact .nil

/-- The authenticated formation over the empty initial heap. -/
example := ContractedFunctionValues.formation_corresponds layout (code descriptor)
  (GenericHeap.HeapRepresents.empty (model := model (table := table))) rfl rfl

example (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities functionType (.closure function) (generated descriptor) := by
  have observed := ContractedFunctionValues.Represents.observation
    (ContractedFunctionValues.Represents.closure layout (code descriptor)) signatures identities
  change DataEqualityValues.Observation catalog signatures identities
    (Core.CallableContract.functionType (artifact descriptor).raw.parameterCore (artifact descriptor).raw.resultCore)
    (.closure function) (ContractedFunctionValues.value (artifact descriptor).raw.parameterCore
      (artifact descriptor).raw.resultCore (artifact descriptor).raw.rawBody layout.embedding actual descriptor.id) at observed
  rw [raw_body descriptor, parameter_type descriptor, result_type descriptor] at observed
  exact observed

/-- Both gates accept, and the exact call prefix can be removed from every
completed evaluation without changing the actual captured body environment. -/
example : CoreProof.ContinuationAgreement actual []
    (Core.CallableContract.call [⟨descriptor.id, none, none⟩] Core.Word.zero .unit
      ((emitted descriptor).expression.rename layout.embedding) (Core.LanguageResult.success .unit))
    (.unit :: actual) [] (Core.LanguageResult.success .unit) := by
  apply ContractedFunctionCalls.accepted_call_agreement (contract := descriptor.id)
    (identity := .inLeft .word .unit) (parameter := .unit) (middle := []) (applied := [])
  · simpa only [generated, FunctionValues.value, Core.LanguageResult.success, Core.Expr.rename] using formed descriptor
  · simp [Core.CallableContract.decision, Core.CallableContract.Gate.reason]
  · simpa only [Core.LanguageResult.success, Core.Expr.weakenAt] using
      (Core.Evaluates.inRight (leftType := Core.Ty.word) Core.Evaluates.unit :
        Core.Evaluates _ [] (.inRight .word .unit) (.inRight .word .unit) [])
  · simp [Core.CallableContract.decision, Core.CallableContract.Gate.reason]

end Tests.SourceCoreContractedFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreControlExpressions
/-! Actual accepted conditional lowering supplies both independent evaluations.
Distinct read occurrences carry distinct test reasons, even at shared types. -/

set_option autoImplicit false

namespace Tests.SourceCoreControlExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .word)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def source : TypedSource := {
  owner
  inputs := [{ id := binder 0, name := "flag", scheme := .mono .bool },
    { id := binder 1, name := "left", scheme := .mono .word },
    { id := binder 2, name := "right", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.product .word .word) (.group (id 1)),
    node 1 (.product .word .word) (.tuple [id 2, id 6]),
    node 2 .word (.conditional (id 3) (id 4) (id 5)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.literal (.decimal "7")),
    node 5 .word (.reference "left" (.local (binder 1))),
    node 6 .word (.reference "right" (.local (binder 2)))]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair .word .word
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (Core.LanguageResult.success (.word (word 7)))
      (Core.OptionalCell.read .word (.var 1) (reasonAt (id 5))))
    (Core.OptionalCell.read .word (.var 2) (reasonAt (id 6)))
private theorem accepted : SourceCoreControl.lowerExpressionWithReasons 4 source scope (id 0) reasonAt =
    .ok ⟨.product .word .word, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType (.product .word .word)) :=
  ControlExpressions.lowerExpression_hasType unique accepted

example : ∃ node, SourceCoreBasic.readExpression source (id 0) = .ok (node, .product .word .word) ∧
    ControlExpressions.Metadata source (id 0) node (.product .word .word) :=
  ControlExpressions.lowerExpression_metadata unique accepted

private def boolCell (value : Option Bool) : Dynamic.Cell := { type := .bool, value := value.map .bool }
private def wordCell (value : Option Nat) : Dynamic.Cell := { type := .word, value := value.map fun n => .word (word n) }
private def boolStored : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def wordStored : Option Nat → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word (word value))
private def heap (flag : Option Bool) (left right : Option Nat) : Dynamic.Heap :=
  ⟨[boolCell flag, wordCell left, wordCell right]⟩
private def store (flag : Option Bool) (left right : Option Nat) : Core.Store :=
  [boolStored flag, wordStored left, wordStored right]
private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .bool, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .word]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 0,
    .cellRef (Core.OptionalCell.cellType .word) 1, .cellRef (Core.OptionalCell.cellType .word) 2]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl (.cons rfl (.cons rfl .nil))
private theorem boolRelated (value : Option Bool) : LocalCell.CellRepresents (boolCell value) (boolStored value) .bool := by
  cases value with
  | none => exact .uninitialized .bool
  | some value => exact .initialized (.bool value)
private theorem wordRelated (value : Option Nat) : LocalCell.CellRepresents (wordCell value) (wordStored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word (word value))
private theorem heaps (flag : Option Bool) (left right : Option Nat) :
    LocalCell.HeapRepresents (heap flag left right).cells (store flag left right) world :=
  .cons (boolRelated flag) (.cons (wordRelated left) (.cons (wordRelated right) .nil))

/-- One theorem covers initialized and absent inputs without manual trees or
child execution assumptions. Its failure case exposes the executed read site. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (left right : Option Nat) :
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag left right) (id 0) sourceOutcome (heap flag left right) ∧
      ControlExpressions.OutcomeRepresents program context evidence source environment
        (heap flag left right) reasonAt (id 0) (.product .word .word) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag left right)) =
        .done coreValue (store flag left right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag left right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag left right) :=
  (ControlExpressions.lowerExpression_run_preserves unique accepted program context evidence environments
    (heaps flag left right)).2

private theorem run_true : Core.runStateful 200 (.initial code coreEnvironment (store (some true) none (some 13))) =
    .done (.inRight .word (.pair (.word (word 7)) (.word (word 13)))) (store (some true) none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_false : Core.runStateful 200 (.initial code coreEnvironment (store (some false) (some 11) (some 13))) =
    .done (.inRight .word (.pair (.word (word 11)) (.word (word 13)))) (store (some false) (some 11) (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_conditionFault : Core.runStateful 200 (.initial code coreEnvironment (store none none (some 13))) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 3)))) (store none none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_branchFault : Core.runStateful 200 (.initial code coreEnvironment (store (some false) none (some 13))) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 5)))) (store (some false) none (some 13)) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_rightFault : Core.runStateful 200 (.initial code coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 6)))) (store (some true) none none) := by
  simp [code, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

private def thenFailedSource : TypedSource := {
  source with nodes := [node 0 (.product .word .word) (.group (id 1)),
    node 1 (.product .word .word) (.tuple [id 2, id 6]),
    node 2 .word (.conditional (id 3) (id 5) (id 4)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.literal (.decimal "7")),
    node 5 .word (.reference "left" (.local (binder 1))),
    node 6 .word (.reference "right" (.local (binder 2)))]
}
private def thenFailedCode : Core.Expr :=
  Core.LocalSequence.pair .word .word
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (Core.OptionalCell.read .word (.var 1) (reasonAt (id 5)))
      (Core.LanguageResult.success (.word (word 7))))
    (Core.OptionalCell.read .word (.var 2) (reasonAt (id 6)))
private theorem thenAccepted : SourceCoreControl.lowerExpressionWithReasons 4 thenFailedSource scope (id 0) reasonAt =
    .ok ⟨.product .word .word, thenFailedCode⟩ := by rfl

example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence thenFailedSource environment
        (heap (some true) none none) (id 0) sourceOutcome (heap (some true) none none) ∧
      ControlExpressions.OutcomeRepresents program context evidence thenFailedSource environment
        (heap (some true) none none) reasonAt (id 0) (.product .word .word) sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment (store (some true) none none) thenFailedCode coreValue
        (store (some true) none none) := by
  have unique : NodeOccurrencesUnique thenFailedSource := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  exact ControlExpressions.lowerExpression_preserves unique thenAccepted program context evidence environments
    (heaps (some true) none none)

example : Core.runStateful 200 (.initial thenFailedCode coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .word) (.word (reasonAt (id 5)))) (store (some true) none none) := by
  simp [thenFailedCode, Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Malformed conditional metadata and branch types are rejected by the real
compiler before any certificate or runtime result can be obtained. -/
private def badSource : TypedSource := {
  source with nodes := [node 0 .word (.conditional (id 3) (id 3) (id 4)),
    node 3 .bool (.reference "flag" (.local (binder 0))), node 4 .word (.literal (.decimal "7"))]
}
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreControl.lowerExpressionWithReasons 4 badSource scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCoreControl.lowerExpressionWithReasons 3 source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCoreControlExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreControlStatementCertificates
/-! Actual control compiler acceptance supplies the complete tree. These
fixtures cover both branch shapes, block scope, early return, and both tail
conventions without constructing or assuming any child Tree/evaluation. -/

set_option autoImplicit false

namespace Tests.SourceCoreControlStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_certificates.solc" }, startByte := 0, endByte := 1 }
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 50)
private def fellThrough : Core.Word := word 99
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := [] }
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _
private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 5]

/-- A branch can return the inner local; its scope is restored before the
outer implicit return. An absent else falls through. -/
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.literal (.decimal "9")),
    expressionNode 2 .bool (.reference "flag" (.builtinBoolean flag)),
    expressionNode 3 .word (.reference "inner" (.local (binder 1).id)),
    expressionNode 4 .word (.reference "outer" (.local (binder 0).id)),
    expressionNode 5 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .word (.block [stmtId 2, stmtId 3]),
    statementNode 2 .unit (.letDecl (binder 1) (some (exprId 1))),
    statementNode 3 .word (.ifThen (exprId 2) [stmtId 4]
      (if withElse then some [stmtId 6] else none)),
    statementNode 4 .word (.returnStmt (some (exprId 3))),
    statementNode 5 .word (.expression (exprId 4) false),
    statementNode 6 .word (.returnStmt (some (exprId 5)))
  ]
}

private def flow (flag withElse : Bool) : Core.Expr :=
  Core.LocalSequence.letInitialized (Core.LocalControl.controlType .word) .word
    (Core.LanguageResult.success (.word (word 7)))
    (Core.LocalControl.sequence .word
      (Core.LocalSequence.letInitialized (Core.LocalControl.controlType .word) .word
        (Core.LanguageResult.success (.word (word 9)))
        (Core.LocalControl.sequence .word
          (Core.LocalControl.conditional .word (Core.LanguageResult.success (.bool flag))
            (Core.LocalControl.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 3))))
            (if withElse then Core.LocalControl.returnValue .word
              (Core.OptionalCell.read .word (.var 1) (reasonAt (exprId 5)))
             else Core.LocalControl.fallthrough .word))
          (Core.LocalControl.fallthrough .word)))
      (Core.LocalControl.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 4)))))

private theorem unique (flag withElse : Bool) : NodeOccurrencesUnique (source flag withElse) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases flag <;> cases withElse <;> decide

private theorem accepted (flag withElse : Bool) :
    SourceCoreControl.lowerFlowStatementsWithReasons 20 (source flag withElse) [] statements .word
      reasonAt true = .ok (flow flag withElse) := by
  cases withElse <;> rfl

example (flag withElse : Bool) : ControlStatements.Tree (source flag withElse) reasonAt [] context true
    statements .word (flow flag withElse) :=
  ControlStatements.tree_of_lowerFlowStatements aligned (unique flag withElse) (accepted flag withElse)

example (flag withElse : Bool) : Core.HasType [] (flow flag withElse) (Core.LocalControl.resultType .word) :=
  (ControlStatements.tree_of_lowerFlowStatements aligned (unique flag withElse) (accepted flag withElse)).hasType .word

private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalControl.finish .word (flow flag withElse) (Core.LanguageResult.failure .word (.word fellThrough))

example (flag withElse : Bool) :
    ∃ compiledFlow, code flag withElse = Core.LocalControl.finish .word compiledFlow
      (Core.LanguageResult.failure .word (.word fellThrough)) ∧
      ControlStatements.Tree (source flag withElse) reasonAt [] context true statements .word compiledFlow := by
  apply ControlStatements.tree_of_lowerStatements aligned (unique flag withElse)
  change (do
    let compiledFlow ← SourceCoreControl.lowerFlowStatementsWithReasons 20 (source flag withElse) []
      statements .word reasonAt true
    pure (Core.LocalControl.finish .word compiledFlow (Core.LanguageResult.failure .word (.word fellThrough)))) = _
  rw [accepted]
  rfl

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)] }
private theorem tailUnique : NodeOccurrencesUnique tailSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- A nested final expression is discarded; the function tail returns it. -/
example : ControlStatements.Tree tailSource reasonAt [] context false [stmtId 0] .word
    (Core.LocalSequence.discard (Core.LocalControl.controlType .word)
      (Core.LanguageResult.success (.word (word 7))) (Core.LocalControl.fallthrough .word)) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 2) aligned tailUnique (by rfl)

example : ControlStatements.Tree tailSource reasonAt [] context true [stmtId 0] .word
    (Core.LocalControl.returnValue .word (Core.LanguageResult.success (.word (word 7)))) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 2) aligned tailUnique (by rfl)

example : ControlStatements.Tree tailSource reasonAt [] context false [] .word
    (Core.LocalControl.fallthrough .word) :=
  ControlStatements.tree_of_lowerFlowStatements (fuel := 0) aligned tailUnique (by rfl)

private def earlySource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit (.returnStmt none)] }
example : ControlStatements.Tree earlySource reasonAt [] context true [stmtId 0, stmtId 99] .unit
    (Core.LocalControl.returned .unit) := by
  apply ControlStatements.tree_of_lowerFlowStatements (fuel := 1) aligned
    (show NodeOccurrencesUnique earlySource from by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide)
  rfl

end Tests.SourceCoreControlStatementCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreControlStatementMeaning
/-! Actual accepted scoped control preserves heap effects and lexical scope
with an installed administrative closure. These proofs construct no static
Tree or source child evaluation. -/

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Tests.SourceCoreControlStatementMeaning

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"control_statement_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 20⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "control_statement_meaning.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 100)
private def fellThroughReason : Core.Word := word 777
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _

private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 5, stmtId 9, stmtId 10]

/-- The block assigns its local value to the outer cell and discards its last
expression. The conditional's local is also scoped. Its unselected branch and
the unsupported tail after the explicit return remain unexecuted. The block
and if occurrence types are Word, as admitted by the current compiler. -/
private def source : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "1")),
    expressionNode 1 .word (.literal (.decimal "7")),
    expressionNode 2 .word (.reference "inner" (.local (binder 1).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 .word (.literal (.decimal "8")),
    expressionNode 5 .word (.reference "branch" (.local (binder 2).id)),
    expressionNode 6 .word (.literal (.decimal "99")),
    expressionNode 7 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .word (.block [stmtId 2, stmtId 3, stmtId 4]),
    statementNode 2 .unit (.letDecl (binder 1) (some (exprId 1))),
    statementNode 3 .unit (.assignValue assignment .equal (exprId 2)),
    statementNode 4 .word (.expression (exprId 2) false),
    statementNode 5 .word (.ifThen (exprId 3) [stmtId 6, stmtId 7] (some [stmtId 8])),
    statementNode 6 .unit (.letDecl (binder 2) (some (exprId 4))),
    statementNode 7 .word (.expression (exprId 5) false),
    statementNode 8 .word (.returnStmt (some (exprId 6))),
    statementNode 9 .word (.returnStmt (some (exprId 7))),
    statementNode 10 .unit .breakStmt
  ]
}

private def compile (source : TypedSource) (statements : List StatementId) (type : Core.Ty) : Core.Expr :=
  match SourceCoreControl.lowerStatementsWithReasons 20 source [] statements type reasonAt fellThroughReason with
  | .ok code => code
  | .error _ => .unit

private def code : Core.Expr := compile source statements .word
private theorem accepted : SourceCoreControl.lowerStatementsWithReasons 20 source [] statements .word reasonAt fellThroughReason =
    .ok code := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- One typed administrative function cell forms a cycle through its captured
reference. It is not associated with any source heap location. -/
private def functionType : Core.Ty := .function .unit .unit
private def administrativeValue : Core.Value := .closure .unit .unit
  (.apply (.loadCell (.var 1)) (.var 0)) [.cellRef functionType 0]
private def initialWorld : Core.StoreTyping := [functionType]
private def initialStore : Core.Store := [administrativeValue]
private def initialEnvironment : Core.Environment := [.cellRef functionType 0]
private def administrativeContext : Core.Context := [.cell functionType]
private theorem administrativeTyped : Core.RuntimeValueHasType initialWorld administrativeValue functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.apply (.loadCell (.var rfl)) (.var rfl))
private theorem initialHeaps : GeneralHeap.HeapRepresents [] initialWorld ⟨[]⟩ initialStore := by
  refine ⟨rfl, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro index type found
    cases index with
    | zero =>
        have same : functionType = type := by simpa [initialWorld] using found
        subst type
        exact ⟨administrativeValue, rfl, administrativeTyped⟩
    | succ index => simp [initialWorld] at found
  · intro source target impossible; simp at impossible
private theorem initialEnvironments : GeneralHeap.EnvRepresents [] initialWorld administrativeContext
    [] [] initialEnvironment := .nil (.cons (.cellRef rfl) .nil)


/-- Acceptance is the only compiler-specific premise. This obtains the
independent source execution and enough runtime fuel, preserving installed
code and the captured outer environment across both scoped bodies. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld required,
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
      ControlStatements.FinishedOutcomeRepresents program [] source finalMapping finalWorld administrativeContext reasonAt fellThroughReason
        .word outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps).2

example (program : Program) : ∃ finalContext outcome after finalMapping finalWorld finalStore,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    0 ∉ finalMapping ∧ finalStore.read? 0 = some administrativeValue := by
  obtain ⟨_, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, maps, worlds, environments, frame, completes, reflects⟩ :=
    ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps
  obtain ⟨unmapped, same⟩ := frame 0 (by simp) (by decide)
  exact ⟨_, _, _, _, _, _, sourceExecution, heaps, unmapped, same⟩

private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 4].map .statement
  nodes := [expressionNode 0 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 1 .word (.reference "empty" (.local (binder 0).id)),
    expressionNode 2 .word (.literal (.decimal "99")),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .word (.ifThen (exprId 0) [stmtId 2] (some [stmtId 3])),
    statementNode 2 .word (.returnStmt (some (exprId 1))),
    statementNode 3 .word (.returnStmt (some (exprId 2))),
    statementNode 4 .unit (.assignValue assignment .equal (exprId 2))]
}
private def failedStatements : List StatementId := [stmtId 0, stmtId 1, stmtId 4]
private def failedCode : Core.Expr := compile failedSource failedStatements .word

example (program : Program) : ∃ finalContext outcome after result finalStore finalMapping finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩ failedStatements finalContext outcome after ∧
    ControlStatements.FinishedOutcomeRepresents program [] failedSource finalMapping finalWorld administrativeContext reasonAt fellThroughReason
      .word outcome result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore := by
  have accepted : SourceCoreControl.lowerStatementsWithReasons 20 failedSource [] failedStatements .word reasonAt fellThroughReason =
      .ok failedCode := by rfl
  have unique : NodeOccurrencesUnique failedSource := by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  obtain ⟨_, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, _⟩ :=
    ControlStatements.lowerStatements_run_preserves aligned unique accepted .word program [] initialEnvironments initialHeaps
  exact ⟨_, _, _, _, _, _, _, sourceExecution, related, heaps⟩

private def fallsThrough : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.block [stmtId 1]),
    statementNode 1 .word (.expression (exprId 0) false)]
}
/-- Concrete execution regressions are checked by the runner; the independent
source/Core correspondence above is a kernel theorem. -/
def run : IO Unit := do
  unless Core.runStateful 500 (.initial code initialEnvironment initialStore) ==
      .done (.inRight .word (.word (word 7)))
        [administrativeValue, .inRight .unit (.word (word 7)), .inRight .unit (.word (word 7)), .inRight .unit (.word (word 8))] do
    throw (IO.userError "scoped locals did not preserve outer write or administrative code")
  unless Core.runStateful 200 (.initial failedCode initialEnvironment initialStore) ==
      .done (.inLeft .word (.word (reasonAt (exprId 1)))) [administrativeValue, .inLeft .word .unit] do
    throw (IO.userError "fault provider or early exit did not survive scoped control")
  unless Core.runStateful 100 (.initial (compile fallsThrough [stmtId 0] .word) [] []) ==
      .done (.inLeft .word (.word fellThroughReason)) [] do
    throw (IO.userError "non-Unit nested tail should fall through to the missing-return token")
  unless Core.runStateful 100 (.initial (compile fallsThrough [stmtId 0] .unit) [] []) ==
      .done (.inRight .word .unit) [] do
    throw (IO.userError "Unit nested tail should finish with Unit")

end Tests.SourceCoreControlStatementMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreForHeaderCertificates
/-! Actual default header acceptance reconstructs binder context extensions,
a later assignment/read of that binder, and the static normal endpoint. -/

set_option autoImplicit false

namespace Tests.SourceCoreForHeaderCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"for_header_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "for_header_certificate.solc" }, startByte := 0, endByte := 1 }
private def falseNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def readNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "flag" (.local binder.id) }
private def source : TypedSource := { owner, nodes := [.expression falseNode, .expression readNode], roots := [], inputs := [] }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def reason : Core.Word := Core.Word.ofNatModulo 73
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def items : List ForItemForm := [
  .letDecl binder (some (exprId 0)), .assignValue assignment .equal (exprId 0), .expression (exprId 1)]
private def code : Core.Expr := Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .unit) .bool
  (Core.LanguageResult.success (.bool false))
  (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0) (Core.LanguageResult.success (.bool false))
    (Core.LocalSequence.discard (Core.LocalLoop.controlType .unit) (Core.OptionalCell.read .bool (.var 0) reason)
      (Core.LocalLoop.fallthrough .unit)))

private theorem accepted : SourceCoreLoops.lowerForItems (LoopStatements.Default.defaultPolicy compilation)
    (.declaration owner) 10 source [] items .unit (fun _ => reason)
    (fun _ => .ok (Core.LocalLoop.fallthrough .unit)) = .ok code := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private theorem certificate : ForHeaders.Tree compilation source (fun _ => reason) .unit
    (ForHeaders.Fallthrough .unit) [] context items code :=
  ForHeaders.tree_of_lowerPost (BasicStatements.ScopeContextAligned.empty signatures) unique accepted

example : Core.HasType [] code (Core.LocalLoop.resultType .unit) := by
  apply certificate.hasType .unit
  intro scope context code endpoint
  cases endpoint
  exact Core.LocalLoop.fallthrough_hasType .unit

example (result : Core.Expr)
    (accepted : SourceCoreLoops.lowerForItems (LoopStatements.Default.defaultPolicy compilation)
      (.declaration owner) 10 source [] items .unit (fun _ => reason)
      (fun _ => .ok (Core.LocalLoop.fallthrough .unit)) = .ok result) :
    ForHeaders.Tree compilation source (fun _ => reason) .unit (ForHeaders.Fallthrough .unit) [] context items result :=
  ForHeaders.tree_of_lowerPost (BasicStatements.ScopeContextAligned.empty signatures) unique accepted

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible

/-- Header source execution and Core completion are constructed from static
compiler evidence and an empty represented initial state. -/
example (program : Program) :
    ForHeaders.PostResult program context [] source (fun _ => reason) [] ⟨[]⟩ items .unit [] [] [] [] code := by
  have layout : LoopStatements.Layout [] [] [] [] [] Core.Renaming.id :=
    ⟨Core.Renaming.respects_id [], fun found => found, .nil⟩
  simpa only [Core.Expr.rename_id] using certificate.construct_post program [] valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty layout

def run : IO Unit := do
  unless Core.runStateful 300 (.initial code [] []) ==
      .done (Core.LocalLoop.fallthroughValue .unit) [.inRight .unit (.bool false)] do
    throw (IO.userError "for-header initializer scope did not reach the assignment and read")

end Tests.SourceCoreForHeaderCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreForHeaderReachableDiagnostics
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! One header Tree supports unconditional and reachable diagnostics. Concrete
named children close prefix and post reflection while preserving the installed
entry, actual hidden slots and outer scope. Ordinary equal assignments use no
operand table entry; compound and RHS faults retain their ordered effects.
Whole statement/loop Errors and the match Ready factory remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreForHeaderReachableDiagnostics
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
theorem concrete_named_prefix_reflects {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
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
  exact ProtectedForHeader.Tree.reflects_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_reflects
    {administrative : Core.Context} {type : Ty}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
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
    (∃ finalContext finalEnvironment after,
      ∃ tail : ProtectedForHeader.Tail (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions source solved evidence administrative frame globals contextLocation native
        (TypedForHeader.Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) := by
  exact ProtectedForHeader.Tree.reflects_post_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_fault {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact ProtectedForHeader.Tree.preserves_fault_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed trace

end Concrete

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal is valid in the very same static header even when its nonexistent
operand failure has no diagnostic interpretation. -/
theorem equal_header_receipt :
    GenericForHeader.Tree.ReachableErrors registry faults
      (GenericForHeader.Tree.assign (layouts := layouts) (owner := owner) (active := active) (frame := frame)
        (globals := globals) (onError := onError) (type := type) (continuation := TypedForHeader.Fallthrough type)
        head (.nil rfl)) := by
  exact .assign (head := head) (remaining := .nil rfl) (.nil (next := rfl))
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The old stronger premise would require precisely that unreachable token. -/
theorem equal_header_strict_impossible
    (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function copied(value: Word) returns (Word) { let local = value; return local; }",
    "function bad(value: Word) returns (Word) { let local = value; let gap: Word; return gap; }",
    "function initialEqual(seed: Word) returns (Word) { for (let root: Word, root = copied(seed); false; ) { return 99; } return seed; }",
    "function postEqual(seed: Word) returns (Word) { let outer = 17; let index = 0; for (; index < 1; let outer: Word, outer = copied(seed), index = index + 1) { continue; } return outer; }",
    "function initialCompound(seed: Word) returns (Word) { for (let root: Word, root += copied(seed), let never = 99; true; ) { return 99; } return 99; }",
    "function postCompound(seed: Word) returns (Word) { let index = 0; for (; true; let root: Word, root += copied(seed), let never = 99) { index = index + 1; continue; } return 99; }",
    "function initialRhsFault(seed: Word) returns (Word) { for (let root: Word, root = bad(seed), let never = 99; true; ) { return 99; } return 99; }",
    "function postRhsFault(seed: Word) returns (Word) { let index = 0; for (; true; let root: Word, root = bad(seed), let never = 99) { index = index + 1; continue; } return 99; }"
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
private def cells (values : List (Option Nat)) : List (TypeSystem.Ty × Option SourceCoreExecution.Value) :=
  values.map fun value => (.word, value.map scalar)

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "reachable for header fixtures" (checkProgram workspace)
  for (name, result, expectedCells) in [
      ("initialEqual", 7, [some 7, some 7, some 7, some 7]),
      ("postEqual", 17, [some 7, some 17, some 1, some 7, some 7, some 7])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "equal header table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "equal header/post requested a nonexistent operand diagnostic"
    require ((← entry.run [scalar 7]) == scalar result) "equal header/post or outer scope changed"
    entry.checkCells [scalar 7] (cells expectedCells)
    for fuel in [0,7,43] do entry.checkResume [scalar 7] (scalar result) fuel
  for (name, priorCells) in [("initialCompound", [some 7]), ("postCompound", [some 7, some 1])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "compound header table" (SourceCoreAssignmentFaultSites.prepare source 100)
    let node ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .forLoop .. => some node | _ => none
        | _ => none with
      | some node => pure node | none => throw (IO.userError "for fault occurrence missing")
    require (table.length == 1 && table.sites.all fun site => decide
      (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
      "header/post fault table lost owning for occurrence or raw target type"
    failure entry {
      error := .invalidAssignmentOperands .add none (some .word),
      site := .occurrence node.id.occurrence, span := some node.span}
      (cells (priorCells ++ [none, some 7, some 7]))
  for (name, priorCells) in [("initialRhsFault", [some 7]), ("postRhsFault", [some 7, some 1])] do
    let entry ← compileNamed program name
    let ownerSource ← sourceFor entry name
    let table ← get "failed equal header table" (SourceCoreAssignmentFaultSites.prepare ownerSource Core.wordModulus)
    require table.sites.isEmpty "RHS failure caused an equal operand table entry"
    let source ← sourceFor entry "bad"
    let (node, binder) ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
        | _ => none with
      | some selected => pure selected | none => throw (IO.userError "named header RHS fault occurrence missing")
    failure entry {
      error := .uninitializedLocal binder,
      site := .occurrence node.id.occurrence, span := some node.span}
      (cells (priorCells ++ [none, some 7, some 7, none]))
  IO.println "reachable for header/post diagnostics: empty equal table, concrete named children, ordered effects, restored scope, exact faults and resume GREEN"

end Tests.SourceCoreForHeaderReachableDiagnostics
end

section
-- leanmerge: from Solcore.Test.SourceCoreForLoopStatementCertificates
/-! Actual nested `for` acceptance supplies the complete static tree without
the old `NoForLoops` restriction. This test checks extraction and Core typing;
the runner check is a regression, not a whole-loop source preservation proof. -/

set_option autoImplicit false

namespace Tests.SourceCoreForLoopStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"for_loop_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "for_loop_certificate.solc" }, startByte := 0, endByte := 1 }
private def trueNode : ExpressionNode := { id := exprId 0, span := span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := exprId 1, span := span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def readNode : ExpressionNode := { id := exprId 2, span := span, type := .bool, form := .reference "flag" (.local binder.id) }
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def outer : StatementNode := {
  id := stmtId 3, span := span, type := .unit,
  form := .forLoop [.letDecl binder (some (exprId 0))] (exprId 2)
    [.assignValue assignment .equal (exprId 1)] [stmtId 4, stmtId 5] }
private def inner : StatementNode := {
  id := stmtId 4, span := span, type := .unit,
  form := .forLoop [] (exprId 1) [] [] }
private def continuing : StatementNode := { id := stmtId 5, span := span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner := owner,
  nodes := [.expression trueNode, .expression falseNode, .expression readNode,
    .statement outer, .statement inner, .statement continuing],
  roots := [], inputs := [] }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def reason : Core.Word := Core.Word.ofNatModulo 73

private def loopBody : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.iterate .unit (Core.LanguageResult.success (.bool false))
    (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) reason)
  (Core.LocalLoop.continuing .unit)
private def post : Core.Expr := Core.LocalSequence.assign (Core.LocalLoop.controlType .unit)
  (.var 0) (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit)
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .unit) .bool
    (Core.LanguageResult.success (.bool true))
    (Core.LocalLoop.iterate .unit (Core.OptionalCell.read .bool (.var 0) reason) loopBody post reason))
  (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit
  (Core.LocalLoop.toControl .unit flow reason) (Core.LanguageResult.success .unit)

private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 20 compilation source []
    [stmtId 3] .unit (fun _ => reason) reason reason = .ok code := by rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The successful compiler result determines the tree and all body, post,
initializer and nested-loop typing obligations. No execution is supplied. -/
example : ∃ loweredFlow,
    code = Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit loweredFlow reason)
      (Core.LanguageResult.success .unit) ∧
    LoopStatements.WithFor.Tree compilation source (fun _ => reason) reason [] context
      (.statements true [stmtId 3]) .unit loweredFlow ∧
    Core.HasType [] loweredFlow (Core.LocalLoop.resultType .unit) := by
  obtain ⟨loweredFlow, equation, tree⟩ := LoopStatements.WithFor.tree_of_lowerStatements
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted
  exact ⟨loweredFlow, equation, tree, tree.hasType .unit⟩

def run : IO Unit := do
  match Core.runStateful 1000 (.initial code [] []) with
  | .done result store =>
      unless result == .inRight .word .unit do
        throw (IO.userError "nested for did not finish with Unit")
      unless store[0]? == some (.inRight .unit (.bool false)) && store.length == 3 do
        throw (IO.userError "for continue skipped post or nested loop self-cell allocation")
  | _ => throw (IO.userError "nested for did not complete")

end Tests.SourceCoreForLoopStatementCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreForStatementReflection
/-! An actual accepted nested for with continue and post yields an independent
source trace from Core completion alone. The numerical runner regression also
checks the post update and both allocated loop self cells. -/

set_option autoImplicit false

namespace Tests.SourceCoreForStatementReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"for_loop_certificate", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "for_loop_certificate.solc" }, startByte := 0, endByte := 1 }
private def trueNode : ExpressionNode := { id := exprId 0, span := span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := exprId 1, span := span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def readNode : ExpressionNode := { id := exprId 2, span := span, type := .bool, form := .reference "flag" (.local binder.id) }
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def outer : StatementNode := {
  id := stmtId 3, span := span, type := .unit,
  form := .forLoop [.letDecl binder (some (exprId 0))] (exprId 2)
    [.assignValue assignment .equal (exprId 1)] [stmtId 4, stmtId 5] }
private def inner : StatementNode := {
  id := stmtId 4, span := span, type := .unit,
  form := .forLoop [] (exprId 1) [] [] }
private def continuing : StatementNode := { id := stmtId 5, span := span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner := owner,
  nodes := [.expression trueNode, .expression falseNode, .expression readNode,
    .statement outer, .statement inner, .statement continuing],
  roots := [], inputs := [] }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def reason : Core.Word := Core.Word.ofNatModulo 73

private def loopBody : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.iterate .unit (Core.LanguageResult.success (.bool false))
    (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) reason)
  (Core.LocalLoop.continuing .unit)
private def post : Core.Expr := Core.LocalSequence.assign (Core.LocalLoop.controlType .unit)
  (.var 0) (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit)
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .unit) .bool
    (Core.LanguageResult.success (.bool true))
    (Core.LocalLoop.iterate .unit (Core.OptionalCell.read .bool (.var 0) reason) loopBody post reason))
  (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit
  (Core.LocalLoop.toControl .unit flow reason) (Core.LanguageResult.success .unit)

private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 20 compilation source []
    [stmtId 3] .unit (fun _ => reason) reason reason = .ok code := by rfl

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- The successful compiler result determines the tree and all body, post,
initializer and nested-loop typing obligations. No execution is supplied. -/
example : ∃ loweredFlow,
    code = Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit loweredFlow reason)
      (Core.LanguageResult.success .unit) ∧
    LoopStatements.WithFor.Tree compilation source (fun _ => reason) reason [] context
      (.statements true [stmtId 3]) .unit loweredFlow ∧
    Core.HasType [] loweredFlow (Core.LocalLoop.resultType .unit) := by
  obtain ⟨loweredFlow, equation, tree⟩ := LoopStatements.WithFor.tree_of_lowerStatements
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted
  exact ⟨loweredFlow, equation, tree, tree.hasType .unit⟩

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible

/-- No source execution or child execution premise is supplied. -/
example (program : Program) {fuel : Nat} {result : Core.Value} {finalStore : Core.Store}
    (completed : Core.runStateful fuel (.initial code [] []) = .done result finalStore) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason reason
      [] ⟨[]⟩ [stmtId 3] .unit [] [] [] result finalStore :=
  LoopStatements.WithFor.lowerStatements_run_reflects
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty completed

/-- Both finite directions are available at the same actual compiler boundary. -/
example (program : Program) :
    (∃ fuel result finalStore, Core.runStateful fuel (.initial code [] []) = .done result finalStore) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
      [stmtId 3] finalContext outcome after) := by
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [context, Context.ofSignatures] at member
  exact LoopStatements.WithFor.lowerStatements_finite_iff
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid covers
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty

private def administrative : Core.Value := .closure .unit .unit .unit []
private theorem administrativeHeap : GeneralHeap.HeapRepresents [] [.function .unit .unit] ⟨[]⟩ [administrative] :=
  GeneralHeap.HeapRepresents.empty.allocate_administrative (Core.RuntimeValueHasType.closure .nil .unit)

/-- The first source allocation maps to Core location 1 when an unrelated
administrative closure already occupies location 0. -/
example (program : Program) {fuel : Nat} {result : Core.Value} {finalStore : Core.Store}
    (completed : Core.runStateful fuel (.initial code [] [administrative]) = .done result finalStore) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason reason
      [] ⟨[]⟩ [stmtId 3] .unit [] [.function .unit .unit] [administrative] result finalStore :=
  LoopStatements.WithFor.lowerStatements_run_reflects
    (BasicStatements.ScopeContextAligned.empty signatures) unique accepted .unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil) administrativeHeap completed

private def scenario (initializers : List ForItemForm) (condition : ExpressionId)
    (postItems : List ForItemForm) (bodyForm : StatementForm) : TypedSource := {
  source with nodes := [.expression trueNode, .expression falseNode, .expression readNode,
    .statement { outer with form := .forLoop initializers condition postItems [stmtId 5] },
    .statement inner, .statement { continuing with form := bodyForm }] }

private def checkScenario (label : String) (input : TypedSource) (expected : Core.Value)
    (cells : Nat) (firstCell : Core.Value) : IO Unit := do
  let lowered ← match SourceCoreLoops.lowerStatementsWithReasons 20 compilation input [] [stmtId 3]
      .unit (fun _ => reason) reason reason with
    | .ok code => pure code
    | .error _ => throw (IO.userError s!"{label}: lowering failed")
  match Core.runStateful 1000 (.initial lowered [] []) with
  | .done result store =>
      unless result == expected && store.length == cells && store[0]? == some firstCell do
        throw (IO.userError s!"{label}: wrong language outcome or cell effects")
  | _ => throw (IO.userError s!"{label}: did not complete")

def run : IO Unit := do
  match Core.runStateful 1000 (.initial code [] []) with
  | .done result store =>
      unless result == .inRight .word .unit do
        throw (IO.userError "nested for did not finish with Unit")
      unless store[0]? == some (.inRight .unit (.bool false)) && store.length == 3 do
        throw (IO.userError "for continue skipped post or nested loop self-cell allocation")
  | _ => throw (IO.userError "nested for did not complete")
  match Core.runStateful 1000 (.initial code [] [administrative]) with
  | .done result store =>
      unless result == .inRight .word .unit && store.length == 4 &&
          store[0]? == some administrative && store[1]? == some (.inRight .unit (.bool false)) do
        throw (IO.userError "for loop changed the administrative cell or used a source index as a Core index")
  | _ => throw (IO.userError "for loop with an administrative prefix did not complete")
  let initialized := [ForItemForm.letDecl binder (some (exprId 0))]
  let uninitialized := [ForItemForm.letDecl binder none]
  let update := [ForItemForm.assignValue assignment .equal (exprId 1)]
  let succeeds := Core.Value.inRight .word .unit
  let fails := Core.Value.inLeft .unit (.word reason)
  checkScenario "fallthrough executes post"
    (scenario initialized (exprId 2) update (.block [])) succeeds 2 (.inRight .unit (.bool false))
  checkScenario "break skips post"
    (scenario initialized (exprId 2) update .breakStmt) succeeds 2 (.inRight .unit (.bool true))
  checkScenario "return skips post"
    (scenario initialized (exprId 2) update (.returnStmt none)) succeeds 2 (.inRight .unit (.bool true))
  checkScenario "continue reaches post fault"
    (scenario uninitialized (exprId 0) [.expression (exprId 2)] .continueStmt) fails 2 (.inLeft .bool .unit)
  checkScenario "fallthrough reaches post fault"
    (scenario uninitialized (exprId 0) [.expression (exprId 2)] (.block [])) fails 2 (.inLeft .bool .unit)
  checkScenario "initializer fault precedes self installation"
    (scenario (uninitialized ++ [.expression (exprId 2)]) (exprId 0) [] .breakStmt) fails 1 (.inLeft .bool .unit)
  checkScenario "condition fault retains installed self"
    (scenario uninitialized (exprId 2) [] .breakStmt) fails 2 (.inLeft .bool .unit)

end Tests.SourceCoreForStatementReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreFunctionArguments
/-! Parameter allocation over a heap with administrative closure values.
The continuation creates a fresh closure under the actual temporary-binder
layout. No assumption equates that capture with the canonical environment. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionArguments
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Core GeneralHeap FunctionArguments

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"function_arguments", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "parameter", scheme := .mono type }
private def bindings : List (TypedBinder × Ty) := [(binder 0 .word, .word), (binder 1 .bool, .bool)]
private def sources : List Dynamic.Value := [.word Word.zero, .bool true]
private def values : List Value := [.word Word.zero, .bool true]
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def model : GenericHeap.PayloadModel catalog := GenericHeap.finitePayload catalog signatures
private def functionType : Ty := .function .unit .unit
private def administrative : Value := .closure .unit .unit (.var 0) []
private def world : StoreTyping := [functionType]
private def store : Store := [administrative]
private def canonical : Environment := [administrative]
private def actual : Environment := [DataPatternValues.packValues values, .integer 9, administrative]
private def embedding : Renaming := Renaming.insertion 1
private def body : Expr := LanguageResult.success (.lambda .unit .unit .unit)

private theorem represented : Arguments model [] world bindings sources values :=
  .cons ⟨rfl, .word _⟩ (.cons ⟨rfl, .bool _⟩ .nil)

private theorem heaps : GenericHeap.HeapRepresents model [] world ⟨[]⟩ store :=
  GenericHeap.HeapRepresents.empty.allocate_administrative (.closure .nil (.var rfl))

private theorem environments : DataHeap.EnvRepresents catalog [] world [functionType] [] [] canonical :=
  .nil (.cons (.closure .nil (.var rfl)) .nil)

private theorem actualLayout : ReadOnly.EnvironmentsAgree embedding
    (DataPatternValues.packValues values :: canonical) actual :=
  ReadOnly.EnvironmentsAgree.insertion (DataPatternValues.packValues values :: canonical) 1 (.integer 9)

/-- Both source arguments are allocated, then the arbitrary continuation may
capture its real Core environment. Removing the prefix recovers exactly the
same continuation evaluation and store, even for that newly created closure. -/
example : ∃ sourceEnvironment heap finalCanonical captured finalStore mapping finalWorld finalEmbedding,
    Dynamic.BindersAllocate [] ⟨[]⟩ (bindings.map Prod.fst) sources sourceEnvironment heap ∧
    DataHeap.EnvRepresents catalog mapping finalWorld [functionType]
      (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) [])
      sourceEnvironment finalCanonical ∧
    GenericHeap.HeapRepresents model mapping finalWorld heap finalStore ∧
    AdministrativePreserved [] store mapping finalStore ∧
    ReadOnly.EnvironmentsAgree finalEmbedding finalCanonical captured ∧
    Evaluates actual store
      ((SourceCoreFunctions.bindParameters bindings functionType (body.weakenAt bindings.length)).rename embedding)
      (.inRight .word (.closure .unit .unit .unit captured)) finalStore ∧
    (∀ result future,
      Evaluates actual store
        ((SourceCoreFunctions.bindParameters bindings functionType (body.weakenAt bindings.length)).rename embedding)
        result future → Evaluates captured finalStore (body.rename finalEmbedding) result future) := by
  obtain ⟨sourceEnvironment, heap, finalCanonical, captured, finalStore, mapping, finalWorld, finalEmbedding,
    allocated, environments, heaps, _, _, frame, layout, agreement⟩ :=
    parameters_prefix represented (body := body) (outputType := functionType) environments heaps actualLayout
  refine ⟨sourceEnvironment, heap, finalCanonical, captured, finalStore, mapping, finalWorld, finalEmbedding,
    allocated, environments, heaps, frame, layout, agreement.wrap ?_, ?_⟩
  · exact .inRight .lambda
  · intro result future evaluation
    exact agreement.unwrap evaluation

end Tests.SourceCoreFunctionArguments
end

section
-- leanmerge: from Solcore.Test.SourceCoreFunctionCalls
/-! The call composition is instantiated with actual semantic proofs for empty
Unit bodies. Parameter count, lexical captures, administrative values and the
payload model are arbitrary. Neither child execution direction is assumed. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionCalls
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Core GeneralHeap FunctionArguments FunctionCallBody FunctionCalls

private def unitBody : FunctionCode.BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = LanguageResult.success .unit

private theorem empty_preserves {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {faults : FunctionCalls.FaultRep}
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    BodyPreserves model program function unitBody faults := by
  intro scope type body certified context staticFinal facts typed mapping world administrativeContext
    environment canonical actual before store ξ outcome after environments heaps locals layout trace
  obtain ⟨empty, rfl, rfl⟩ := certified
  cases trace with
  | returned execution => rw [empty] at execution; cases execution
  | unit _ execution =>
    rw [empty] at execution
    cases execution
    exact ⟨.inRight .word .unit, store, mapping, world, .inRight .unit,
      .value (resultUnit ▸ unitRep mapping world), heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | fault execution => rw [empty] at execution; cases execution
  | escaped execution escape =>
    rw [empty] at execution
    cases execution
    rcases escape with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

private theorem empty_reflects {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {faults : FunctionCalls.FaultRep}
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    BodyReflects model program function unitBody faults := by
  intro scope type body certified context staticFinal facts typed mapping world administrativeContext
    environment canonical actual before store ξ value finalStore environments heaps locals layout evaluated
  obtain ⟨empty, rfl, rfl⟩ := certified
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated
    (show Evaluates actual store ((LanguageResult.success .unit).rename ξ) (.inRight .word .unit) store from .inRight .unit)
  exact ⟨.value .unit, before, mapping, world, .unit resultUnit (by rw [empty]; exact .nil),
    .value (resultUnit ▸ unitRep mapping world), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

/-- An authenticated empty-body closure with any finite argument list executes
its real parameter wrapper and application. Administrative closures and cyclic
captured cells are allowed by the generic initial heap relation. -/
example {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : SourceSemantics.Program} {function : Dynamic.Closure} {policy : SourceCoreFunctions.Policy}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program unitBody policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) (callerEnvironment : Environment)
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit) :
    ∃ after finalStore finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments (.value .unit) after ∧
      Evaluates (DataPatternValues.packValues values :: actual) store
        (code.artifact.rawBody.rename layout.embedding.lift) (.inRight .word .unit) finalStore ∧
      Evaluates (DataPatternValues.packValues values ::
        FunctionValues.value code.artifact.parameterCore code.artifact.resultCore code.artifact.rawBody layout.embedding actual ::
        callerEnvironment) store (.apply (.second (.var 1)) (.var 0)) (.inRight .word .unit) finalStore ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨_, callContext, _, _, extension, _, _⟩ := frame_body code.frame
  obtain ⟨entry⟩ := entry_exists layout code extension represented heaps locals
  have trace : Trace program function callContext entry.environment entry.heap (.value .unit) entry.heap :=
    .unit resultUnit (by rw [code.artifact.bodyTree.1]; exact .nil)
  have sourceCall : Outcome program context caller function.evidence before (.closure function) arguments (.value .unit) entry.heap :=
    trace.call code.frame extension entry.copy entry.allocation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata⟩ :=
    FunctionCalls.preserves layout code (empty_preserves (faults := fun _ _ => False) unitRep resultUnit)
      represented heaps locals sourceCall
  cases result with
  | @value source value payload =>
    have coreUnit : value = .unit := by
      have typed := model.runtime_hasType payload
      have unitType : code.artifact.resultCore = .unit := code.artifact.bodyTree.2.1
      rw [unitType] at typed
      cases typed
      rfl
    subst value
    exact ⟨entry.heap, finalStore, finalMap, finalWorld, sourceCall, evaluated,
      (FunctionCalls.application_agreement _ _ _ _ _ callerEnvironment _ store).wrap evaluated,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Core-only completion reconstructs an independent source call for the same
body family. The body reflection hypothesis is discharged above. -/
example {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : SourceSemantics.Program} {function : Dynamic.Closure} {policy : SourceCoreFunctions.Policy}
    {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program unitBody policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store finalStore : Store} {arguments : List Dynamic.Value} {values : List Value}
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) {value : Value}
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (unitRep : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
    (resultUnit : function.resultType = .unit)
    (evaluated : Evaluates (DataPatternValues.packValues values :: actual) store
      (code.artifact.rawBody.rename layout.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Outcome program context caller function.evidence before (.closure function) arguments outcome after ∧
      ResultRepresents model finalMap finalWorld function.resultType code.artifact.resultCore (fun _ _ => False) outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  FunctionCalls.reflects layout code (empty_reflects unitRep resultUnit) context caller represented heaps locals evaluated

end Tests.SourceCoreFunctionCalls
end

section
-- leanmerge: from Solcore.Test.SourceCoreFunctionCertificates
/-! Actual lambda lowering, independent source formation, and a cyclic
capture through a mapped cell after administrative layout insertion.  The
body compiler is the existing basic compiler restricted to an empty Unit
body; no body execution appears in the code-authentication premise. -/

set_option autoImplicit false
namespace Tests.SourceCoreFunctionCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap FunctionCode FunctionCaptures

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"function_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def self : Resolved.LocalId := ⟨owner, 0⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "function_certificates.solc"⟩, 0, 1⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def program : Program := ⟨signatures, [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.TaggedFunction.functionType .unit .unit
private def cellType : Core.Ty := Core.OptionalCell.cellType functionType
private def scope : SourceCoreLocalCell.Scope := [(self, functionType)]
private def node : ExpressionNode := { id, span, type := sourceType, form := .lambda [] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression node] }
private def context : SourceSemantics.Context := {
  (SourceSemantics.Context.ofSignatures signatures).withLocal self (.mono sourceType) [] with
  currentDeclaration := some owner, residualTypeVariables := true }
private def function : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [], source
  captured := [(self, ⟨0⟩)], context, evidence := [] }
private def compilation : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0
  solvedRequirements := [], internalReason := Core.Word.zero }
private def policy : SourceCoreFunctions.Policy := {}
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun _ budget source scope statements result _ reason _ =>
    SourceCoreBasic.lowerStatements budget source scope statements result reason
private def bodyCertificate : BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = Core.LanguageResult.success .unit
private def emitted : SourceCoreBasic.LoweredExpr := ⟨functionType,
  Core.LanguageResult.success (Core.TaggedFunction.anonymous
    (.lambda .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit)))⟩

private theorem artifact_exists : Nonempty
    (LambdaCertificate bodyCertificate policy source scope id node [] .unit [] functionType emitted) := by
  apply lambda_of_accepted (ordinaryCells := rfl) (ordinaryBody := rfl) (ordinaryExpression := rfl) (lowerBody := lowerBody) (fuel := 1) (context := compilation)
    (reasonAt := fun _ => Core.Word.zero) rfl rfl rfl rfl rfl rfl
  · intro budget bodyScope type code accepted
    simp only [lowerBody, SourceCoreBasic.lowerStatements] at accepted
    split at accepted
    · next same => cases accepted; exact ⟨rfl, same, rfl⟩
    · cases accepted
  · cbv

private noncomputable def artifact : LambdaCertificate bodyCertificate policy source scope id node [] .unit [] functionType emitted :=
  Classical.choice artifact_exists

private theorem parameter_type : artifact.parameterCore = .unit := by
  have selected := artifact.parameterProjection
  rw [← artifact.bundle] at selected
  exact Except.ok.inj selected.symm

private theorem result_type : artifact.resultCore = .unit := Except.ok.inj artifact.resultProjection.symm

private theorem graph : OccurrenceGraphWellFormed source := by
  constructor
  · unfold NodeOccurrencesUnique nodeOccurrenceIds
    decide
  · intro selected member
    simp only [source, List.mem_singleton] at member
    subst selected
    rfl
  · intro root member
    simp only [source, List.mem_singleton] at member
    subst root
    rfl
  · intro root member
    simpa [source, nodeIds, Node.id, node] using member
  · intro selected member child childMember
    simp only [source, List.mem_singleton] at member
    subst selected
    cases childMember

private theorem frame : Dynamic.ClosureFrame program function := by
  have unique : RequirementIdsUnique context := by
    simp [RequirementIdsUnique, context, Context.withLocal, Context.ofSignatures]
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence impossible
      cases impossible
    · intro predicate impossible
      cases impossible
  refine ⟨rfl, rfl, ?_, unique, covers⟩
  refine ⟨rfl, rfl, rfl, rfl, graph, ⟨unique, ?_⟩, ?_⟩
  · intro row evidence member
    cases member
  · refine ⟨id, node, ⟨by change Node.expression node ∈ [Node.expression node]; exact List.mem_singleton_self _, rfl⟩, rfl, rfl, ?_⟩
    exact .lambda (by decide) (.nil _) (.nil _ _) ⟨rfl, rfl, .inr rfl⟩

private def world : Core.StoreTyping := [.word, .unit, cellType]
private def canonical : Core.Environment := [.cellRef cellType 2, .bool false]
private def actual : Core.Environment := [.integer 11, .cellRef cellType 2, .bool false]
private def sourceHeap : Dynamic.Heap := ⟨[⟨sourceType, none, none⟩]⟩
private def store : Core.Store := [.word Core.Word.zero, .unit, .inLeft functionType .unit]
private def layout : Layout catalog [2] world scope function.captured actual where
  administrativeContext := [.bool]
  canonical := canonical
  actualContext := [.integer, .cell cellType, .bool]
  embedding := Core.Renaming.insertion 0
  represented := .cons ⟨rfl, rfl⟩ (.nil (.cons .bool .nil))
  lookups := Core.ReadOnly.EnvironmentsAgree.insertion canonical 0 (.integer 11)
  types := Core.Renaming.insertion_respects_insertAt [.cell cellType, .bool] 0 .integer
  actualTyped := .cons .integer (.cons (.cellRef rfl) (.cons .bool .nil))

private def captures : Certificate catalog [2] world sourceHeap context scope function.captured actual :=
  ⟨layout, .cons (.intro .head) rfl (.ordinary rfl rfl) .nil⟩

private noncomputable def code : FunctionValues.Code catalog program bodyCertificate policy function scope [.bool] where
  id := id
  node := node
  reportedType := functionType
  lowered := emitted
  artifact := artifact
  frame := frame
  projection := by
    rw [parameter_type, result_type]
    rfl
  outputTyped := by
    rw [parameter_type, result_type]
    exact .inRight .word (.pair (.inLeft .word .unit) (.lambda .unit (.sum .word .unit) (.inRight .word .unit)))

/-- The source cell can be uninitialized when the closure captures it. -/
example : FunctionValues.SourceCapturesValid sourceHeap (.closure function) := captures.sourceMetadata

private def model : GenericHeap.PayloadModel catalog := FunctionValues.model catalog program bodyCertificate policy
private noncomputable def generated : Core.Value :=
  FunctionValues.value artifact.parameterCore artifact.resultCore artifact.rawBody layout.embedding actual
private theorem represented : model.Represents [2] world sourceType (.closure function) generated functionType := by
  have related := FunctionValues.Represents.closure layout code
  change FunctionValues.Represents catalog program bodyCertificate policy [2] world sourceType
    (.closure function) generated (Core.TaggedFunction.functionType artifact.parameterCore artifact.resultCore) at related
  rw [parameter_type, result_type] at related
  exact related

private theorem initialHeap : GenericHeap.HeapRepresents model [2] world sourceHeap store := by
  have empty := GenericHeap.HeapRepresents.empty (model := model)
  have administrative := (empty.allocate_administrative (.word (value := Core.Word.zero))).allocate_administrative .unit
  exact (administrative.allocate (.uninitialized rfl) .append).1

/-- The actual lowering certificate gives independent source formation and a
Core closure over its copies of the creation environment, which keep the
inserted Integer slot. -/
example : ∃ captured finalHeap finalStore,
    Dynamic.ExpressionEvaluates program context [] source function.captured sourceHeap id
      (.closure { function with captured := captured }) finalHeap ∧
    ∃ embedding closureActual, Core.Evaluates actual store (emitted.expression.rename layout.embedding)
      (.inRight .word (FunctionValues.value code.artifact.parameterCore code.artifact.resultCore
        code.artifact.rawBody embedding closureActual)) finalStore := by
  obtain ⟨captured, finalHeap, finalStore, _, _, closureActual, embedding, formed, evaluated, _⟩ :=
    FunctionValues.formation_corresponds layout code initialHeap rfl rfl
  exact ⟨captured, finalHeap, finalStore, formed, embedding, closureActual, evaluated⟩

private def installedHeap : Dynamic.Heap := ⟨[⟨sourceType, some (.closure function), none⟩]⟩
private noncomputable def installedStore : Core.Store := [.word Core.Word.zero, .unit, .inRight .unit generated]

/-- The generated closure can be installed in the cell it captures. The
source and Core indices differ, and no recursive heap-unfolding proof is used. -/
private theorem installed : GenericHeap.HeapRepresents model [2] world installedHeap installedStore := by
  obtain ⟨updated, written, related, _⟩ := initialHeap.write_initialized
    (reference := ⟨rfl, rfl⟩) (.intro .head) represented (.intro (.intro .head) .head)
  have exactWrite : store.write? 2 (.inRight .unit generated) = some installedStore := rfl
  have same := Option.some.inj (written.symm.trans exactWrite)
  exact same ▸ related

example : Core.RuntimeStoreHasTypes world installedStore catalog.definitions := installed.runtime_hasTypes

example : GenericHeap.HeapRepresents model [2] (world ++ [.integer]) installedHeap
    (installedStore ++ [.integer 81]) := installed.allocate_administrative .integer

example : Dynamic.ValueHasType context installedHeap (.closure function) sourceType :=
  FunctionValues.Represents.source_hasType represented rfl
    (.cons (.intro .head) rfl (.ordinary rfl rfl) .nil)

example (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities functionType (.closure function) generated :=
  FunctionValues.Represents.observation represented signatures identities

end Tests.SourceCoreFunctionCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralExpressionNativeTyping
/-! Actual lowering of a logical operation above product-key indexing closes its
base and both key components without native child callbacks. Hidden slots and
ambient definitions remain arbitrary. The existing recursive/general IO suites
exercise the production compiler's tags, lazy initialization, faults and resume. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreGeneralExpressionNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral CompatibleExpressionScalarNativeTyping
open CompatibleExpressionGeneralNativeTyping CompatibleCatalogNominalCoverage

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"index_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "index_meaning.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def keyType : TypeSystem.Ty := .product .bool .bool
private def mappingType : TypeSystem.Ty := .mapping keyType .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def trueNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := id 2, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def keyNode : ExpressionNode := { id := id 3, span, type := keyType, form := .tuple [id 1, id 2] }
private def indexNode : ExpressionNode := { id := id 4, span, type := .bool, form := .index (id 0) (id 3) }
private def unaryNode : ExpressionNode := { id := id 5, span, type := .bool, form := .unary .logicalNot (id 4) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 5)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode, .expression unaryNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem keyAdmitted : TypeAdmissible context keyType := .product boolAdmitted boolAdmitted
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping keyAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem trueTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := trueNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem falseTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := falseNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 3) keyType := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := keyType)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons trueTyped (.cons falseTyped (.nil _)))) keyAdmitted keyAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 4) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary indexTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionGeneral.Syntax source (id 4) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv)
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl)))))))
    (.pair (node := keyNode) (by cbv) rfl
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := trueNode) (by cbv) (.bool _ _))))))))
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := falseNode) (by cbv) (.bool _ _)))))))))
private theorem syntaxTree : CompatibleExpressionGeneral.Syntax source (id 5) :=
  .unary (node := unaryNode) (by cbv) rfl indexSyntax
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) unaryTyped accepted

private theorem actual_factory : SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType] = .ok checked := by cbv

private theorem visibleTypes : ScopeWellFormed checked.catalog.definitions scope := by
  apply ScopeWellFormed.prepend (.empty _) binder.id
  exact Ty.isWellFormed_sound (by cbv)

/-- Independent source typing, actual lowering and factory acceptance close
all native base/key/parent obligations for this compound-key example. -/
theorem product_key_below_unary_native {code : SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (administrative : Core.Context)
    (extension : checked.catalog.definitions.Extends definitions)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5)
      (fun _ => reason) = .ok code) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) code := by
  have shaped := prepare_shapes actual_factory
  rw [← SourceCoreCompatibleCatalog.prepare_signatures actual_factory] at shaped
  exact general_native_at shaped (prepare_complete actual_factory) visibleTypes administrative extension (certified accepted)

private def compiledAction := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope
  (id 5) (fun _ => reason)

theorem actual_contextual_general_native
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment} (administrative : Core.Context)
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (ordinary : CompatibleExpressionGeneral.Ordinary source locals compilation.owner)
    (unique : SourceSemantics.NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : SourceSemantics.ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  CompatibleExpressionGeneralNativeTyping.contextual_native visibleTypes administrative registered ordinary unique closed residual declarations sourceSignatures
    syntaxTree found sourceTyped readPolicy lowerPolicy leafPolicy accepted extension


def run : IO Unit := do
  match compiledAction with
  | .error error => throw (IO.userError s!"product-key native fixture failed to compile: {repr error}")
  | .ok code =>
    if code.type != .bool then throw (IO.userError "product-key parent result type changed")
    if Core.infer? (SourceCoreLocalCell.coreContext scope ++ [.integer, .function .unit .word])
        code.expression checked.catalog.definitions != some (LanguageResult.resultType .bool) then
      throw (IO.userError "product-key native fixture failed native type inference under hidden slots")
  IO.println "general expression native typing: actual product-key parent, hidden slots and native inference GREEN"

end Tests.SourceCoreGeneralExpressionNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralExpressions
/-! Actual primitive compilation and independent semantics over a heap with
interleaved administrative recursive function cells and source locations.
Temporary lexical values must not alter captured closures or stored payloads. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "general_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .bool)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := Context.ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private def source : TypedSource := {
  owner
  inputs := [{ id := binder 0, name := "flag", scheme := .mono .bool },
    { id := binder 1, name := "number", scheme := .mono .word },
    { id := binder 2, name := "right", scheme := .mono .bool }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.product .word .bool) (.group (id 1)),
    node 1 (.product .word .bool) (.tuple [id 2, id 8]),
    node 2 .word (.conditional (id 3) (id 4) (id 7)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.binary (id 5) .add (id 6)),
    node 5 .word (.literal (.decimal "17")),
    node 6 .word (.reference "number" (.local (binder 1))),
    node 7 .word (.unary .bitNot (id 6)),
    node 8 .bool (.binary (id 9) .logicalAnd (id 10)),
    node 9 .bool (.unary .logicalNot (id 3)),
    node 10 .bool (.reference "right" (.local (binder 2)))]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair .word .bool
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (SourceCorePrimitive.binary .add
        (Core.LanguageResult.success (.word (word 17)))
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6))))
      (Core.LocalPrimitiveResults.unary .wordNot
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6)))))
    (Core.LocalPrimitiveResults.logicalAnd
      (Core.LocalPrimitiveResults.unary .boolNot
        (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3))))
      (Core.OptionalCell.read .bool (.var 2) (reasonAt (id 10))))
private theorem accepted : SourceCorePrimitive.lowerExpressionWithReasons 5 compilation source scope (id 0) reasonAt =
    .ok ⟨.product .word .bool, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

private def boolCell (value : Option Bool) : Dynamic.Cell := { type := .bool, value := value.map .bool }
private def wordCell (value : Option Nat) : Dynamic.Cell := { type := .word, value := value.map fun n => .word (word n) }
private def boolStored : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def wordStored : Option Nat → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word (word value))
private def heap (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Dynamic.Heap :=
  ⟨[boolCell flag, wordCell number, boolCell right]⟩
private def functionType : Core.Ty := .function .unit .unit
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def identityFunction : Core.Value := .closure .unit .unit (.var 0) []
private def recursiveFunction : Core.Value := .closure .unit .unit
  (.caseE (.loadCell (.var 1)) .unit (.apply (.var 0) (.var 1)))
  [.cellRef optionalFunction 0]
private def world : Core.StoreTyping := [optionalFunction, Core.OptionalCell.cellType .bool,
  functionType, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def mapping : GeneralHeap.LocationMap := [1, 3, 4]
private def store (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Core.Store :=
  [.inRight .unit recursiveFunction, boolStored flag, recursiveFunction, wordStored number, boolStored right]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def administrativeContext : Core.Context := [.cell optionalFunction, .cell functionType]
private def coreEnvironment : Core.Environment := [
  .cellRef (Core.OptionalCell.cellType .bool) 1,
  .cellRef (Core.OptionalCell.cellType .word) 3,
  .cellRef (Core.OptionalCell.cellType .bool) 4,
  .cellRef optionalFunction 0, .cellRef functionType 2]
private theorem environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) (.cons (.cellRef rfl) .nil)))))
private theorem boolRelated (value : Option Bool) : LocalCell.CellRepresents (boolCell value) (boolStored value) .bool := by
  cases value with
  | none => exact .uninitialized .bool
  | some value => exact .initialized (.bool value)
private theorem wordRelated (value : Option Nat) : LocalCell.CellRepresents (wordCell value) (wordStored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word (word value))
private theorem recursiveTyped : Core.RuntimeValueHasType world recursiveFunction functionType := by
  exact .closure (.cons (.cellRef rfl) .nil)
    (.caseE (.loadCell (.var rfl)) .unit (.apply (.var rfl) (.var rfl)))
private theorem heaps (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    GeneralHeap.HeapRepresents mapping world (heap flag number right) (store flag number right) := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  have flagRelated := (admin.allocate (boolRelated flag) .append).1
  have extra := flagRelated.allocate_administrative
    (show Core.RuntimeValueHasType _ identityFunction functionType from .closure .nil (.var rfl))
  have numberRelated := (extra.allocate (wordRelated number) .append).1
  have original := (numberRelated.allocate (boolRelated right) .append).1
  have initial : GeneralHeap.HeapRepresents mapping world (heap flag number right)
      [.inLeft functionType .unit, boolStored flag, identityFunction, wordStored number, boolStored right] := original
  have installed : GeneralHeap.HeapRepresents mapping world (heap flag number right)
      [.inRight .unit recursiveFunction, boolStored flag, identityFunction, wordStored number, boolStored right] := by
    apply initial.write_administrative (location := 0) (type := optionalFunction)
    · intro index found
      have member := List.mem_of_getElem? found
      simp [mapping] at member
    · rfl
    · exact .inRight recursiveTyped
    · rfl
  apply installed.write_administrative (location := 2) (type := functionType)
  · intro index found
    have member := List.mem_of_getElem? found
    simp [mapping] at member
  · rfl
  · exact recursiveTyped
  · rfl

/-- Arbitrary ordinary input initialization is allowed alongside administrative
recursive functions. The derived source and Core results need no child
execution assumptions and no first-order invariant for the complete store. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code =
      some (Core.LanguageResult.resultType (.product .word .bool)) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag number right) (id 0) sourceOutcome (heap flag number right) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap flag number right) reasonAt (id 0) (.product .word .bool) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done coreValue (store flag number right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag number right) :=
  GeneralExpressions.Primitive.lowerExpression_run_preserves unique accepted program context evidence contextValid
    environments (heaps flag number right)

private theorem readOnly : Core.ReadOnly.Expression code := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact GeneralExpressions.Primitive.readOnly tree

private theorem run_shortCircuit : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) (some 3) none)) =
    .done (.inRight .word (.pair (.word (word 20)) (.bool false))) (store (some true) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_rightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some false) (some 3) none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 10)))) (store (some false) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_arithmeticRightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 6)))) (store (some true) none none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- The same actual compiler output evaluates under a temporary binder at
an arbitrary cutoff. Even the inserted value can itself be a closure. -/
example (cutoff : Nat) :
    Core.Evaluates (Core.Environment.insertAt coreEnvironment cutoff recursiveFunction)
      (store (some true) (some 3) none) (code.weakenAt cutoff)
      (.inRight .word (.pair (.word (word 20)) (.bool false))) (store (some true) (some 3) none) :=
  readOnly.evaluation_weakenAt (Core.runStateful_evaluation_sound run_shortCircuit) cutoff recursiveFunction

/-- Administrative closure cells retain their exact values after a completed
expression, including after the short-circuit RHS is actually evaluated and
fails at its own source read occurrence. -/
example : (store (some false) (some 3) none).read? 0 = some (.inRight .unit recursiveFunction) := rfl
example : (store (some false) (some 3) none).read? 2 = some recursiveFunction := rfl

example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap (some false) (some 3) none) (id 0) sourceOutcome (heap (some false) (some 3) none) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap (some false) (some 3) none) reasonAt (id 0) (.product .word .bool) sourceOutcome
        (.inLeft (.product .word .bool) (.word (reasonAt (id 10)))) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, represented, coreEvaluation⟩ :=
    GeneralExpressions.Primitive.lowerExpression_preserves unique accepted program context evidence contextValid
      environments (heaps (some false) (some 3) none)
  have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run_rightFault) coreEvaluation
  exact ⟨sourceOutcome, sourceEvaluation, same.1 ▸ represented⟩

/-- The restriction really excludes closure creation and calls. -/
example : ¬ Core.ReadOnly.Expression (.lambda .unit .unit (.var 0)) := by intro impossible; cases impossible
example : ¬ Core.ReadOnly.Expression (.apply (.var 0) (.var 1)) := by intro impossible; cases impossible

end Tests.SourceCoreGeneralExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralFunctions
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreGeneralFunctions

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function leaf(value: Word) returns (Tree) { return .Leaf(value); }",
    "function branch(left: Tree, right: Tree) returns (Tree) { return .Pair(left, right); }",
    "function choose(flag: Bool, value: Word) returns (Tree) { return flag ? leaf(value) : .Pair(leaf(value), leaf(value + 1)); }",
    "function mutate(value: Tree, replacement: Tree) returns (Tree) {",
    " let setter: function(Tree) returns (Tree) = lam(next: Tree) -> Tree { value = next; return value; };",
    " setter(replacement); return value; }",
    "function transform(value: Tree, change: function(Tree) returns (Tree)) returns (Tree) { return change(value); }",
    "function through(value: Tree) returns (Tree) { return transform(value, lam(input: Tree) -> Tree { return .Pair(input, input); }); }",
    "function recurse(count: Word, value: Tree) returns (Tree) { return count == 0 ? value : recurse(count - 1, Tree.Pair(value, value)); }",
    "function proxyValue() returns (@Word) { return @Word; }",
    "function find(table: mapping(Word => Word), key: Word) returns (Word) { return table[key]; }",
    "function empty() returns (Word) { let table: mapping(Word => Word); return table[1]; }",
    "function missing(table: mapping(Word => Tree), key: Word) returns (Tree) { return table[key]; }",
    "function absent() returns (Tree) { let value: Tree; return value; }"
    , "function select(value: Tree) returns (Word) { match (value) { case .Leaf(x) { return x; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 0; } } }"
    , "function patternCall(value: Tree) returns (Word) { let out: Word; match (value) { case .Leaf(x) { let f: function() returns (Word) = lam() -> Word { return x; }; out = f(); } default { out = 0; } } return out; }"
    , "function matchContinue(value: Tree) returns (Word) { let count: Word = 0; while (count < 2) { count += 1; match (value) { case .Leaf(x) { continue; } default { break; } } count += 10; } return count; }"
  ] }]
}

private def entryFor (program : CheckedProgram) (checked : SourceCoreDataCatalog.Checked) (name : String) :
    IO (SourceCoreGeneralEntry.Entry checked) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"general function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"general plan failed: {reprStr result}")
  match SourceCoreGeneralFunctions.prepareWithCatalog program plan checked 256 with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "general seed count changed")
  | .error error => throw (IO.userError s!"{name} general compilation failed: {reprStr error}")

private def expect {checked : SourceCoreDataCatalog.Checked} (entry : SourceCoreGeneralEntry.Entry checked)
    (arguments : List Core.Value) (expected : Core.Value) : IO Unit := do
  for _ in [0, 1] do
    match entry.run arguments 32768 with
    | .ok result => match result.observation with
        | .succeeded actual _ => assertTrue (actual == expected) s!"general function result changed: {reprStr actual}"
        | observation => throw (IO.userError s!"general function failed: {reprStr observation}")
    | .error error => throw (IO.userError s!"general input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"general source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "Tree signature missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 256
      [treeType, .mapping .word .word, .mapping .word treeType, .proxy .word,
       .function treeType treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"general catalog failed: {reprStr error}")
  let treeId ← match checked.catalog.identity? treeType with
    | some id => pure id
    | none => throw (IO.userError "Tree Core identity missing")
  let leaf := fun value => Core.Value.constructed ⟨treeId, 0⟩ (word value)
  let pair := fun left right => Core.Value.constructed ⟨treeId, 1⟩ (.pair left right)
  expect (← entryFor program checked "leaf") [word 17] (leaf 17)
  expect (← entryFor program checked "branch") [leaf 2, leaf 3] (pair (leaf 2) (leaf 3))
  let choose ← entryFor program checked "choose"
  expect choose [.bool true, word 9] (leaf 9)
  expect choose [.bool false, word 9] (pair (leaf 9) (leaf 10))
  -- The setter assigns only its call's copy of the captured `value`.
  expect (← entryFor program checked "mutate") [leaf 1, pair (leaf 8) (leaf 9)] (leaf 1)
  expect (← entryFor program checked "through") [leaf 7] (pair (leaf 7) (leaf 7))
  let recursive ← entryFor program checked "recurse"
  let twice := pair (leaf 4) (leaf 4)
  expect recursive [word 2, leaf 4] (pair twice twice)
  match recursive.run [word 2, leaf 4] 8 with
  | .ok result => match result.checkpoint? with
      | some checkpoint =>
          match (checkpoint.resume 32768).observation with
          | .succeeded actual _ => assertTrue (actual == pair twice twice) "general checkpoint lost recursive data"
          | other => throw (IO.userError s!"general resume failed: {reprStr other}")
      | none => throw (IO.userError "general recursion did not suspend")
  | .error error => throw (IO.userError s!"general checkpoint input rejected: {reprStr error}")
  let proxy ← match checked.catalog.proxyValue? .word with
    | some value => pure value
    | none => throw (IO.userError "proxy representation missing")
  expect (← entryFor program checked "proxyValue") [] proxy
  let mapId ← match checked.catalog.identity? (.mapping .word .word) with
    | some id => pure id
    | none => throw (IO.userError "mapping representation missing")
  let layout : Core.OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  let find ← entryFor program checked "find"
  let mapping := Core.OrderedMapping.encode layout [(word 3, word 41), (word 7, word 99)]
  expect find [mapping, word 7] (word 99)
  expect find [mapping, word 8] (word 0)
  let empty ← entryFor program checked "empty"
  expect empty [] (word 0)
  match empty.run [] 32768 with
  | .ok result => match result.observation with
      | .succeeded _ store =>
          assertTrue (store.contains (.inRight .unit (Core.OrderedMapping.encode layout [])))
            "uninitialized mapping read did not install its empty value"
      | other => throw (IO.userError s!"empty mapping failed: {reprStr other}")
  | .error error => throw (IO.userError s!"empty mapping input failed: {reprStr error}")
  let missing ← entryFor program checked "missing"
  let emptyTreeMap ← match checked.catalog.emptyMapping? .word treeType with
    | some value => pure value
    | none => throw (IO.userError "Tree mapping representation missing")
  match missing.run [emptyTreeMap, word 2] 32768 with
  | .ok result => match result.observation with
      | .failed reason _ => match missing.failureDiagnostic? reason with
          | some diagnostic =>
              assertTrue (decide (diagnostic.error = .typeMismatch treeType none) && diagnostic.span.isSome)
                "missing mapping default lost its error or source span"
          | none => throw (IO.userError "missing mapping default lost its diagnostic")
      | other => throw (IO.userError s!"missing mapping default changed: {reprStr other}")
  | .error error => throw (IO.userError s!"missing mapping input failed: {reprStr error}")
  let absent ← entryFor program checked "absent"
  match absent.run [] 32768 with
  | .ok result => match result.observation with
      | .failed reason _ => assertTrue ((absent.failureDiagnostic? reason).isSome) "nominal absence lost diagnostic"
      | other => throw (IO.userError s!"nominal absence changed: {reprStr other}")
  | .error error => throw (IO.userError s!"nominal absence input failed: {reprStr error}")
  let select ← entryFor program checked "select"
  expect select [leaf 7] (word 7)
  expect select [pair (leaf 8) (leaf 9)] (word 17)
  expect select [pair (pair (leaf 1) (leaf 2)) (leaf 3)] (word 0)
  expect (← entryFor program checked "patternCall") [leaf 42] (word 42)
  let matchContinue ← entryFor program checked "matchContinue"
  expect matchContinue [leaf 7] (word 2)
  expect matchContinue [pair (leaf 7) (leaf 8)] (word 1)
  IO.println "general Core functions with recursive data GREEN"

end Tests.SourceCoreGeneralFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralHeap
/-! Source cells need not occupy the same Core indices, or even share one
constant offset. Administrative closures can capture mapped source cells and
form cycles through an optional function cell without recursively typing the
store. These are representation tests, not source-closure execution proofs. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralHeap

open Solcore Solcore.Frontend Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def functionType : Core.Ty := .function .unit (Core.LanguageResult.resultType .word)
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def optionalWord : Core.Ty := Core.OptionalCell.cellType .word
private def world : Core.StoreTyping := [optionalFunction, optionalWord]
private def sourceCell (value : Nat) : Dynamic.Cell := { type := .word, value := some (.word (word value)) }
private def sourceHeap (value : Nat) : Dynamic.Heap := ⟨[sourceCell value]⟩
private def presentWord (value : Nat) : Core.Value := .inRight .unit (.word (word value))
private def before : Core.Store := [.inLeft functionType .unit, presentWord 7]
private theorem beforeRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 7) before := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  exact (admin.allocate (.initialized (.word (word 7))) .append).1

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_heap", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def capture : Core.Environment := [.cellRef optionalWord 1, .cellRef optionalFunction 0]
private def sourceCapture : Dynamic.Environment := [(binder, ⟨0⟩)]
private def scope : SourceCoreLocalCell.Scope := [(binder, .word)]
private theorem captures : GeneralHeap.EnvRepresents [1] world [.cell optionalFunction]
    scope sourceCapture capture :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) .nil))

/-- The function may call its own optional cell. The capture includes both
that cell and the mutable source cell, so the resulting store is cyclic. -/
private def body : Core.Expr :=
  .caseE (.loadCell (.var 2)) (.inLeft .word (.word (word 90))) (.apply (.var 0) (.var 1))
private def function : Core.Value := .closure .unit (Core.LanguageResult.resultType .word) body capture
private theorem functionTyped : Core.RuntimeValueHasType world function functionType := by
  apply Core.RuntimeValueHasType.closure captures.runtime_hasTypes
  exact .caseE (.loadCell (.var rfl)) (.inLeft .word .word) (.apply (.var rfl) (.var rfl))
private def installed : Core.Store := [.inRight .unit function, presentWord 7]
private theorem installedRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 7) installed := by
  apply beforeRelated.write_administrative (location := 0) (type := optionalFunction)
  · intro index impossible
    cases index <;> simp at impossible
  · rfl
  · exact .inRight functionTyped
  · rfl

/-- The complete store typing is finite even though cell zero contains a
closure whose captured environment refers back to cell zero. -/
example : Core.RuntimeStoreHasTypes world installed := installedRelated.runtime_hasTypes

private theorem sourceWritten : Dynamic.Heap.Writes (sourceHeap 7) ⟨0⟩
    (some (.word (word 9))) (sourceHeap 9) :=
  .intro (.intro .head) .head
private def updated : Core.Store := [.inRight .unit function, presentWord 9]
private theorem updatedRelated : GeneralHeap.HeapRepresents [1] world (sourceHeap 9) updated := by
  obtain ⟨actual, written, related⟩ := installedRelated.write_initialized
    (reference := ⟨rfl, rfl⟩) (.word (word 9)) rfl sourceWritten
  have expected : installed.write? 1 (presentWord 9) = some updated := rfl
  have same : actual = updated := Option.some.inj (written.symm.trans expected)
  exact same ▸ related

/-- Captures keep the original reference and see the new source cell value.
The administrative recursive closure stays installed at index zero. -/
example : Core.Evaluates capture updated
    (Core.OptionalCell.read .word (.var 0) (word 91))
    (.inRight .word (.word (word 9))) updated :=
  Core.OptionalCell.read_success _ (.var rfl) rfl
example : updated.read? 0 = some (.inRight .unit function) := rfl
example : ∃ source target cell value,
    Dynamic.Environment.LooksUp sourceCapture binder source ∧
    capture[0]? = some (.cellRef optionalWord target) ∧
    GeneralHeap.ReferenceRepresents [1] world source target .word ∧
    Dynamic.Heap.Reads (sourceHeap 9) source cell ∧ updated.read? target = some value ∧
    LocalCell.CellRepresents cell value .word :=
  captures.lookup_heap updatedRelated rfl

private def administrativeWorld : Core.StoreTyping := world ++ [functionType]
private def administrativeStore : Core.Store := updated ++ [function]
private theorem administrativeRelated : GeneralHeap.HeapRepresents [1]
    administrativeWorld (sourceHeap 9) administrativeStore :=
  updatedRelated.allocate_administrative functionTyped

/-- Adding a second administrative function cell does not allocate any source
location. The next source cell consequently maps to Core index three. -/
private def finalHeap : Dynamic.Heap := ⟨(sourceHeap 9).cells ++ [{ type := .bool, value := none }]⟩
private def finalWorld : Core.StoreTyping := administrativeWorld ++ [Core.OptionalCell.cellType .bool]
private def finalStore : Core.Store := administrativeStore ++ [.inLeft .bool .unit]
private theorem finalRelated : GeneralHeap.HeapRepresents [1, 3] finalWorld finalHeap finalStore :=
  (administrativeRelated.allocate (.uninitialized .bool) .append).1
example : GeneralHeap.ReferenceRepresents [1, 3] finalWorld ⟨1⟩ 3 .bool :=
  (administrativeRelated.allocate (.uninitialized .bool) .append).2
example : GeneralHeap.EnvRepresents [1, 3] finalWorld [.cell optionalFunction] scope sourceCapture capture :=
  captures.extend ⟨[3], rfl⟩ ⟨[functionType, Core.OptionalCell.cellType .bool], rfl⟩
example : Core.RuntimeStoreHasTypes finalWorld finalStore := finalRelated.runtime_hasTypes
example : finalStore.read? 1 = some (presentWord 9) := rfl
example : finalStore.read? 3 = some (.inLeft .bool .unit) := rfl

/-- The identity-map embedding reuses every existing exact-index heap proof. -/
example : GeneralHeap.HeapRepresents [0] [optionalWord] (sourceHeap 9) [presentWord 9] :=
  GeneralHeap.HeapRepresents.of_exact (.cons (.initialized (.word (word 9))) .nil)

/-- Distinct source cells cannot map to one Core location. -/
example : ¬ GeneralHeap.LocationMap.Injective [1, 1] := by
  intro injective
  have impossible : 0 = 1 := injective rfl rfl
  cases impossible

private def readId : SourceInference.ExpressionId := ⟨⟨owner, 0⟩⟩
private def readNode : SourceInference.ExpressionNode := {
  id := readId
  span := { source := { origin := .main, path := "general_heap.solc" }, startByte := 0, endByte := 1 }
  type := .word
  form := .reference "shared" (.local binder)
}
private def readSource : SourceInference.TypedSource := {
  owner, inputs := [], roots := [.expression readId], nodes := [.expression readNode]
}
private def readSite : LocalCell.ReadSite readSource scope readId .word := {
  node := readNode, binder, name := "shared", index := 0
  contains := lookupExpression?_sound rfl
  form := rfl, owner := rfl, requirements := rfl, coercions := rfl, slot := rfl, types := .word
}
private theorem readUnique : NodeOccurrencesUnique readSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
example : SourceCoreLocalCell.lowerRead readSource scope readId (word 91) =
    .ok (Core.OptionalCell.read .word (.var 0) (word 91)) := readSite.lower readUnique _

/-- The independent source read of source location zero corresponds to a
Core read of location one in the cyclic administrative heap. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ location target sourceOutcome coreValue,
      GeneralHeap.ReferenceRepresents [1] world location target .word ∧
      Dynamic.ExpressionEvaluatesOutcome program context evidence readSource sourceCapture
        (sourceHeap 9) readId sourceOutcome (sourceHeap 9) ∧
      LocalCell.OutcomeRepresents location (word 91) sourceOutcome coreValue ∧
      Core.Evaluates capture updated (Core.OptionalCell.read .word (.var 0) (word 91)) coreValue updated :=
  GeneralHeap.read_preserves readSite program context evidence captures updatedRelated _

end Tests.SourceCoreGeneralHeap
end

section
-- leanmerge: from Solcore.Test.SourceCoreGeneralStatements
/-! Complete basic statement sequences execute over an administrative cyclic
closure heap. Source cells receive independent Core indices, writes preserve
installed code, and source initialization failures skip subsequent effects. -/

set_option autoImplicit false

namespace Tests.SourceCoreGeneralStatements

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"general_statements", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "general_statements.solc" }
  startByte := 0
  endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reason : Core.Word := word 73
private def resultType : Core.Ty := .product .word .bool
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := (List.range 6).map stmtId

/-- `let a: Word; let b = 7; a = b; b; return (a, true); { ... }`.
The unsupported final block is skipped by the actual explicit return branch. -/
private def source : TypedSource := {
  owner
  inputs := []
  roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.reference "b" (.local (binder 1).id)),
    expressionNode 2 .word (.reference "a" (.local (binder 0).id)),
    expressionNode 3 .bool (.reference "true" (.builtinBoolean true)),
    expressionNode 4 (.product .word .bool) (.tuple [exprId 2, exprId 3]),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.assignValue assignment .equal (exprId 1)),
    statementNode 3 .unit (.expression (exprId 1) true),
    statementNode 4 (.product .word .bool) (.returnStmt (some (exprId 4))),
    statementNode 5 .unit (.block [])
  ]
}
private def code : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized resultType .word (Core.LanguageResult.success (.word (word 7)))
      (Core.LocalSequence.assign resultType (.var 1) (Core.OptionalCell.read .word (.var 0) reason)
        (Core.LocalSequence.discard resultType (Core.OptionalCell.read .word (.var 0) reason)
          (Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
            (Core.LanguageResult.success (.bool true))))))

private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private def firstContext : SourceSemantics.Context :=
  context.withLocal (binder 0).id (binder 0).scheme
private def secondContext : SourceSemantics.Context :=
  firstContext.withLocal (binder 1).id (binder 1).scheme

private theorem firstExtension : BinderExtends owner context (binder 0) firstContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, context, Context.ofSignatures]

private theorem secondExtension : BinderExtends owner firstContext (binder 1) secondContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, firstContext, context, Context.ofSignatures, Context.withLocal]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word
      }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl
    }
  · simp [LocalFresh, firstContext, context, Context.ofSignatures, Context.withLocal, binder]

private def statement (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : StatementNode :=
  { id := stmtId index, span, type, form }
private def bothScope : SourceCoreBasic.Scope := [((binder 1).id, .word), ((binder 0).id, .word)]

private theorem certificate : ∃ depth, BasicStatements.Tree source reason [] context
    statements resultType code depth := by
  obtain ⟨initializerDepth, _, initializer⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.LanguageResult.success (.word (word 7))⟩) (by rfl)
  obtain ⟨localDepth, _, localRead⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := source) (scope := bothScope) (id := exprId 1) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  obtain ⟨pairDepth, _, pair⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 2) (source := source) (scope := bothScope) (id := exprId 4) (reason := reason)
    (lowered := ⟨resultType, Core.LocalSequence.pair .word .bool (Core.OptionalCell.read .word (.var 1) reason)
      (Core.LanguageResult.success (.bool true))⟩) (by rfl)
  have returned := BasicStatements.Tree.returnValue (context := secondContext) [stmtId 5]
    ((BasicStatements.readStatement_certificate
      (id := stmtId 4) (node := statement 4 (.product .word .bool) (.returnStmt (some (exprId 4)))) (by rfl)).2)
    (by rfl) pair
  have discarded := BasicStatements.Tree.discard
    ((BasicStatements.readStatement_certificate
      (id := stmtId 3) (node := statement 3 .unit (.expression (exprId 1) true)) (by rfl)).2)
    (by rfl) localRead returned
  have assigned := BasicStatements.Tree.assign
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.assignValue assignment .equal (exprId 1))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerAssignment_certificate (index := 1) (by rfl)) localRead discarded
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension initializer assigned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

/-- One typed administrative function cell forms a cycle through its captured
reference. It is not associated with any source heap location. -/
private def functionType : Core.Ty := .function .unit .unit
private def administrativeValue : Core.Value := .closure .unit .unit
  (.apply (.loadCell (.var 1)) (.var 0)) [.cellRef functionType 0]
private def initialWorld : Core.StoreTyping := [functionType]
private def initialStore : Core.Store := [administrativeValue]
private def initialEnvironment : Core.Environment := [.cellRef functionType 0]
private def administrativeContext : Core.Context := [.cell functionType]
private theorem administrativeTyped : Core.RuntimeValueHasType initialWorld administrativeValue functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.apply (.loadCell (.var rfl)) (.var rfl))
private theorem initialHeaps : GeneralHeap.HeapRepresents [] initialWorld ⟨[]⟩ initialStore := by
  refine ⟨rfl, ?_, ⟨rfl, ?_⟩, ?_⟩
  · intro left right target impossible; simp at impossible
  · intro index type found
    cases index with
    | zero =>
        have same : functionType = type := by simpa [initialWorld] using found
        subst type
        exact ⟨administrativeValue, rfl, administrativeTyped⟩
    | succ index => simp [initialWorld] at found
  · intro source target impossible; simp at impossible
private theorem initialEnvironments : GeneralHeap.EnvRepresents [] initialWorld administrativeContext
    [] [] initialEnvironment := .nil (.cons (.cellRef rfl) .nil)

/-- The entire source list follows from a static certificate. Final mapping,
world, heap, original captures and administrative cells all remain related. -/
example (program : Program) :
    ∃ compilationFuel finalContext outcome after result finalStore finalMapping finalWorld required,
      SourceCoreBasic.lowerStatements compilationFuel source [] statements resultType reason = .ok code ∧
      Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩
        statements finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason resultType outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.EnvRepresents finalMapping finalWorld administrativeContext [] [] initialEnvironment ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code initialEnvironment initialStore) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨lowered, _, finalContext, outcome, after, result, finalStore, finalMapping, finalWorld, required,
    sourceExecution, related, heaps, mapsExtended, worldsExtended, captured, frame, completes, reflects⟩ :=
    GeneralStatements.lower_run_preserves tree unique depth (Nat.le_refl _) program [] initialEnvironments initialHeaps
  exact ⟨_, _, _, _, _, _, _, _, _, lowered, sourceExecution, related, heaps,
    mapsExtended, worldsExtended, captured, frame, completes, reflects⟩

private def finalStore : Core.Store := [administrativeValue,
  .inRight .unit (.word (word 7)), .inRight .unit (.word (word 7))]
private theorem executed : Core.runStateful 200 (.initial code initialEnvironment initialStore) =
    .done (.inRight .word (.pair (.word (word 7)) (.bool true))) finalStore := by
  simp [code, resultType, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.LocalSequence.assign, Core.LocalSequence.discard, Core.LocalSequence.pair,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- Allocation and assignment under any inserted lexical binder produce the
same value and complete final store, including its captured closure. -/
example (cutoff : Nat) : Core.Evaluates
    (Core.Environment.insertAt initialEnvironment cutoff administrativeValue) initialStore (code.weakenAt cutoff)
    (.inRight .word (.pair (.word (word 7)) (.bool true))) finalStore := by
  obtain ⟨depth, tree⟩ := certificate
  exact (GeneralStatements.heapEffects tree).evaluation_weakenAt
    (Core.runStateful_evaluation_sound executed) cutoff administrativeValue

/-- The frame theorem exposes the unchanged installed function cell even
without knowing the concrete final mapping or final heap in advance. -/
example (program : Program) : ∃ outcome after finalMapping finalWorld finalContext finalStore,
    Dynamic.FunctionStatementsExecuteOutcome program context [] source [] ⟨[]⟩ statements finalContext outcome after ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    0 ∉ finalMapping ∧ finalStore.read? 0 = some administrativeValue := by
  obtain ⟨depth, tree⟩ := certificate
  obtain ⟨finalContext, outcome, after, result, finalStore, finalMapping, finalWorld,
    sourceExecution, related, coreExecution, heaps, mapsExtended, worldsExtended, frame⟩ :=
    GeneralStatements.preserves tree unique program [] initialEnvironments initialHeaps
  obtain ⟨unmapped, same⟩ := frame 0 (by simp) (by decide)
  exact ⟨outcome, after, finalMapping, finalWorld, finalContext, finalStore,
    sourceExecution, heaps, unmapped, same⟩

/-- Loading and storing an existing closure is admitted by the restricted
Core grammar. No lambda is evaluated, so renaming keeps that closure exact. -/
example (inserted : Core.Value) :
    Core.Evaluates (inserted :: initialEnvironment) initialStore
      ((Core.Expr.storeCell (.var 0) (.loadCell (.var 0))).weakenAt 0) .unit initialStore := by
  have evaluated : Core.Evaluates initialEnvironment initialStore
      (.storeCell (.var 0) (.loadCell (.var 0))) .unit initialStore :=
    .storeCell (.var rfl) rfl (.loadCell (.var rfl) rfl) rfl
  exact (Core.HeapEffects.Expression.storeCell .var (.loadCell .var)).evaluation_weakenAt_zero evaluated inserted

example : ¬ Core.HeapEffects.Expression (.lambda .unit .unit (.var 0)) := by intro impossible; cases impossible
example : ¬ Core.HeapEffects.Expression (.apply (.var 0) (.var 1)) := by intro impossible; cases impossible

private def failedSource : TypedSource := {
  owner, inputs := [], roots := [stmtId 0, stmtId 1, stmtId 2].map .statement
  nodes := [expressionNode 0 .word (.reference "a" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) none),
    statementNode 1 .unit (.letDecl (binder 1) (some (exprId 0))),
    statementNode 2 .unit (.returnStmt none)]
}
private def failedCode : Core.Expr :=
  Core.LocalSequence.letUninitialized .word
    (Core.LocalSequence.letInitialized .unit .word (Core.OptionalCell.read .word (.var 0) reason)
      (Core.LanguageResult.success .unit))
private theorem failedCertificate : ∃ depth, BasicStatements.Tree failedSource reason [] context
    [stmtId 0, stmtId 1, stmtId 2] .unit failedCode depth := by
  obtain ⟨valueDepth, _, value⟩ := BasicExpressions.tree_of_lowerExpression
    (fuel := 1) (source := failedSource) (scope := [((binder 0).id, .word)]) (id := exprId 0) (reason := reason)
    (lowered := ⟨.word, Core.OptionalCell.read .word (.var 0) reason⟩) (by rfl)
  have returned := BasicStatements.Tree.returnUnit (source := failedSource) (reason := reason)
    (context := secondContext) (scope := bothScope) []
    ((BasicStatements.readStatement_certificate
      (id := stmtId 2) (node := statement 2 .unit (.returnStmt none)) (by rfl)).2) (by rfl)
  have initialized := BasicStatements.Tree.letInitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 1) (node := statement 1 .unit (.letDecl (binder 1) (some (exprId 0)))) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) secondExtension value returned
  exact ⟨_, BasicStatements.Tree.letUninitialized
    ((BasicStatements.readStatement_certificate
      (id := stmtId 0) (node := statement 0 .unit (.letDecl (binder 0) none)) (by rfl)).2)
    (by rfl) (BasicStatements.lowerBinder_certificate (by rfl)) firstExtension initialized⟩

/-- A failed initializer leaves the administrative closure and only the first
source allocation; the second allocation and return remain unexecuted. -/
example (program : Program) :
    ∃ finalContext outcome after result finalStore finalMapping finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program context [] failedSource [] ⟨[]⟩
        [stmtId 0, stmtId 1, stmtId 2] finalContext outcome after ∧
      GeneralStatements.OutcomeRepresents finalMapping finalWorld administrativeContext reason .unit outcome result ∧
      Core.Evaluates initialEnvironment initialStore failedCode result finalStore ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends [] finalMapping ∧ Core.WorldExtends initialWorld finalWorld ∧
      GeneralHeap.AdministrativePreserved [] initialStore finalMapping finalStore := by
  obtain ⟨depth, tree⟩ := failedCertificate
  have unique : NodeOccurrencesUnique failedSource := by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  exact GeneralStatements.preserves tree unique program [] initialEnvironments initialHeaps

example : Core.runStateful 100 (.initial failedCode initialEnvironment initialStore) =
    .done (.inLeft .unit (.word reason)) [administrativeValue, .inLeft .word .unit] := by
  simp [failedCode, Core.LocalSequence.letUninitialized, Core.LocalSequence.letInitialized,
    Core.OptionalCell.allocate, Core.OptionalCell.allocateInitialized, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

end Tests.SourceCoreGeneralStatements
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoopBranchReflection
/-! Focused scoped-head reverse tests. Compiler acceptance supplies the guard
tree; child reconstruction uses primitive list helpers. The concrete tests
supply only Core executions and represented initial state. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopBranchReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements LoopStatements.Reflection

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"branch_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 1⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "branch_reflection.solc" }, startByte := 0, endByte := 1 }
private def guardNode (flag : Bool) : ExpressionNode := {
  id := exprId, span, type := .bool, form := .reference "flag" (.builtinBoolean flag) }
private def breakNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .breakStmt }
private def continueNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .continueStmt }
private def blockNode : StatementNode := { id := stmtId 3, span, type := .unit, form := .block [stmtId 1] }
private def ifNode (withElse : Bool) : StatementNode := {
  id := stmtId 0, span, type := .unit,
  form := .ifThen exprId [stmtId 1] (if withElse then some [stmtId 2] else none) }
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0), .statement (stmtId 3)],
  nodes := [.expression (guardNode flag), .statement (ifNode withElse),
    .statement breakNode, .statement continueNode, .statement blockNode] }
private def reason : Core.Word := Core.Word.ofNatModulo 17
private def reasonAt (_ : ExpressionId) : Core.Word := reason
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
    (Core.LocalLoop.breaking .unit)
    (if withElse then Core.LocalLoop.continuing .unit else Core.LocalLoop.fallthrough .unit)

private theorem contains_if (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 0) (ifNode withElse) := by
  simp [ContainsStatement, source, ifNode]
private theorem contains_break (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 1) breakNode := by
  simp [ContainsStatement, source, breakNode]
private theorem contains_continue (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 2) continueNode := by
  simp [ContainsStatement, source, continueNode]
private theorem contains_block (flag withElse : Bool) :
    ContainsStatement (source flag withElse) (stmtId 3) blockNode := by
  simp [ContainsStatement, source, blockNode]

private theorem if_reflects (flag withElse : Bool) (program : Program)
    (evidence : Dynamic.EvidenceEnvironment) :
    ScopedReflects compilation program evidence (source flag withElse) reasonAt [] context
      (stmtId 0) .unit (code flag withElse) := by
  have unique : NodeOccurrencesUnique (source flag withElse) := by
    unfold NodeOccurrencesUnique nodeOccurrenceIds
    cases flag <;> cases withElse <;> decide
  have accepted : SourceCorePrimitive.lowerExpressionWithReasons 1 compilation (source flag withElse)
      [] exprId reasonAt = .ok ⟨.bool, Core.LanguageResult.success (.bool flag)⟩ := by rfl
  obtain ⟨depth, _, guardTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  have breaking : Reflects compilation program evidence (source flag withElse) reasonAt [] context
      false [stmtId 1] .unit (Core.LocalLoop.breaking .unit) :=
    reflects_breaking (contains_break flag withElse) (show breakNode.form = .breakStmt from rfl)
    (program := program) (evidence := evidence) (context := context) (compilation := compilation)
    (reasonAt := reasonAt) (scope := []) (mode := false) (rest := []) (type := .unit)
  cases withElse with
  | false =>
    change ScopedReflects _ _ _ _ _ _ _ _ _
      (Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
        (Core.LocalLoop.breaking .unit) (Core.LocalLoop.fallthrough .unit))
    exact reflects_if_head (contains_if flag false) rfl guardTree breaking
      (reflects_nil compilation program evidence (source flag false) reasonAt [] context false .unit)
  | true =>
    change ScopedReflects _ _ _ _ _ _ _ _ _
      (Core.LocalLoop.conditional .unit (Core.LanguageResult.success (.bool flag))
        (Core.LocalLoop.breaking .unit) (Core.LocalLoop.continuing .unit))
    exact reflects_if_head (contains_if flag true) rfl guardTree breaking
      (reflects_continuing (contains_continue flag true) rfl)

/-- Block restoration uses the child list's reconstructed break outcome. -/
example (flag withElse : Bool) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedReflects compilation program evidence (source flag withElse) reasonAt [] context
      (stmtId 3) .unit (Core.LocalLoop.breaking .unit) :=
  reflects_block_head (contains_block flag withElse) rfl
    (reflects_breaking (contains_break flag withElse) rfl)

private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private theorem layout : Layout [] [] [] [] [] Core.Renaming.id := by
  refine ⟨?_, ?_, .nil⟩
  · intro index type found; cases found
  · intro index value found; cases found

private theorem reconstruct (flag withElse : Bool) (program : Program)
    (evidence : Dynamic.EvidenceEnvironment) {result : Core.Value}
    (evaluated : Core.Evaluates [] [] (code flag withElse) result []) :
    ScopedResult program context evidence (source flag withElse) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] result [] := by
  apply if_reflects flag withElse program evidence Core.Ty.WellFormed.unit valid
    (GeneralHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil)
    GeneralHeap.HeapRepresents.empty layout
  simpa only [Core.Expr.rename_id] using evaluated

/-- True chooses break even when an else branch exists. -/
example (withElse : Bool) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source true withElse) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.breakingValue .unit) [] := by
  apply reconstruct true withElse program evidence
  exact Core.LocalControl.choose_true (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.breaking, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inRight (.inLeft .unit)))

/-- An absent else reconstructs the source's false-without-else rule. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source false false) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.fallthroughValue .unit) [] := by
  apply reconstruct false false program evidence
  exact Core.LocalControl.choose_false (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inLeft (.inLeft .unit)))

/-- A present else reconstructs continue and restores the enclosing scope. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ScopedResult program context evidence (source false true) reasonAt [] ⟨[]⟩ (stmtId 0)
      .unit [] [] [] (Core.LocalLoop.continuingValue .unit) [] := by
  apply reconstruct false true program evidence
  exact Core.LocalControl.choose_false (Core.LocalLoop.controlType .unit)
    (.inRight .bool) (by simp [Core.LocalLoop.continuing, Core.LanguageResult.success, Core.Expr.weakenAt]; exact .inRight (.inRight (.inRight .unit)))

end Tests.SourceCoreLoopBranchReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoopFiniteComposition
/-! A finite independent while trace changes its captured Boolean cell, takes
continue, rechecks the guard, and exits. The concrete compiled Core installs a
self cell and preserves its exact closure across that source write. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopFiniteComposition

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"finite_loop", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "finite_loop.solc" }, startByte := 0, endByte := 1
}
private def readReason : Core.Word := Core.Word.ofNatModulo 11
private def selfReason : Core.Word := Core.Word.ofNatModulo 12
private def assignment : AssignmentResolution := { target := { root := binder, projections := [], type := .bool } }
private def guardNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "flag" (.local binder) }
private def falseNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def assignNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .assignValue assignment .equal (exprId 1) }
private def continueNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner, inputs := [{ id := binder, name := "flag", scheme := .mono .bool }]
  roots := [.statement (stmtId 0)]
  nodes := [.expression guardNode, .expression falseNode,
    .statement { id := stmtId 0, span, type := .unit, form := .whileLoop (exprId 0) [stmtId 1, stmtId 2] },
    .statement assignNode, .statement continueNode]
}
private def scope : SourceCoreBasic.Scope := [(binder, .bool)]
private def sourceEnvironment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def sourceHeap (value : Bool) : Dynamic.Heap := ⟨[{ type := .bool, value := some (.bool value) }]⟩
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .bool) 0]
private def conditionCode : Core.Expr := Core.OptionalCell.read .bool (.var 0) readReason
private def bodyCode : Core.Expr := Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0)
  (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit)
private def whileCode : Core.Expr := Core.LocalLoop.whileLoop .unit conditionCode bodyCode selfReason
private def code : Core.Expr := Core.LocalLoop.sequence .unit whileCode (Core.LocalLoop.fallthrough .unit)
private def initialStore : Core.Store := [.inRight .unit (.bool true)]
private def selfClosure : Core.Value := Core.LocalLoop.installedClosure .unit conditionCode bodyCode
  (Core.LocalLoop.fallthrough .unit) selfReason 1 coreEnvironment
private def loopStore (value : Bool) : Core.Store := [.inRight .unit (.bool value), .inRight .unit selfClosure]

private theorem accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
    (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel { solvedRequirements := [] } source scope id reasons)
    5 source scope [stmtId 0] .unit (fun _ => readReason) false selfReason = .ok code := by rfl

private theorem guard_contains : ContainsExpression source (exprId 0) guardNode := ⟨by simp [source], rfl⟩
private theorem false_contains : ContainsExpression source (exprId 1) falseNode := ⟨by simp [source], rfl⟩
private theorem assign_contains : ContainsStatement source (stmtId 1) assignNode := ⟨by simp [source], rfl⟩
private theorem continue_contains : ContainsStatement source (stmtId 2) continueNode := ⟨by simp [source], rfl⟩

private theorem source_guard (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (value : Bool) :
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment (sourceHeap value) (exprId 0) (.bool value) (sourceHeap value) :=
  .intro guard_contains (.local rfl .head (.intro .head) rfl rfl) .nil

private theorem source_false (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment (sourceHeap true) (exprId 1) (.bool false) (sourceHeap true) :=
  .intro false_contains (.builtinBoolean rfl) .nil

private theorem source_assignment (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment (sourceHeap true) assignment.target (exprId 1) (.bool false) (sourceHeap false) :=
  .intro (.intro .head (.intro .head) .nil (.intro .head) .initialized .nil)
    (source_false program context evidence)
    (.intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head))

private theorem source_body (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.StatementsExecute program context evidence source sourceEnvironment (sourceHeap true) [stmtId 1, stmtId 2]
      context (.continuing sourceEnvironment) (sourceHeap false) :=
  .cons (.assignValue assign_contains rfl (source_assignment program context evidence))
    (.terminal (.continueStmt continue_contains rfl) (.continuing _))

/-- The finite source derivation itself supplies the two guard observations. -/
private theorem source_while (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.WhileExecutes program context evidence source sourceEnvironment (sourceHeap true) (exprId 0) [stmtId 1, stmtId 2]
      context (.fallthrough sourceEnvironment) (sourceHeap false) :=
  .nextContinue (source_guard program context evidence true) (source_body program context evidence)
    (.done (source_guard program context evidence false))

private theorem body_restricted : Core.HeapEffects.Expression bodyCode := by
  have rhs : Core.HeapEffects.Expression (Core.LanguageResult.success (.bool false)) := .inRight .bool
  have next : Core.HeapEffects.Expression (Core.LocalLoop.continuing .unit) := .inRight (.inRight (.inRight .unit))
  exact .letE .var (.caseE (rhs.weakenAt 0) (.inLeft .var)
    (.letE (.storeCell .var (.inRight .var)) (((next.weakenAt 0).weakenAt 0).weakenAt 0)))

private theorem condition_evaluates (value : Bool) :
    Core.Evaluates coreEnvironment (loopStore value) conditionCode (.inRight .word (.bool value)) (loopStore value) :=
  Core.OptionalCell.read_success readReason (.var rfl) rfl

private theorem body_evaluates : Core.Evaluates coreEnvironment (loopStore true) bodyCode
    (Core.LocalLoop.continuingValue .unit) (loopStore false) := by
  refine Core.LocalSequence.assign_success (referenceStore := loopStore true) (rhsStore := loopStore true)
    (writtenStore := loopStore false) (oldValue := .inRight .unit (.bool true)) (value := .bool false)
    _ (.var rfl) ?_ rfl rfl ?_
  · simp [Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight .bool
  · simp [Core.LocalLoop.continuing, Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight (.inRight (.inRight .unit))

private theorem core_trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode selfReason 1 coreEnvironment
    (loopStore true) (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := by
  have conditionRestricted : Core.ReadOnly.Expression conditionCode := .caseE (.loadCell .var) (.inLeft .word) (.inRight .var)
  have conditionTrue := (conditionRestricted.weakenAt 0).evaluation_weakenAt_zero
    (conditionRestricted.evaluation_weakenAt_zero (condition_evaluates true)
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit
  have conditionFalse := (conditionRestricted.weakenAt 0).evaluation_weakenAt_zero
    (conditionRestricted.evaluation_weakenAt_zero (condition_evaluates false)
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit
  have shiftedBody := ((body_restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((body_restricted.weakenAt 0).evaluation_weakenAt_zero
      (body_restricted.evaluation_weakenAt_zero body_evaluates
        (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit) (.bool true)
  exact .nextContinue conditionTrue shiftedBody rfl (.done conditionFalse)

private theorem core_while : Core.Evaluates coreEnvironment initialStore whileCode
    (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := core_trace.whileLoop_evaluates

private theorem core_flow : Core.Evaluates coreEnvironment initialStore code
    (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := by
  apply Core.LocalLoop.sequence_fallthrough _ core_while
  simp [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight (.inLeft (.inLeft .unit))

/-- Actual accepted code, an independent finite source loop, and a finite Core
execution agree on the source cell and retain the installed self closure. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel { solvedRequirements := [] } source scope id reasons)
      5 source scope [stmtId 0] .unit (fun _ => readReason) false selfReason = .ok code ∧
    Dynamic.WhileExecutes program context evidence source sourceEnvironment (sourceHeap true) (exprId 0) [stmtId 1, stmtId 2]
      context (.fallthrough sourceEnvironment) (sourceHeap false) ∧
    Core.Evaluates coreEnvironment initialStore code (Core.LocalLoop.fallthroughValue .unit) (loopStore false) :=
  ⟨accepted, source_while program context evidence, core_flow⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 400 (.initial code coreEnvironment initialStore) ==
    .done (Core.LocalLoop.fallthroughValue .unit) (loopStore false))
    "continue did not update its captured cell, recheck the guard, or retain the self closure"

end Tests.SourceCoreLoopFiniteComposition
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoopStatementCertificates
/-! Extraction from actual default lowering, with no assumed child trees or
execution derivations. The fixtures cover scoped while bodies, both branch
shapes, break/continue, assignment, both local allocation forms, and function
versus nested-list tail conventions. A for loop is accepted by the compiler
but deliberately outside this certificate's static grammar. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementCertificates

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_certificates", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def binder (index : Nat) : TypedBinder :=
  { id := ⟨owner, index⟩, name := "local", scheme := .mono .word }
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_certificates.solc" }, startByte := 0, endByte := 1 }
private def expressionNode (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := exprId index, span, type, form }
private def statementNode (index : Nat) (type : TypeSystem.Ty) (form : StatementForm) : Node :=
  .statement { id := stmtId index, span, type, form }
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (id : ExpressionId) : Core.Word := word (id.occurrence.index + 50)
private def fellThrough : Core.Word := word 99
private def escaped : Core.Word := word 100
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := .ofSignatures {
  functions := [], implRules := [], traits := [], implementations := [] }
private theorem aligned : BasicStatements.ScopeContextAligned [] context :=
  BasicStatements.ScopeContextAligned.empty _
private def assignment : AssignmentResolution :=
  { target := { root := (binder 0).id, projections := [], type := .word } }
private def statements : List StatementId := [stmtId 0, stmtId 1, stmtId 8]

/-- The inner scope has two locals; assignment addresses the outer local at
index two. The loop body's locals are absent from the outer implicit return. -/
private def source (flag withElse : Bool) : TypedSource := {
  owner, inputs := [], roots := statements.map .statement
  nodes := [
    expressionNode 0 .word (.literal (.decimal "7")),
    expressionNode 1 .word (.literal (.decimal "9")),
    expressionNode 2 .bool (.reference "flag" (.builtinBoolean flag)),
    expressionNode 3 .word (.reference "inner" (.local (binder 2).id)),
    expressionNode 4 .word (.reference "outer" (.local (binder 0).id)),
    statementNode 0 .unit (.letDecl (binder 0) (some (exprId 0))),
    statementNode 1 .unit (.whileLoop (exprId 2) [stmtId 2, stmtId 3]),
    statementNode 2 .unit (.letDecl (binder 1) none),
    statementNode 3 .unit (.block [stmtId 4, stmtId 5, stmtId 7]),
    statementNode 4 .unit (.letDecl (binder 2) (some (exprId 1))),
    statementNode 5 .unit (.ifThen (exprId 2) [stmtId 6]
      (if withElse then some [stmtId 9] else none)),
    statementNode 6 .unit .continueStmt,
    statementNode 7 .unit (.assignValue assignment .equal (exprId 3)),
    statementNode 8 .word (.expression (exprId 4) false),
    statementNode 9 .unit .breakStmt
  ] }

private def flow (flag withElse : Bool) : Core.Expr :=
  Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .word) .word
    (Core.LanguageResult.success (.word (word 7)))
    (Core.LocalLoop.sequence .word
      (Core.LocalLoop.whileLoop .word (Core.LanguageResult.success (.bool flag))
        (Core.LocalSequence.letUninitialized .word
          (Core.LocalLoop.sequence .word
            (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType .word) .word
              (Core.LanguageResult.success (.word (word 9)))
              (Core.LocalLoop.sequence .word
                (Core.LocalLoop.conditional .word (Core.LanguageResult.success (.bool flag))
                  (Core.LocalLoop.continuing .word)
                  (if withElse then Core.LocalLoop.breaking .word else Core.LocalLoop.fallthrough .word))
                (Core.LocalSequence.assign (Core.LocalLoop.controlType .word) (.var 2)
                  (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 3)))
                  (Core.LocalLoop.fallthrough .word))))
            (Core.LocalLoop.fallthrough .word))) escaped)
      (Core.LocalLoop.returnValue .word (Core.OptionalCell.read .word (.var 0) (reasonAt (exprId 4)))))

private theorem unique (flag withElse : Bool) : NodeOccurrencesUnique (source flag withElse) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases flag <;> cases withElse <;> decide

private theorem noFor (flag withElse : Bool) : NoForLoops (source flag withElse) := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [source, expressionNode, statementNode] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

private theorem accepted (flag withElse : Bool) :
    SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 20 (source flag withElse)
      [] statements .word reasonAt true escaped = .ok (flow flag withElse) := by
  cases withElse <;> rfl

example (flag withElse : Bool) : Tree compilation (source flag withElse) reasonAt escaped [] context true
    statements .word (flow flag withElse) :=
  tree_of_lowerFlowStatements aligned (unique flag withElse) (noFor flag withElse) (accepted flag withElse)

example (flag withElse : Bool) : Core.HasType [] (flow flag withElse) (Core.LocalLoop.resultType .word) :=
  (tree_of_lowerFlowStatements aligned (unique flag withElse) (noFor flag withElse) (accepted flag withElse)).hasType .word

private def code (flag withElse : Bool) : Core.Expr :=
  Core.LocalControl.finish .word (Core.LocalLoop.toControl .word (flow flag withElse) escaped)
    (Core.LanguageResult.failure .word (.word fellThrough))

example (flag withElse : Bool) :
    ∃ compiledFlow, code flag withElse = Core.LocalControl.finish .word
      (Core.LocalLoop.toControl .word compiledFlow escaped) (Core.LanguageResult.failure .word (.word fellThrough)) ∧
      Tree compilation (source flag withElse) reasonAt escaped [] context true statements .word compiledFlow := by
  apply tree_of_lowerStatements aligned (unique flag withElse) (noFor flag withElse)
  change (do
    let compiledFlow ← SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 20
      (source flag withElse) [] statements .word reasonAt true escaped
    pure (Core.LocalControl.finish .word (Core.LocalLoop.toControl .word compiledFlow escaped)
      (Core.LanguageResult.failure .word (.word fellThrough)))) = _
  rw [accepted]
  rfl

example (flag withElse : Bool) : Core.HasType [] (code flag withElse)
    (Core.LanguageResult.resultType .word) :=
  Core.LocalControl.finish_hasType .word
    (Core.LocalLoop.toControl_hasType escaped .word
      ((tree_of_lowerFlowStatements aligned (unique flag withElse)
        (noFor flag withElse) (accepted flag withElse)).hasType .word))
    (Core.LanguageResult.failure_hasType .word .word)

private def tailSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .word (.literal (.decimal "7")),
    statementNode 0 .word (.expression (exprId 0) false)] }
private theorem tailUnique : NodeOccurrencesUnique tailSource := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private theorem tailNoFor : NoForLoops tailSource := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [tailSource, expressionNode, statementNode] at member
  subst node
  simp

example : Tree compilation tailSource reasonAt escaped [] context false [stmtId 0] .word
    (Core.LocalSequence.discard (Core.LocalLoop.controlType .word)
      (Core.LanguageResult.success (.word (word 7))) (Core.LocalLoop.fallthrough .word)) :=
  tree_of_lowerFlowStatementsWithExpression (fuel := 2) aligned tailUnique tailNoFor (by rfl)

example : Tree compilation tailSource reasonAt escaped [] context true [stmtId 0] .word
    (Core.LocalLoop.returnValue .word (Core.LanguageResult.success (.word (word 7)))) :=
  tree_of_lowerFlowStatementsWithExpression (fuel := 2) aligned tailUnique tailNoFor (by rfl)

example : Tree compilation tailSource reasonAt escaped [] context false [] .word
    (Core.LocalLoop.fallthrough .word) :=
  tree_of_lowerFlowStatements (fuel := 0) aligned tailUnique tailNoFor (by rfl)

/-- Break and continue stop traversal of their tail without claiming a finite
loop execution. An explicit return has the same compiler traversal behavior. -/
private def earlySource (form : StatementForm) : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [statementNode 0 .unit form] }
private theorem earlyUnique (form : StatementForm) : NodeOccurrencesUnique (earlySource form) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, earlySource, statementNode]
private theorem earlyNoFor (form : StatementForm)
    (notFor : ∀ initializer condition post body, form ≠ .forLoop initializer condition post body) :
    NoForLoops (earlySource form) := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [earlySource, statementNode] at member
  subst node
  exact notFor initializer condition post body

example : Tree compilation (earlySource .breakStmt) reasonAt escaped [] context false
    [stmtId 0, stmtId 99] .word (Core.LocalLoop.breaking .word) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)
example : Tree compilation (earlySource .continueStmt) reasonAt escaped [] context false
    [stmtId 0, stmtId 99] .word (Core.LocalLoop.continuing .word) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)
example : Tree compilation (earlySource (.returnStmt none)) reasonAt escaped [] context true
    [stmtId 0, stmtId 99] .unit (Core.LocalLoop.returned .unit) :=
  tree_of_lowerFlowStatements (fuel := 1) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp)) (by rfl)

example : ∃ compiledFlow,
    Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit (Core.LocalLoop.returned .unit) escaped)
        (Core.LanguageResult.success .unit) =
      Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit compiledFlow escaped)
        (Core.LanguageResult.success .unit) ∧
    Tree compilation (earlySource (.returnStmt none)) reasonAt escaped [] context true [stmtId 0] .unit compiledFlow := by
  apply tree_of_lowerStatements (fuel := 1) (fellThroughReason := fellThrough) aligned (earlyUnique _)
    (earlyNoFor _ (by intros; simp))
  rfl

private def primitiveSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .bool (.reference "flag" (.builtinBoolean true)),
    expressionNode 1 .bool (.unary .logicalNot (exprId 0)),
    statementNode 0 .unit (.whileLoop (exprId 1) [stmtId 1]),
    statementNode 1 .unit .breakStmt] }
private theorem primitiveNoFor : NoForLoops primitiveSource := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [primitiveSource, expressionNode, statementNode] at member
  rcases member with rfl | rfl <;> simp

/-- Expression certificates come from the primitive policy, including unary
conditions; they are not assumed from a separate basic-expression tree. -/
example : Tree compilation primitiveSource reasonAt escaped [] context true [stmtId 0] .unit
    (Core.LocalLoop.sequence .unit
      (Core.LocalLoop.whileLoop .unit
        (Core.LocalPrimitiveResults.unary .boolNot (Core.LanguageResult.success (.bool true)))
        (Core.LocalLoop.breaking .unit) escaped)
      (Core.LocalLoop.fallthrough .unit)) := by
  apply tree_of_lowerFlowStatements (fuel := 5) aligned
    (show NodeOccurrencesUnique primitiveSource from by unfold NodeOccurrencesUnique nodeOccurrenceIds; decide)
    primitiveNoFor
  rfl

private def forSource : TypedSource := {
  owner, inputs := [], roots := [.statement (stmtId 0)]
  nodes := [expressionNode 0 .bool (.reference "false" (.builtinBoolean false)),
    statementNode 0 .unit (.forLoop [] (exprId 0) [] [])] }

/-- For is supported by production lowering; this extraction excludes it by
an explicit static premise rather than a hidden assumed child certificate. -/
example : ¬NoForLoops forSource := by
  intro noFor
  exact noFor (id := stmtId 0) (node := {
    id := stmtId 0, span, type := .unit, form := .forLoop [] (exprId 0) [] [] })
    (by rfl) [] (exprId 0) [] [] rfl

example : SourceCoreLoops.lowerFlowStatementsWithPolicy (defaultPolicy compilation) 4 forSource []
    [stmtId 0] .unit reasonAt true escaped = .ok
      (Core.LocalLoop.sequence .unit
        (Core.LocalLoop.iterate .unit (Core.LanguageResult.success (.bool false))
          (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) escaped)
        (Core.LocalLoop.fallthrough .unit)) := by rfl

end Tests.SourceCoreLoopStatementCertificates
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoopStatementMeaning
/-! Actual compiler acceptance plus independent nested-loop source traces.
The initial store already contains a closure. Source location zero maps to
Core location one; both generated self cells remain administrative. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementMeaning

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_meaning.solc" }, startByte := 0, endByte := 1 }
private def reason : Core.Word := Core.Word.ofNatModulo 43
private def escaped : Core.Word := Core.Word.ofNatModulo 44
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context :=
  (Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .bool)]
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def guardNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "flag" (.local binder.id) }
private def falseNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def outerNode : StatementNode := { id := stmtId 0, span, type := .unit, form := .whileLoop (exprId 0) [stmtId 1, stmtId 2, stmtId 3] }
private def innerNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .whileLoop (exprId 1) [] }
private def assignNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .assignValue assignment .equal (exprId 1) }
private def continueNode : StatementNode := { id := stmtId 3, span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner, inputs := [binder], roots := [.statement (stmtId 0)]
  nodes := [.expression guardNode, .expression falseNode, .statement outerNode,
    .statement innerNode, .statement assignNode, .statement continueNode] }
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def sourceHeap (value : Option Bool) : Dynamic.Heap := ⟨[{ type := .bool, value := value.map Dynamic.Value.bool }]⟩
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .bool) 1]
private def adminType : Core.Ty := .sum .unit (.function .unit .unit)
private def admin : Core.Value := .inRight .unit (.closure .unit .unit .unit [])
private def corePayload : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def initialStore (value : Option Bool) : Core.Store := [admin, corePayload value]
private def world : Core.StoreTyping := [adminType, Core.OptionalCell.cellType .bool]
private def conditionCode : Core.Expr := Core.OptionalCell.read .bool (.var 0) reason
private def innerCode : Core.Expr := Core.LocalLoop.whileLoop .unit (Core.LanguageResult.success (.bool false))
  (Core.LocalLoop.fallthrough .unit) escaped
private def bodyCode : Core.Expr := Core.LocalLoop.sequence .unit innerCode
  (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0)
    (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit))
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.whileLoop .unit conditionCode bodyCode escaped) (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit flow escaped)
  (Core.LanguageResult.success .unit)
private def outerClosure : Core.Value := Core.LocalLoop.installedClosure .unit conditionCode bodyCode
  (Core.LocalLoop.fallthrough .unit) escaped 2 coreEnvironment
private def innerClosure : Core.Value := Core.LocalLoop.installedClosure .unit
  (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) escaped 3
  [.bool true, .unit, .cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 2,
    .cellRef (Core.OptionalCell.cellType .bool) 1]

private theorem aligned : BasicStatements.ScopeContextAligned scope context :=
  (BasicStatements.ScopeContextAligned.empty signatures).bind binder .bool
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private theorem noFor : NoForLoops source := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [outerNode, innerNode, assignNode, continueNode]
private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 10 compilation source scope [stmtId 0]
    .unit (fun _ => reason) reason escaped = .ok code := by rfl
private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.withLocal, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.withLocal, Context.ofSignatures] at impossible
private theorem covers : Dynamic.EvidenceEnvironment.Covers context [] := by
  constructor
  · intro goal evidence found; cases found
  · intro predicate member
    simp [context, Context.withLocal, Context.ofSignatures] at member
private theorem heaps (value : Option Bool) : GeneralHeap.HeapRepresents [1] world (sourceHeap value) (initialStore value) := by
  have adminTyped : Core.RuntimeValueHasType [] admin adminType := .inRight (.closure .nil .unit)
  have base := GeneralHeap.HeapRepresents.empty.allocate_administrative adminTyped
  cases value with
  | none =>
    exact (base.allocate (LocalCell.CellRepresents.uninitialized LocalCell.TypeRepresents.bool) Dynamic.Heap.Allocates.append).1
  | some value =>
    exact (base.allocate (LocalCell.CellRepresents.initialized (.bool value)) Dynamic.Heap.Allocates.append).1
private theorem environments : GeneralHeap.EnvRepresents [1] world [] scope sourceEnvironment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil .nil)

private theorem guard_contains : ContainsExpression source (exprId 0) guardNode := ⟨by simp [source], rfl⟩
private theorem false_contains : ContainsExpression source (exprId 1) falseNode := ⟨by simp [source], rfl⟩
private theorem outer_contains : ContainsStatement source (stmtId 0) outerNode := ⟨by simp [source], rfl⟩
private theorem inner_contains : ContainsStatement source (stmtId 1) innerNode := ⟨by simp [source], rfl⟩
private theorem assign_contains : ContainsStatement source (stmtId 2) assignNode := ⟨by simp [source], rfl⟩
private theorem continue_contains : ContainsStatement source (stmtId 3) continueNode := ⟨by simp [source], rfl⟩
private theorem source_guard (program : Program) (value : Bool) :
    Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (sourceHeap (some value))
      (exprId 0) (.bool value) (sourceHeap (some value)) :=
  .intro guard_contains (.local rfl .head (.intro .head) rfl rfl) .nil
private theorem source_false (program : Program) :
    Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (sourceHeap (some true))
      (exprId 1) (.bool false) (sourceHeap (some true)) :=
  .intro false_contains (.builtinBoolean rfl) .nil
private theorem source_assignment (program : Program) :
    Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment (sourceHeap (some true)) assignment.target (exprId 1) (.bool false) (sourceHeap (some false)) :=
  .intro (.intro .head (.intro .head) .nil (.intro .head) .initialized .nil)
    (source_false program)
    (.intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head))
private theorem source_body (program : Program) :
    Dynamic.StatementsExecute program context [] source sourceEnvironment (sourceHeap (some true)) [stmtId 1, stmtId 2, stmtId 3]
      context (.continuing sourceEnvironment) (sourceHeap (some false)) :=
  .cons (.whileLoop inner_contains rfl (.done (source_false program)))
    (.cons (.assignValue assign_contains rfl (source_assignment program))
      (.terminal (.continueStmt continue_contains rfl) (.continuing _)))
private theorem source_success (program : Program) :
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (sourceHeap (some true)) [stmtId 0]
      context (.fallthrough sourceEnvironment) (sourceHeap (some false)) :=
  .control (.singleton outer_contains (by intro expression; simp [outerNode])
    (.whileLoop outer_contains rfl
      (.nextContinue (source_guard program true) (source_body program) (.done (source_guard program false)))))
private theorem source_fault (program : Program) :
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (sourceHeap none) [stmtId 0]
      context (.fault (.uninitializedLocation ⟨0⟩)) (sourceHeap none) :=
  .fault (.singleton (.whileIteration outer_contains rfl (.condition
    (.form guard_contains (.localUninitialized (owned := []) rfl .head (.intro .head) rfl rfl LocalCell.TypeRepresents.bool.not_mapping)))))

/-- The actual accepted compiler and independently constructed finite nested
source trace imply completion; no child Core execution is provided. -/
example (program : Program) :
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program [] source (fun _ => reason) .unit reason escaped (.fallthrough sourceEnvironment) result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld (sourceHeap (some false)) finalStore ∧
      GeneralHeap.LocationMap.Extends [1] finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved [1] (initialStore (some true)) finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (lowerStatements_source_run_preserves aligned unique noFor accepted .unit valid covers
    environments (heaps (some true)) (source_success program)).2

example (program : Program) :
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program [] source (fun _ => reason) .unit reason escaped (.fault (.uninitializedLocation ⟨0⟩)) result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld (sourceHeap none) finalStore ∧
      GeneralHeap.LocationMap.Extends [1] finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved [1] (initialStore none) finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (initialStore none)) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (initialStore none)) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (lowerStatements_source_run_preserves aligned unique noFor accepted .unit valid covers
    environments (heaps none) (source_fault program)).2

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore (some true))) ==
    .done (.inRight .word .unit) [admin, .inRight .unit (.bool false), .inRight .unit outerClosure, .inRight .unit innerClosure])
    "nested loops lost the mutable input or their actual lexical captures"
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore none)) ==
    .done (.inLeft .unit (.word reason)) [admin, .inLeft .bool .unit, .inRight .unit outerClosure])
    "uninitialized guard failed to retain the installed self cell or report its occurrence token"
  match Core.runStateful 0 (.initial code coreEnvironment (initialStore (some true))) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel became a terminal loop result")

end Tests.SourceCoreLoopStatementMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreLoopStatementReflection
/-! Core-only completion witnesses reconstruct independent nested-loop source traces.
The initial store already contains a closure. Source location zero maps to
Core location one; both generated self cells remain administrative. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_reflection.solc" }, startByte := 0, endByte := 1 }
private def reason : Core.Word := Core.Word.ofNatModulo 43
private def escaped : Core.Word := Core.Word.ofNatModulo 44
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context :=
  (Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .bool)]
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def guardNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "flag" (.local binder.id) }
private def falseNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def outerNode : StatementNode := { id := stmtId 0, span, type := .unit, form := .whileLoop (exprId 0) [stmtId 1, stmtId 2, stmtId 3] }
private def innerNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .whileLoop (exprId 1) [] }
private def assignNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .assignValue assignment .equal (exprId 1) }
private def continueNode : StatementNode := { id := stmtId 3, span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner, inputs := [binder], roots := [.statement (stmtId 0)]
  nodes := [.expression guardNode, .expression falseNode, .statement outerNode,
    .statement innerNode, .statement assignNode, .statement continueNode] }
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def sourceHeap (value : Option Bool) : Dynamic.Heap := ⟨[{ type := .bool, value := value.map Dynamic.Value.bool }]⟩
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .bool) 1]
private def adminType : Core.Ty := .sum .unit (.function .unit .unit)
private def admin : Core.Value := .inRight .unit (.closure .unit .unit .unit [])
private def corePayload : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def initialStore (value : Option Bool) : Core.Store := [admin, corePayload value]
private def world : Core.StoreTyping := [adminType, Core.OptionalCell.cellType .bool]
private def conditionCode : Core.Expr := Core.OptionalCell.read .bool (.var 0) reason
private def innerCode : Core.Expr := Core.LocalLoop.whileLoop .unit (Core.LanguageResult.success (.bool false))
  (Core.LocalLoop.fallthrough .unit) escaped
private def bodyCode : Core.Expr := Core.LocalLoop.sequence .unit innerCode
  (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0)
    (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit))
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.whileLoop .unit conditionCode bodyCode escaped) (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit flow escaped)
  (Core.LanguageResult.success .unit)
private def outerClosure : Core.Value := Core.LocalLoop.installedClosure .unit conditionCode bodyCode
  (Core.LocalLoop.fallthrough .unit) escaped 2 coreEnvironment
private def innerClosure : Core.Value := Core.LocalLoop.installedClosure .unit
  (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) escaped 3
  [.bool true, .unit, .cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 2,
    .cellRef (Core.OptionalCell.cellType .bool) 1]

private theorem aligned : BasicStatements.ScopeContextAligned scope context :=
  (BasicStatements.ScopeContextAligned.empty signatures).bind binder .bool
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private theorem noFor : NoForLoops source := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [outerNode, innerNode, assignNode, continueNode]
private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 10 compilation source scope [stmtId 0]
    .unit (fun _ => reason) reason escaped = .ok code := by rfl
private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.withLocal, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.withLocal, Context.ofSignatures] at impossible
private theorem covers : Dynamic.EvidenceEnvironment.Covers context [] := by
  constructor
  · intro goal evidence found; cases found
  · intro predicate member
    simp [context, Context.withLocal, Context.ofSignatures] at member
private theorem heaps (value : Option Bool) : GeneralHeap.HeapRepresents [1] world (sourceHeap value) (initialStore value) := by
  have adminTyped : Core.RuntimeValueHasType [] admin adminType := .inRight (.closure .nil .unit)
  have base := GeneralHeap.HeapRepresents.empty.allocate_administrative adminTyped
  cases value with
  | none =>
    exact (base.allocate (LocalCell.CellRepresents.uninitialized LocalCell.TypeRepresents.bool) Dynamic.Heap.Allocates.append).1
  | some value =>
    exact (base.allocate (LocalCell.CellRepresents.initialized (.bool value)) Dynamic.Heap.Allocates.append).1
private theorem environments : GeneralHeap.EnvRepresents [1] world [] scope sourceEnvironment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil .nil)


private def successStore : Core.Store :=
  [admin, .inRight .unit (.bool false), .inRight .unit outerClosure, .inRight .unit innerClosure]
private def failureStore : Core.Store := [admin, .inLeft .bool .unit, .inRight .unit outerClosure]


private def installedStore (value : Option Bool) : Core.Store :=
  [admin, corePayload value, .inRight .unit outerClosure]
private def bodyEnvironment : Core.Environment :=
  [.bool true, .unit, .cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 2,
    .cellRef (Core.OptionalCell.cellType .bool) 1]

private theorem core_inner : Core.Evaluates bodyEnvironment (installedStore (some true)) innerCode
    (Core.LocalLoop.fallthroughValue .unit)
    (installedStore (some true) ++ [.inRight .unit innerClosure]) := by
  apply Core.LoopExecution.WhileTrace.whileLoop_evaluates
  apply Core.LoopExecution.WhileTrace.done
  simp only [Core.LoopExecution.conditionCode, Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight .bool

private theorem core_body : Core.Evaluates bodyEnvironment (installedStore (some true))
    (Core.LoopExecution.bodyCode bodyCode) (Core.LocalLoop.continuingValue .unit) successStore := by
  have shifted : Core.LoopExecution.bodyCode bodyCode = Core.LocalLoop.sequence .unit innerCode
      (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 3)
        (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit)) := by
    simp [Core.LoopExecution.bodyCode, bodyCode, innerCode, ← Core.Expr.rename_insertion,
      Core.LoopRenaming.sequence, Core.LoopRenaming.assign, Core.LoopRenaming.whileLoop,
      Core.LocalLoop.fallthrough, Core.LocalLoop.continuing, Core.LanguageResult.success,
      Core.Expr.rename, Core.Renaming.insertion]
  rw [shifted]
  apply Core.LocalLoop.sequence_fallthrough _ core_inner
  simp [Core.LocalSequence.assign, Core.LanguageResult.bind, Core.Expr.weakenAt,
    Core.LocalLoop.continuing, Core.LanguageResult.success]
  apply Core.Evaluates.letE (boundValue := .cellRef (Core.OptionalCell.cellType .bool) 1) (.var rfl)
  apply Core.Evaluates.caseRight (payload := .bool false) (.inRight .bool)
  apply Core.Evaluates.letE (boundValue := .unit)
  · exact .storeCell (.var rfl) rfl (.inRight (.var rfl)) rfl
  · exact .inRight (.inRight (.inRight .unit))

private theorem core_success : Core.Evaluates coreEnvironment (initialStore (some true)) code
    (.inRight .word .unit) successStore := by
  have trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode escaped 2 coreEnvironment
      (installedStore (some true)) (Core.LocalLoop.fallthroughValue .unit) successStore := by
    apply Core.LoopExecution.WhileTrace.nextContinue (middle := installedStore (some true))
      (nextStore := successStore) (bodyEvaluation := core_body) (installed := rfl)
    · simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
        Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
        (Core.OptionalCell.read_success (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
          (reference := .var 2) (referenceStore := installedStore (some true)) reason (.var rfl) rfl)
    · apply Core.LoopExecution.WhileTrace.done
      simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
        Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
        (Core.OptionalCell.read_success (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
          (reference := .var 2) (referenceStore := successStore) reason (.var rfl) rfl)
  have flowEval : Core.Evaluates coreEnvironment (initialStore (some true)) flow
      (Core.LocalLoop.fallthroughValue .unit) successStore := by
    apply Core.LocalLoop.sequence_fallthrough .unit trace.whileLoop_evaluates
    simp only [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight (.inLeft (.inLeft .unit))
  apply Core.LocalControl.finish_fallthrough .unit (Core.LocalLoop.toControl_normal .unit escaped flowEval)
  simp only [Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight .unit

private theorem core_failure : Core.Evaluates coreEnvironment (initialStore none) code
    (.inLeft .unit (.word reason)) failureStore := by
  have trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode escaped 2 coreEnvironment
      failureStore (.inLeft (Core.LocalLoop.controlType .unit) (.word reason)) failureStore := by
    apply Core.LoopExecution.WhileTrace.conditionFault
    simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
      Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
      (Core.OptionalCell.read_failure (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
        (reference := .var 2) (referenceStore := failureStore) reason (.var rfl) rfl)
  exact Core.LocalControl.finish_failure .unit
    (Core.LocalLoop.toControl_failure .unit escaped
      (Core.LocalLoop.sequence_failure .unit trace.whileLoop_evaluates))

/-- Finite Core derivations alone construct the independent source traces.
The expected Core stores retain both exact nested-loop lexical captures. -/
example (program : Program) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason escaped
      sourceEnvironment (sourceHeap (some true)) [stmtId 0] .unit [1] world (initialStore (some true))
      (.inRight .word .unit) successStore := by
  obtain ⟨fuel, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel core_success
  exact lowerStatements_run_reflects aligned unique noFor accepted .unit valid environments (heaps (some true))
    (completes fuel (Nat.le_refl _))

example (program : Program) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason escaped
      sourceEnvironment (sourceHeap none) [stmtId 0] .unit [1] world (initialStore none)
      (.inLeft .unit (.word reason)) failureStore := by
  obtain ⟨fuel, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel core_failure
  exact lowerStatements_run_reflects aligned unique noFor accepted .unit valid environments (heaps none)
    (completes fuel (Nat.le_refl _))

example (program : Program) :
    (∃ fuel value after, Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done value after) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment
      (sourceHeap (some true)) [stmtId 0] finalContext outcome after) :=
  lowerStatements_finite_iff aligned unique noFor accepted .unit valid covers environments (heaps (some true))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore (some true))) ==
    .done (.inRight .word .unit) successStore) "reflected nested loop completion changed"
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore none)) ==
    .done (.inLeft .unit (.word reason)) failureStore) "reflected loop fault completion changed"
  match Core.runStateful 0 (.initial code coreEnvironment (initialStore (some true))) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "reflection treated fuel exhaustion as completion")

end Tests.SourceCoreLoopStatementReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreNativeEntry
/-! The shared native runner checks every input payload and retains typing
across suspension. Its definitions need not come from the strict catalog. -/
set_option autoImplicit false
namespace Tests.SourceCoreNativeEntry
open Solcore Solcore.Core Solcore.Frontend SourceCoreGeneralEntry

private def definitions : DataEnvironment := [⟨[.product .integer .bool]⟩]
private def body : Expr := Core.LanguageResult.bind (.namedData ⟨0⟩)
  (Core.OptionalCell.read (.namedData ⟨0⟩) (.var 0) Word.zero)
  (Core.LanguageResult.success (.var 0))
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content := "function empty() returns () {}"}]
}

example {definitions : DataEnvironment} (entry : NativeEntry definitions) (arguments : List Core.Value)
    (checkpoint : Checkpoint definitions entry.resultType) (_accepted : entry.start arguments = .ok checkpoint) :
    Core.StateHasType checkpoint.state (Core.LanguageResult.resultType entry.resultType) definitions :=
  checkpoint.typed

def run : IO Unit := do
  let entry ← match NativeEntry.compile definitions [.namedData ⟨0⟩] (.namedData ⟨0⟩) body with
    | .ok entry => pure entry
    | .error error => throw (IO.userError s!"native entry rejected: {reprStr error}")
  let value : Core.Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.integer (-900)) (.bool true))
  let checkpoint ← match entry.start [value] with
    | .ok checkpoint => pure checkpoint
    | .error error => throw (IO.userError s!"native input rejected: {reprStr error}")
  let suspended := checkpoint.resume 0
  let next ← match suspended.checkpoint? with
    | some next => pure next
    | none => throw (IO.userError "native zero fuel did not suspend")
  match (next.resume 100).observation with
    | .succeeded actual [.inRight .unit stored] =>
        unless actual == value && stored == value do throw (IO.userError "native input/result changed")
    | result => throw (IO.userError s!"native resume failed: {reprStr result}")
  for malformed in [Core.Value.constructed ⟨⟨0⟩, 0⟩ (.pair (.bool false) (.bool true)),
      .constructed ⟨⟨0⟩, 1⟩ .unit,
      .constructed ⟨⟨0⟩, 0⟩ (.pair (.integer 0) (.cellRef .bool 0))] do
    match entry.start [malformed] with
      | .error (.input 0 _) => pure ()
      | _ => throw (IO.userError "native boundary accepted malformed nested payload")
  match entry.start [value] [.unit] with
    | .error (.initialStoreUnsupported 1) => pure ()
    | _ => throw (IO.userError "native Core initial-store behavior changed")
  match NativeEntry.compile definitions [.namedData ⟨0⟩] .bool body with
    | .error (.coreCheckFailed _ _) => pure ()
    | _ => throw (IO.userError "native body accepted the wrong result projection")
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"native diagnostic fixture rejected: {reprStr error}")
  let table ← match SourceCoreStageCodebook.prepareWithProjection
      program ⟨[], [], [], []⟩ (fun _ => pure .unit) with
    | .ok table => pure table
    | .error error => throw (IO.userError s!"empty native descriptor inventory failed: {reprStr error}")
  let owner ← match program.signatures.functions.head? with
    | some signature => pure signature.id
    | none => throw (IO.userError "native diagnostic root missing")
  let base : SourceCoreFaultSites.Table := {
    owner, resultType := .unit, reads := [], escapedReason := Word.zero, additional := []}
  let diagnostics ← match SourceCoreCallableFaultSites.prepare ⟨[], [], [], []⟩ table base 70000 with
    | .ok diagnostics => pure diagnostics
    | .error error => throw (IO.userError s!"native diagnostic reservation failed: {reprStr error}")
  unless diagnostics.unknown.val == 70000 do throw (IO.userError "callable tokens overlapped reserved dynamic ranges")
  IO.println "shared native input checking, typed resume and diagnostic reservation GREEN"

end Tests.SourceCoreNativeEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreNumericLiteralEvidenceReceipts
/-! Actual validator receipts close numeric leaves in a complete runtime ledger.
An unrelated uncovered assumption is retained. The executable audits below use
actual checked numeric nodes and explicitly marked mutations of their ledgers;
mutated ledgers are not claimed to come from a well-formed checked program. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNumericLiteralEvidenceReceipts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreElaboration NumericLiteralEvidenceReceipts

section Accepted
variable {solved : List SolvedRequirement} {node : ExpressionNode}
  {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
  {context : SourceSemantics.Context}
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)
  (form : node.form = .integerLiteral literal resolution)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (environment : Dynamic.Environment) (heap : Dynamic.Heap)

include sameLedger runtime form

/-- Concrete primitive source and native semantics use no ordinary ledger or
covering-dictionary callback. Arbitrary native environments and stores persist. -/
theorem word_leaf {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (actual : Core.Environment) (store : Core.Store) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap ∧
    Evaluates actual store (.inRight .word (.word validated.value))
      (.inRight .word (.word validated.value)) store :=
  ⟨word_raw accepted form sameLedger runtime program evidence source environment heap, .inRight .word⟩

/-- Reflection inverts the completed native leaf and constructs the independent
source result. It does not consume preservation or prior source execution. -/
theorem word_reflects {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    {actual : Core.Environment} {store after : Core.Store} {result : Core.Value}
    (completed : Evaluates actual store (.inRight .word (.word validated.value)) result after) :
    result = .inRight .word (.word validated.value) ∧ after = store ∧
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap := by
  cases completed with
  | inRight evaluated =>
    cases evaluated
    exact ⟨rfl, rfl, word_raw accepted form sameLedger runtime program evidence source environment heap⟩

theorem integer_leaf {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    (actual : Core.Environment) (store : Core.Store) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.integer validated.value) heap ∧
    Evaluates actual store (.inRight .word (.integer validated.value))
      (.inRight .word (.integer validated.value)) store :=
  ⟨integer_raw accepted form sameLedger runtime program evidence source environment heap, .inRight .integer⟩

theorem integer_reflects {validated : NativeIntegerLiteral}
    (accepted : validateNativeIntegerLiteral solved node literal resolution = .ok validated)
    {actual : Core.Environment} {store after : Core.Store} {result : Core.Value}
    (completed : Evaluates actual store (.inRight .word (.integer validated.value)) result after) :
    result = .inRight .word (.integer validated.value) ∧ after = store ∧
    Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions (.integer validated.value) heap := by
  cases completed with
  | inRight evaluated =>
    cases evaluated
    exact ⟨rfl, rfl, integer_raw accepted form sameLedger runtime program evidence source environment heap⟩

omit form in
/-- Empty-premise evidence does not inspect the ambient dictionary, even when
it contains no entry for another assumption in the complete ledger. -/
theorem arbitrary_dictionary {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated) :
    Dynamic.RequirementProducesEvidence context evidence resolution.requirement resolution.predicate
      (.implementation resolution.predicate (.builtin .intWord) []) ∧
    ¬ Dynamic.RequirementUnavailable context evidence resolution.requirement :=
  ⟨(word accepted).produces sameLedger runtime evidence, (word accepted).safe sameLedger runtime evidence⟩
end Accepted

/-- The complete runtime ledger is computed from the actual initial source
frame, even when local template IDs are nonempty. The validator chooses the
one primitive implementation row; no prior Header.valid is supplied. -/
theorem frame_word_leaf {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved)
    {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : WordIntegerLiteral}
    (accepted : validateWordIntegerLiteral solved node literal resolution = .ok validated)
    (form : node.form = .integerLiteral literal resolution)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionFormEvaluates program context function.evidence function.source environment heap
      node.form node.requirements node.coercions (.word validated.value) heap :=
  word_raw accepted form ((RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger)
    (RecursiveNamedInitialContextValidity.runtime frame extended programTyped)
    program function.evidence function.source environment heap

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def selected : SolvedRequirement := ⟨⟨0⟩, goal, .implementation (.byImpl goal (.builtin .intWord) [])⟩
private def assumed : SolvedRequirement := ⟨⟨1⟩, goal, .assumption goal⟩
private def rows : List SolvedRequirement := [assumed, selected]
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements rows
private def resolution : IntegerLiteralResolution := ⟨37, .word, ⟨0⟩⟩
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"numeric_receipts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def node : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "numeric_receipts.solc"⟩, 0, 2⟩,
  type := .word, form := .integerLiteral (.decimal "37") resolution, requirements := [⟨0⟩] }

private theorem runtime : RuntimeRequirementLedgerValid context := by
  refine ⟨?_, ?_⟩
  · change ([⟨1⟩, ⟨0⟩] : List RequirementId).Nodup
    decide
  all_goals skip
  intro row evidence member isImpl
  simp only [context, Context.withSolvedRequirements, rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · cases isImpl
  · refine .intro (.intro (.implementation (.byImpl .nil)) ?_)
    apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
    · simp [context, Context.withSolvedRequirements, Context.ofSignatures, signatures,
        ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]
    · rfl
    · exact .intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl
    · exact .nil

/-- A concrete successful validator leaf coexists with an uncovered assumption
row. The complete ledger is runtime-valid but is not ordinary-valid. -/
theorem uncovered_unused_row :
    validateWordIntegerLiteral rows node (.decimal "37") resolution = .ok ⟨Word.ofNatModulo 37, [⟨0⟩]⟩ ∧
    RuntimeRequirementLedgerValid context ∧ ¬ RequirementLedgerWellFormed context ∧
    Dynamic.RequirementProducesEvidence context [] resolution.requirement resolution.predicate
      (.implementation resolution.predicate (.builtin .intWord) []) := by
  have accepted : validateWordIntegerLiteral rows node (.decimal "37") resolution = .ok ⟨Word.ofNatModulo 37, [⟨0⟩]⟩ := by rfl
  refine ⟨accepted, runtime, ?_, (word accepted).produces rfl runtime []⟩
  intro ordinary
  have valid := ordinary.entriesValid assumed (by simp [context, Context.withSolvedRequirements, rows])
  cases valid with
  | intro retained =>
    cases retained with
    | intro represents valid =>
      cases represents
      cases valid with
      | assumption member => cases member

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def huge : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639937
private def content : String := String.intercalate "\n" [
  "function wordRoot() returns (Word) { let first = 0x25; return first; }",
  s!"function wrapRoot() returns (Word) \{ return {huge}; }",
  s!"function integerRoot() returns (integer) \{ let full = {huge}; return full; }",
  "function faultRoot() returns (Word) { let prior = 41; let missing: Word; return missing + 43; }"
]

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut wordCount := 0
  let mut integerCount := 0
  for named in compiled.indexed.base.functions do
    let actual ← get "numeric actual specialization"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (actual == named.specialized) "numeric full selected record changed"
    let source := actual.function.typedBody
    let ledger := actual.function.solvedRequirements
    for retained in source.nodes do
      match retained with
      | .expression node => match node.form with
        | .integerLiteral literal resolution =>
          let selected ← match ledger.filter (·.id == resolution.requirement) with
            | [selected] => pure selected
            | _ => throw (IO.userError "numeric real row is not singleton")
          let implementation : ProgramImplId := if resolution.targetType == .integer then .builtin .intInteger else .builtin .intWord
          let raw : TypedTraitResolution.Evidence := .byImpl resolution.predicate implementation []
          require (selected.predicate == resolution.predicate && selected.evidence == .implementation raw)
            "numeric selected full evidence changed"
          let validate (rows : List SolvedRequirement) : Except SourceCoreElaboration.Error (Core.Value × List RequirementId) :=
            if node.type == .integer then
              (validateNativeIntegerLiteral rows node literal resolution).map fun value => (.integer value.value, value.consumedRequirements)
            else
              (validateWordIntegerLiteral rows node literal resolution).map fun value => (.word value.value, value.consumedRequirements)
          let checked ← get "numeric actual validator" (validate ledger)
          let expected := if node.type == .integer then Core.Value.integer (Int.ofNat resolution.rawValue)
            else .word (Word.ofNatModulo resolution.rawValue)
          require (checked.1 == expected && checked.2 == [resolution.requirement]) "numeric value/consumed order changed"
          let fresh : RequirementId := ⟨(ledger.map (·.id.index)).foldl max 0 + 1⟩
          let assumption : SolvedRequirement := ⟨fresh, resolution.predicate, .assumption resolution.predicate⟩
          -- These are explicit ledger mutations, not checker-produced ledgers.
          let variants := [ledger, assumption :: ledger, ledger ++ [assumption],
            (ledger.filter (·.id != resolution.requirement)) ++ [selected, assumption]]
          for rows in variants do
            let observed ← get "numeric unrelated assumption" (validate rows)
            require (observed == checked) "unrelated retained row changed selected numeric result"
            let context : SourceCoreFunctions.Context := {
              plan := compiled.indexed.base.plan, owner := named.signature.key,
              globals := compiled.indexed.base.globals, administrativePrefix := 1,
              solvedRequirements := rows, internalReason := Word.zero }
            let lowered ← get "numeric actual primitive compiler"
              (SourceCoreFunctions.lowerExpressionWithReasons
                (fun _ _ _ _ _ _ _ _ _ => .error (.unsupportedExpression node.id node.form))
                20 context source [] node.id (fun _ => Word.zero))
            let expectedCode : Expr := match checked.1 with
              | .word value => .inRight .word (.word value)
              | .integer value => .inRight .word (.integer value)
              | _ => .unit
            require (lowered.expression == expectedCode) "actual numeric emission differs from validator payload"
            let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
              .letE (.newCell (.function .unit .unit) (.lambda .unit .unit .unit)) (lowered.expression.weakenAt 0),
              compiled.compatible.checked.catalog.definitions⟩
            require native.check "numeric emitted code failed Core typing"
            for fuel in [0, 1, 5, 1000] do
              let completed := match native.runStateful fuel with
                | .outOfFuel checkpoint => Core.runStateful 1000 checkpoint
                | other => other
              match completed with
              | .done value store =>
                require (value == .inRight .word checked.1 && store == [.closure .unit .unit .unit []])
                  "numeric primitive changed result/administrative store on resume"
              | other => throw (IO.userError s!"numeric primitive did not finish: {reprStr other}")
          let wrongImpl : ProgramImplId := if implementation == .builtin .intWord then .builtin .intInteger else .builtin .intWord
          let malformed := [
            ledger.filter (·.id != resolution.requirement), ledger ++ [selected],
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .assumption row.predicate} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl resolution.predicate wrongImpl [])} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl resolution.predicate implementation [raw])} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with predicate := ProgramSignatures.builtinIntPredicate .bool} else row,
            ledger.map fun row => if row.id == resolution.requirement then {row with evidence := .implementation (.byImpl (ProgramSignatures.builtinIntPredicate .bool) implementation [])} else row]
          for rows in malformed do
            require (validate rows |>.toOption.isNone) "numeric malformed selected receipt was accepted"
          if node.type == .integer then integerCount := integerCount + 1 else wordCount := wordCount + 1
        | _ => pure ()
      | _ => pure ()
  require (wordCount ≥ 4 && integerCount ≥ 1) "numeric audit missed Word/Integer or fault suffix literal"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"numeric full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "numeric evidence receipts" content
    ["wordRoot", "wrapRoot", "integerRoot", "faultRoot"]
  inspect compiled
  let missing ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "numeric missing binder identity lost")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordRoot", .word (Word.ofNatModulo 37), [(.word, some (.word (Word.ofNatModulo 37)))]),
    ("wrapRoot", .word (Word.ofNatModulo 1), []),
    ("integerRoot", .integer (Int.ofNat huge), [(.integer, some (.integer (Int.ofNat huge)))])]
  for fuel in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let finished ← get "numeric public resume" (started.resume 300000)
      match finished.observation with
      | .done value state =>
        require (reprStr value == reprStr expected) "numeric public completed value changed"
        cells state heap
      | other => throw (IO.userError s!"numeric public success expected: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] fuel
    let finished ← get "numeric public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == missing) "numeric first fault identity changed"
      cells state [(.word, some (.word (Word.ofNatModulo 41))), (.word, none)]
    | other => throw (IO.userError s!"numeric first fault expected: {reprStr other}")
  IO.println "numeric selected implementation / retained unrelated rows / exact emission / full heaps / resume GREEN"

end Tests.SourceCoreNumericLiteralEvidenceReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCorePrimitiveExpressions
/-! Kernel-checked regression examples use actual accepted compiler output.
The retained integer evidence is validated independently, and short-circuit
fault reasons are attached to the executed local read occurrence. -/

set_option autoImplicit false

namespace Tests.SourceCorePrimitiveExpressions

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"primitive_expressions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "primitive_expressions.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder 0, .bool), (binder 1, .word), (binder 2, .bool)]
private def node (index : Nat) (type : TypeSystem.Ty) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type, form }
private def literalRequirement : SolvedRequirement := {
  id := ⟨0⟩, predicate := ProgramSignatures.builtinIntPredicate .word
  evidence := .implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])
}
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [literalRequirement] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements [literalRequirement]
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.withSolvedRequirements]
  · intro requirement member
    have same : requirement = literalRequirement := by simpa [context, Context.withSolvedRequirements] using member
    subst requirement
    apply SolvedRequirementValid.intro
    apply RetainedEvidenceValid.intro
    · exact .implementation (.byImpl .nil)
    · apply EvidenceValid.implementation (rule := ProgramSignatures.builtinIntWordRule)
      · simp [context, Context.withSolvedRequirements, Context.ofSignatures,
          ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]
      · rfl
      · refine .intro { parameters := [], variables := [] } ?_ rfl rfl
        exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩
      · exact .nil
private def source : TypedSource := {
  owner
  inputs := [{ id := binder 0, name := "flag", scheme := .mono .bool },
    { id := binder 1, name := "number", scheme := .mono .word },
    { id := binder 2, name := "right", scheme := .mono .bool }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.product .word .bool) (.group (id 1)),
    node 1 (.product .word .bool) (.tuple [id 2, id 8]),
    node 2 .word (.conditional (id 3) (id 4) (id 7)),
    node 3 .bool (.reference "flag" (.local (binder 0))),
    node 4 .word (.binary (id 5) .add (id 6)),
    .expression {
      id := id 5, span, type := .word
      form := .integerLiteral (.decimal "17") { rawValue := 17, targetType := .word, requirement := ⟨0⟩ }
      requirements := [⟨0⟩] },
    node 6 .word (.reference "number" (.local (binder 1))),
    node 7 .word (.unary .bitNot (id 6)),
    node 8 .bool (.binary (id 9) .logicalAnd (id 10)),
    node 9 .bool (.unary .logicalNot (id 3)),
    node 10 .bool (.reference "right" (.local (binder 2)))]
}
private def code : Core.Expr :=
  Core.LocalSequence.pair .word .bool
    (Core.LocalControl.choose .word
      (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3)))
      (SourceCorePrimitive.binary .add
        (Core.LanguageResult.success (.word (word 17)))
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6))))
      (Core.LocalPrimitiveResults.unary .wordNot
        (Core.OptionalCell.read .word (.var 1) (reasonAt (id 6)))))
    (Core.LocalPrimitiveResults.logicalAnd
      (Core.LocalPrimitiveResults.unary .boolNot
        (Core.OptionalCell.read .bool (.var 0) (reasonAt (id 3))))
      (Core.OptionalCell.read .bool (.var 2) (reasonAt (id 10))))
private theorem accepted : SourceCorePrimitive.lowerExpressionWithReasons 5 compilation source scope (id 0) reasonAt =
    .ok ⟨.product .word .bool, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide

example : Core.HasType (SourceCoreLocalCell.coreContext scope) code
    (Core.LanguageResult.resultType (.product .word .bool)) :=
  PrimitiveExpressions.lowerExpression_hasType unique accepted

/-- Integer metadata retains its one requirement; it is not coerced to the
empty-requirement metadata used by ordinary primitive nodes. -/
example : ∃ literalNode, source.lookupExpression? (id 5) = some literalNode ∧
    PrimitiveExpressions.RootMetadata source (id 5) literalNode .word :=
  PrimitiveExpressions.lowerExpression_metadata unique (show
    SourceCorePrimitive.lowerExpressionWithReasons 1 compilation source scope (id 5) reasonAt =
      .ok ⟨.word, Core.LanguageResult.success (.word (word 17))⟩ from rfl)

private def boolCell (value : Option Bool) : Dynamic.Cell := { type := .bool, value := value.map .bool }
private def wordCell (value : Option Nat) : Dynamic.Cell := { type := .word, value := value.map fun n => .word (word n) }
private def boolStored : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def wordStored : Option Nat → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word (word value))
private def heap (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Dynamic.Heap :=
  ⟨[boolCell flag, wordCell number, boolCell right]⟩
private def store (flag : Option Bool) (number : Option Nat) (right : Option Bool) : Core.Store :=
  [boolStored flag, wordStored number, boolStored right]
private def world : Core.StoreTyping :=
  [Core.OptionalCell.cellType .bool, Core.OptionalCell.cellType .word, Core.OptionalCell.cellType .bool]
private def environment : Dynamic.Environment := [(binder 0, ⟨0⟩), (binder 1, ⟨1⟩), (binder 2, ⟨2⟩)]
private def coreEnvironment : Core.Environment :=
  [.cellRef (Core.OptionalCell.cellType .bool) 0,
    .cellRef (Core.OptionalCell.cellType .word) 1, .cellRef (Core.OptionalCell.cellType .bool) 2]
private theorem environments : LocalCell.EnvRepresents world scope environment coreEnvironment :=
  .cons rfl (.cons rfl (.cons rfl .nil))
private theorem boolRelated (value : Option Bool) : LocalCell.CellRepresents (boolCell value) (boolStored value) .bool := by
  cases value with
  | none => exact .uninitialized .bool
  | some value => exact .initialized (.bool value)
private theorem wordRelated (value : Option Nat) : LocalCell.CellRepresents (wordCell value) (wordStored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word (word value))
private theorem heaps (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    LocalCell.HeapRepresents (heap flag number right).cells (store flag number right) world :=
  .cons (boolRelated flag) (.cons (wordRelated number) (.cons (boolRelated right) .nil))

/-- Accepted lowering, ordinary input representation, and the independently
proved ledger validity suffice. No source or Core child execution is assumed. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (flag : Option Bool) (number : Option Nat) (right : Option Bool) :
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap flag number right) (id 0) sourceOutcome (heap flag number right) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap flag number right) reasonAt (id 0) (.product .word .bool) sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done coreValue (store flag number right)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store flag number right)) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store flag number right) :=
  (PrimitiveExpressions.lowerExpression_run_preserves unique accepted program context evidence contextValid
    environments (heaps flag number right)).2

private theorem run_shortCircuit : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) (some 3) none)) =
    .done (.inRight .word (.pair (.word (word 20)) (.bool false))) (store (some true) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_rightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some false) (some 3) none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 10)))) (store (some false) (some 3) none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl
private theorem run_arithmeticRightFault : Core.runStateful 300
    (.initial code coreEnvironment (store (some true) none none)) =
    .done (.inLeft (.product .word .bool) (.word (reasonAt (id 6)))) (store (some true) none none) := by
  simp [code, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LocalPrimitiveResults.logicalAnd, Core.LocalPrimitiveResults.unary,
    Core.LocalControl.choose, Core.LocalSequence.pair, Core.OptionalCell.read,
    Core.LanguageResult.bind, Core.LanguageResult.success, Core.LanguageResult.failure, Core.Expr.weakenAt]
  rfl

/-- The concrete short-circuit machine observation also reflects to a related
independent source outcome, using the accepted compiler preservation theorem. -/
example (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
        (heap (some true) (some 3) none) (id 0) sourceOutcome (heap (some true) (some 3) none) ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment
        (heap (some true) (some 3) none) reasonAt (id 0) (.product .word .bool) sourceOutcome
        (.inRight .word (.pair (.word (word 20)) (.bool false))) := by
  obtain ⟨sourceOutcome, coreValue, evaluation, related, coreEvaluation⟩ :=
    PrimitiveExpressions.lowerExpression_preserves unique accepted program context evidence contextValid
      environments (heaps (some true) (some 3) none)
  have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run_shortCircuit) coreEvaluation
  exact ⟨sourceOutcome, evaluation, same.1 ▸ related⟩

/-- Missing literal evidence and insufficient traversal fuel cannot yield a
certificate. The rejected branch is exercised by the actual compiler. -/
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 5 { solvedRequirements := [] } source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 4 compilation source scope (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

private def sourceResultType : Syntax.BinaryOp → TypeSystem.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .shiftLeft | .shiftRight
  | .bitAnd | .bitXor | .bitOr | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply => .word
  | _ => .bool
private def operatorSource (operator : Syntax.BinaryOp) : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)]
  nodes := [node 0 (sourceResultType operator) (.binary (id 1) operator (id 2)),
    node 1 .word (.literal (.decimal "7")), node 2 .word (.literal (.decimal "0"))]
}
private def operatorCode (operator : Syntax.BinaryOp) : Core.Expr :=
  SourceCorePrimitive.binary operator (Core.LanguageResult.success (.word (word 7)))
    (Core.LanguageResult.success (.word (word 0)))
private theorem operatorAccepted (operator : Syntax.BinaryOp) (strict : Dynamic.StrictBinaryOperator operator) :
    SourceCorePrimitive.lowerExpressionWithReasons 2 compilation (operatorSource operator) [] (id 0) reasonAt =
      .ok ⟨SourceCorePrimitive.binaryResultType operator, operatorCode operator⟩ := by
  cases strict <;> rfl
private theorem operatorUnique (operator : Syntax.BinaryOp) : NodeOccurrencesUnique (operatorSource operator) := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  cases operator <;> decide

/-- All nineteen strict Word operators pass through the real compiler and the
same independently proved semantic bridge, including swapped comparisons. -/
example (operator : Syntax.BinaryOp) (strict : Dynamic.StrictBinaryOperator operator)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence (operatorSource operator) [] ⟨[]⟩
        (id 0) sourceOutcome ⟨[]⟩ ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence (operatorSource operator) [] ⟨[]⟩ reasonAt
        (id 0) (SourceCorePrimitive.binaryResultType operator) sourceOutcome coreValue ∧
      Core.Evaluates [] [] (operatorCode operator) coreValue [] :=
  PrimitiveExpressions.lowerExpression_preserves (operatorUnique operator) (operatorAccepted operator strict)
    program context evidence contextValid LocalCell.EnvRepresents.nil LocalCell.HeapRepresents.nil

/-- Word division and remainder by zero have defined Word results in both
semantics; these are successful language results, not missing-carrier faults. -/
example : Core.runStateful 80 (.initial (operatorCode .divide) [] []) =
    .done (.inRight .word (.word (word 0))) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .modulo) [] []) =
    .done (.inRight .word (.word (word 0))) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .lessEqual) [] []) =
    .done (.inRight .word (.bool false)) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl
example : Core.runStateful 80 (.initial (operatorCode .notEqual) [] []) =
    .done (.inRight .word (.bool true)) [] := by
  simp [operatorCode, SourceCorePrimitive.binary, SourceCorePrimitive.strictBinaryBody,
    Core.LocalPrimitiveResults.binaryWith, Core.LanguageResult.bind, Core.LanguageResult.success, Core.Expr.weakenAt]
  rfl

private def wrongOperands : TypedSource := {
  owner, inputs := [], roots := [.expression (id 0)]
  nodes := [node 0 .word (.binary (id 1) .add (id 2)),
    node 1 .bool (.reference "true" (.builtinBoolean true)), node 2 .word (.literal (.decimal "0"))]
}
example (output : SourceCoreBasic.LoweredExpr) :
    SourceCorePrimitive.lowerExpressionWithReasons 2 compilation wrongOperands [] (id 0) reasonAt ≠ .ok output := by
  intro impossible
  cases impossible

end Tests.SourceCorePrimitiveExpressions
end

section
-- leanmerge: from Solcore.Test.SourceCoreProjectedAssignmentHeader
/-! Actual assignment Heads supply all three header callbacks for bare and
projected targets, retaining the reached success or fault state. -/
set_option autoImplicit false
namespace Tests.SourceCoreProjectedAssignmentHeader
open Solcore
open SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {context : SourceSemantics.Context} {administrative : Core.Context}
  {faults : FunctionCalls.FaultRep} {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  (budget : Nat)
  (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
    ProtectedStateTransition.PreservesAt protocol (payloadModel values.checked registry functions)
      program context evidence source certificate faults size))

include extension transport faithful observations meaning in
theorem full_successful_head_discharges_header :
    ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial updated after size trace bounded
  exact ProtectedAssignmentHeads.Stateful.Head.preserves_prefix_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget meaning trace bounded

include extension transport faithful observations meaning in
theorem full_fault_head_discharges_header :
    ProtectedForHeader.Stateful.AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial errors reason after size trace bounded next output
  exact ProtectedAssignmentHeads.Stateful.Head.preserves_fault_reachable_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget meaning errors trace bounded next output

include extension transport faithful observations in
theorem full_reflected_head_discharges_header
    (functionTypes : FunctionRuntimeViews functions)
    (reflection : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.ReflectsAt protocol (payloadModel values.checked registry functions)
        program context evidence source certificate faults size)) :
    ProtectedForHeader.Stateful.AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees actualTyped initial errors next output value finalStore size completed bounded
  exact ProtectedAssignmentHeads.Stateful.Head.reflects_reachable_bounded functions extension program evidence
    protocol transport faithful observations head environments heaps locals agrees actualTyped initial
    budget reflection functionTypes errors completed bounded


end Tests.SourceCoreProjectedAssignmentHeader
end

section
-- leanmerge: from Solcore.Test.SourceCoreRuntimeKeyGuards
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRuntimeKeyGuards
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping

/-- The independent normalizer matches the historical pure runtime type view
on every type, including nested nominal arguments, proxies and function types. -/
theorem normalization (type : TypeSystem.Ty) : Dynamic.runtimeType type = SourceTypedRuntime.runtimeType type := by
  induction type <;> simp_all [Dynamic.runtimeType, SourceTypedRuntime.runtimeType]

theorem staged_boolean (value : Bool) : Dynamic.ValueRuntimeTypeMatches (.bool value) (.comptime .bool) :=
  .intro (.bool value) rfl

theorem staged_product (value : Bool) (inner : TypeSystem.Ty) :
    Dynamic.ValueRuntimeTypeMatches (.product (.bool value) (.proxy (.comptime inner)))
      (.product (.comptime .bool) (.proxy inner)) :=
  .intro (.product (.bool value) (.proxy _)) rfl

theorem staged_nominal (metadata : DataConstructorInstantiation) (arguments : List Dynamic.Value) :
    Dynamic.ValueRuntimeTypeMatches (.constructed metadata arguments) (.comptime metadata.resultType) :=
  .intro (.constructed metadata arguments) rfl

private def keyType : TypeSystem.Ty := .comptime .bool
private def valueType : TypeSystem.Ty := .comptime (.function .bool .bool)
private def mapType : TypeSystem.Ty := .mapping keyType valueType
private def sourceRoot : Dynamic.Value := .mapping keyType valueType []
private def carrier : SourceCoreDataValues.Value := .mapping keyType valueType []
private theorem unavailable : ¬ Dynamic.Defaultable valueType := by
  intro impossible; cases impossible with | comptime inner => cases inner

/-- Former counterexample: normalization accepts the Bool key, while the
missing default and fault retain the raw staged function type. -/
theorem source_missing : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault valueType) :=
  .indexDefaultUnavailable (staged_boolean true) .nil unavailable

/-- A raw type difference caused only by staging cannot trigger the
independent expression key-type mismatch rule. -/
theorem no_false_key_mismatch : ¬ (Dynamic.runtimeType .bool ≠ Dynamic.runtimeType keyType) := by simp [keyType]

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem observations (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionObservations catalog (noFunctions catalog) (fun _ _ => False) := fun impossible => False.elim impossible
private theorem functionViews (catalog : SourceCoreCompatibleCatalog.Catalog) :
    FunctionRuntimeViews (noFunctions catalog) := fun impossible => False.elim impossible

/-- Actual encoder and comparator receipts give finite completion and
reflection with the corrected independent key guard. No helper run is assumed. -/
theorem actual_missing {context : SourceCoreCompatibleValues.Context} {layout : OrderedMapping.Layout}
    (comparison : SourceCoreCompatibleDataEquality.Prepared context.checked)
    (registered : layout.Registered context.checked.catalog.definitions) (sameKey : layout.keyType = comparison.type)
    (mappingProjection : context.checked.catalog.project mapType = .ok (SourceCoreMappingWithDefault.type layout))
    (keyProjection : context.checked.catalog.project keyType = .ok layout.keyType)
    {encodedMapping : SourceCoreCompatibleValues.Encoded 100 context mapType carrier}
    {encodedKey : SourceCoreCompatibleValues.Encoded 100 encodedMapping.context keyType (.bool true)}
    (mappingAccepted : SourceCoreCompatibleValues.encode 100 context mapType carrier = .ok encodedMapping)
    (keyAccepted : SourceCoreCompatibleValues.encode 100 encodedMapping.context keyType (.bool true) = .ok encodedKey)
    (missing : Word) :
    ∃ header finalStore,
      MetadataRep encodedKey.context.registry (.mapping keyType valueType) header ∧
      Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault valueType) ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1))
          [encodedMapping.value, encodedKey.value] [.integer (-9)]) =
          .done (.inLeft layout.valueType (.word (missing.add header))) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missing comparison.expression (.var 0) (.var 1))
          [encodedMapping.value, encodedKey.value] [.integer (-9)]) = .done actual actualStore →
          actual = .inLeft layout.valueType (.word (missing.add header)) ∧ actualStore = finalStore) := by
  obtain ⟨header, result, finalStore, metadata, meaning, completes, reflects, _⟩ :=
    encoded_lookup_run comparison layout registered sameKey mappingProjection keyProjection mappingAccepted keyAccepted
      (show CompatibleEncoding.Means carrier sourceRoot from .mapping .empty) (.bool true)
      faithful (observations context.checked.catalog) [] [.integer] [encodedMapping.value, encodedKey.value] [.integer (-9)] missing
      (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases meaning with
  | found located => cases located
  | default _ defaulted => exact (unavailable defaulted.defaultable).elim
  | missing absent _ =>
    have keyRep := CompatibleEncoding.encode_represents_at (context := encodedMapping.context) (functions := noFunctions context.checked.catalog) keyAccepted
      (show CompatibleEncoding.Means (.bool true) (.bool true) from .bool true) [] [.integer]
    have typed := keyRep.source_runtimeView (functionViews context.checked.catalog)
    exact ⟨header, finalStore, metadata, .indexDefaultUnavailable typed absent unavailable, completes, reflects⟩

private def exercise (context : SourceCoreCompatibleValues.Context) : IO Unit := do
  match layoutAccepted : context.checked.catalog.mappingLayout keyType valueType with
  | .error error => throw (IO.userError s!"key guard layout rejected {reprStr error}")
  | .ok layout =>
    have facts := CompatibleEncoding.mappingLayout_facts (checked := context.checked) layoutAccepted
    have projection := CompatibleEncoding.mapping_project facts.1 facts.2.1 facts.2.2.1
    match comparisonAccepted : SourceCoreCompatibleDataEquality.prepare 100 context.checked keyType with
    | .error error => throw (IO.userError s!"key guard comparison rejected {reprStr error}")
    | .ok comparison =>
      have comparisonProjection : context.checked.catalog.project keyType = .ok comparison.type := by
        simpa only [comparison_sourceType comparisonAccepted] using comparison.projection
      have keySame := Except.ok.inj (facts.2.1.symm.trans comparisonProjection)
      match mappingAccepted : SourceCoreCompatibleValues.encode 100 context mapType carrier with
      | .error error => throw (IO.userError s!"key guard mapping rejected {reprStr error}")
      | .ok encodedMapping =>
        match keyAccepted : SourceCoreCompatibleValues.encode 100 encodedMapping.context keyType (.bool true) with
        | .error error => throw (IO.userError s!"key guard key rejected {reprStr error}")
        | .ok encodedKey =>
          have _receipt := actual_missing comparison facts.2.2.2 keySame projection facts.2.1 mappingAccepted keyAccepted (Word.ofNatModulo 100)
          let code := SourceCoreMappingWithDefault.lookup layout (Word.ofNatModulo 100) comparison.expression (.var 0) (.var 1)
          unless infer? [SourceCoreMappingWithDefault.type layout, layout.keyType] code context.checked.catalog.definitions ==
              some (LanguageResult.resultType layout.valueType) do
            throw (IO.userError "key guard actual helper checker rejected")
          let header ← match encodedMapping.value with
            | .pair (.word header) _ => pure header
            | _ => throw (IO.userError "key guard header missing")
          unless encodedKey.context.registry.lookup header == some (.mapping keyType valueType) do
            throw (IO.userError "key guard raw expected metadata erased")
          let initial := Core.State.initial code [encodedMapping.value, encodedKey.value] [.integer (-9)]
          match runStateful 200000 initial with
          | .done (.inLeft _ (.word token)) after =>
            unless token == (Word.ofNatModulo 100).add header && after[0]? == some (.integer (-9)) &&
                after.length == context.checked.catalog.entries.length + 2 do
              throw (IO.userError "key guard missing-default or helper effects changed")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft layout.valueType (.word token)) after do
                throw (IO.userError "key guard checkpoint changed result")
            | _ => throw (IO.userError "key guard expected checkpoint")
          | result => throw (IO.userError s!"key guard helper unexpected {reprStr result}")

def run : IO Unit := do
  match SourceCoreCompatibleCatalog.prepare ⟨[], [], [], [], [], []⟩ 100 [mapType] with
  | .error error => throw (IO.userError s!"key guard catalog rejected {reprStr error}")
  | .ok checked => exercise (SourceCoreCompatibleValues.Context.initial checked)
  IO.println "independent normalized key guards, raw defaults and actual native reflection GREEN"

end Tests.SourceCoreRuntimeKeyGuards
end

section
-- leanmerge: from Solcore.Test.SourceCoreScalarExpressionReflection
/-! The supplied source execution, including a propagated read fault, is
reflected through actual primitive lowering in a store containing a cyclic
administrative closure. Source location zero is Core location one. -/

set_option autoImplicit false

namespace Tests.SourceCoreScalarExpressionReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"scalar_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "scalar_reflection.solc" }
  startByte := 0, endByte := 1
}
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def reasonAt (site : ExpressionId) : Core.Word := word (100 + site.occurrence.index)
private def scope : SourceCoreBasic.Scope := [(binder, .word)]
private def node (index : Nat) (form : ExpressionForm) : Node :=
  .expression { id := id index, span, type := .word, form }
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def context : SourceSemantics.Context := Context.ofSignatures {
  functions := [], implRules := [], traits := [], implementations := []
}
private theorem contextValid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.ofSignatures] at impossible
private theorem covers : Dynamic.EvidenceEnvironment.Covers context [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    simp [context, Context.ofSignatures] at member
private def source : TypedSource := {
  owner, inputs := [{ id := binder, name := "number", scheme := .mono .word }]
  roots := [.expression (id 0)]
  nodes := [node 0 (.group (id 1)), node 1 (.binary (id 2) .add (id 3)),
    node 2 (.reference "number" (.local binder)), node 3 (.literal (.decimal "1"))]
}
private def code : Core.Expr := SourceCorePrimitive.binary .add
  (Core.OptionalCell.read .word (.var 0) (reasonAt (id 2)))
  (Core.LanguageResult.success (.word (word 1)))
private theorem accepted : SourceCorePrimitive.lowerExpressionWithReasons 4 compilation source scope (id 0) reasonAt =
    .ok ⟨.word, code⟩ := by rfl
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private def cell (value : Option Core.Word) : Dynamic.Cell := { type := .word, value := value.map .word }
private def stored : Option Core.Word → Core.Value
  | none => .inLeft .word .unit
  | some value => .inRight .unit (.word value)
private def heap (value : Option Core.Word) : Dynamic.Heap := ⟨[cell value]⟩
private def functionType : Core.Ty := .function .unit .unit
private def optionalFunction : Core.Ty := Core.OptionalCell.cellType functionType
private def recursiveFunction : Core.Value := .closure .unit .unit
  (.caseE (.loadCell (.var 1)) .unit (.apply (.var 0) (.var 1)))
  [.cellRef optionalFunction 0]
private def world : Core.StoreTyping := [optionalFunction, Core.OptionalCell.cellType .word]
private def mapping : GeneralHeap.LocationMap := [1]
private def store (value : Option Core.Word) : Core.Store := [.inRight .unit recursiveFunction, stored value]
private def environment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def administrativeContext : Core.Context := [.cell optionalFunction]
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .word) 1, .cellRef optionalFunction 0]
private theorem environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) .nil))
private theorem cellRelated (value : Option Core.Word) : LocalCell.CellRepresents (cell value) (stored value) .word := by
  cases value with
  | none => exact .uninitialized .word
  | some value => exact .initialized (.word value)
private theorem recursiveTyped : Core.RuntimeValueHasType world recursiveFunction functionType := by
  exact .closure (.cons (.cellRef rfl) .nil)
    (.caseE (.loadCell (.var rfl)) .unit (.apply (.var rfl) (.var rfl)))
private theorem heaps (value : Option Core.Word) : GeneralHeap.HeapRepresents mapping world (heap value) (store value) := by
  have admin : GeneralHeap.HeapRepresents [] [optionalFunction] ⟨[]⟩ [.inLeft functionType .unit] :=
    GeneralHeap.HeapRepresents.empty.allocate_administrative (.inLeft .unit)
  have allocated := (admin.allocate (cellRelated value) .append).1
  apply allocated.write_administrative (location := 0) (type := optionalFunction)
  · intro index found
    have member := List.mem_of_getElem? found
    simp at member
  · rfl
  · exact .inRight recursiveTyped
  · rfl

/-- A caller supplies its actual source trace; no child evaluation or desired
Tree is assumed by the compile-to-run theorem. -/
example (program : Program) (value : Option Core.Word) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (execution : Dynamic.ExpressionEvaluatesOutcome program context [] source environment (heap value) (id 0) outcome after) :
    after = heap value ∧ ∃ result required,
      PrimitiveExpressions.OutcomeRepresents program context [] source environment (heap value) reasonAt (id 0) .word outcome result ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (store value)) = .done result (store value)) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (store value)) = .done actual actualStore →
        actual = result ∧ actualStore = store value) :=
  ScalarExpressionReflection.Primitive.lowerExpression_source_run_preserves unique accepted contextValid covers environments (heaps value) execution

/-- Reflection rules out two successful source values as well as success and
fault overlap, even with administrative recursive cells. -/
example (program : Program) (input : Option Core.Word) (left right : Dynamic.Value) (leftHeap rightHeap : Dynamic.Heap)
    (leftEvaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) left leftHeap)
    (rightEvaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) right rightHeap) :
    left = right ∧ leftHeap = heap input ∧ rightHeap = heap input := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact ScalarExpressionReflection.Primitive.source_success_functional tree unique environments (heaps input) leftEvaluation rightEvaluation

example (program : Program) (input : Option Core.Word) (value : Dynamic.Value) (reason : Dynamic.SemanticFault)
    (valueHeap faultHeap : Dynamic.Heap)
    (evaluation : Dynamic.ExpressionEvaluates program context [] source environment (heap input) (id 0) value valueHeap)
    (fault : Dynamic.ExpressionFaults program context [] source environment (heap input) (id 0) reason faultHeap) : False := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact ScalarExpressionReflection.Primitive.source_success_excludes_fault tree unique contextValid covers environments (heaps input) evaluation fault

private theorem readOnly : Core.ReadOnly.Expression code := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  exact GeneralExpressions.Primitive.readOnly tree

private theorem core_failed : Core.Evaluates coreEnvironment (store none) code
    (.inLeft .word (.word (reasonAt (id 2)))) (store none) :=
  Core.LocalPrimitiveResults.binaryWith_left_failure
    (Core.OptionalCell.read_failure _ (.var rfl) rfl)

/-- The reason is the leaf read occurrence, not the enclosing group/binary. -/
example (program : Program) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (execution : Dynamic.ExpressionEvaluatesOutcome program context [] source environment (heap none) (id 0) outcome after) :
    after = heap none ∧ ∃ site location,
      outcome = .fault (.uninitializedLocation location) ∧
      reasonAt site = reasonAt (id 2) ∧
      PrimitiveExpressions.UninitializedAt program context [] source environment (heap none) (id 0) site location := by
  obtain ⟨_, _, tree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique accepted
  obtain ⟨same, result, related, core⟩ := ScalarExpressionReflection.Primitive.source_outcome
    tree unique contextValid covers environments (heaps none) execution
  have resultSame := (Core.evaluation_deterministic core core_failed).1
  cases related with
  | value staged typed => cases resultSame
  | uninitialized site location origin =>
      exact ⟨same, site, location, rfl, Core.Value.word.inj (Core.Value.inLeft.inj resultSame).2, origin⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 100 (.initial code coreEnvironment (store (some (word 6)))) ==
    .done (.inRight .word (.word (word 7))) (store (some (word 6))))
    "reflected arithmetic changed the result or administrative closure"
  assertTrue (Core.runStateful 100 (.initial code coreEnvironment (store none)) ==
    .done (.inLeft .word (.word (reasonAt (id 2)))) (store none))
    "reflected read fault changed its leaf reason or administrative closure"

end Tests.SourceCoreScalarExpressionReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreScalarNativeTyping
/-! External consumers derive complete native annotations from the production
contextual traversal. The negative fixture distinguishes visible cell types
from runtime typing; shadowed and administrative annotations are unconstrained.
The existing conditional and compatible-read IO suites exercise this same code. -/
set_option autoImplicit false
namespace Tests.SourceCoreScalarNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionScalarNativeTyping

/-- No static lowering tree or per-child native typing premise is supplied by
the consumer. Root and specialized parent callbacks use the same entry point. -/
theorem actual_contextual_native
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (ordinary : CompatibleExpressionConditionals.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    lowered.type.WellFormed definitions ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions :=
  contextual_native visibleTypes administrative ordinary unique declarations syntaxTree found typed
    readPolicy lowerPolicy leafPolicy accepted extension

/-- The same induction closes all scalar children inside another static
consumer, under arbitrary hidden slots and an ambient data extension. -/
theorem all_children_native
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} {definitions : DataEnvironment}
    (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context)
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  conditionals_native_at visibleTypes administrative extension tree

private def missing : Ty := .namedData ⟨0⟩

/-- Runtime typing of an inhabited sum leaves its unused annotation unchecked.
It cannot supply the visible annotation needed by a lazy default/read. -/
theorem runtime_typing_does_not_authenticate_scope (binder : Resolved.LocalId) :
    RuntimeValueHasType [] (.inLeft missing .unit) (.sum .unit missing) [] ∧
      ¬ ScopeWellFormed [] [(binder, .sum .unit missing)] := by
  refine ⟨.inLeft .unit, ?_⟩
  intro typed
  have found : SourceCoreLocalCell.lookup? [(binder, .sum .unit missing)] binder =
      some (0, .sum .unit missing) := by simp [SourceCoreLocalCell.lookup?]
  have wellFormed := typed binder 0 (.sum .unit missing) found
  cases wellFormed with
  | sum _ invalid => cases invalid with | namedData found => cases found

/-- An invalid annotation hidden by the actual first-match scope lookup is
irrelevant. No requirement is imposed on the complete native context. -/
theorem shadowed_annotation_allowed (binder : Resolved.LocalId) :
    ScopeWellFormed [] [(binder, .bool), (binder, missing)] := by
  intro selected index type found
  by_cases same : binder = selected
  · simp [SourceCoreLocalCell.lookup?, same] at found
    obtain ⟨rfl, rfl⟩ := found
    constructor
  · simp [SourceCoreLocalCell.lookup?, same] at found

end Tests.SourceCoreScalarNativeTyping
end
