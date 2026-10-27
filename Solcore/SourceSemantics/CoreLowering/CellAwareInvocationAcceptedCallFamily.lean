import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallExpressions
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedApplication

/-! The size induction across bodies for direct calls. A family of rows is
given by the instantiations it admits (`called`): every catalog header with an
admitted instantiation has the receipts of a named row whose accepted
expressions are extended roots calling only admitted instantiations (`Row`).
One strong induction on the grade gives the accepted-expression meaning of
every family body on the slot-retaining protocol: at a call of a given grade
the direct-call head needs the callee's application below that grade, and the
row lemma gives it from the callee body's expressions below it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

/-- The receipts of one family row, as the public named root takes them, with
the extended closure and call authority of its body and its own registry
scope. -/
structure Row (called : DeclarationInstantiation → Prop)
    (header : Header whole (Program.ofChecked whole.sourceProgram)) where
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code
  record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized
  sameNamed : header.named = named
  sameLayouts : header.layouts = whole.indexed.layouts
  sameGlobals : header.globals = whole.indexed.base.globals.length
  sameBindings : header.bindings = named.inputs
  sameBody : header.body = generation.body
  sameSolved : header.solved = named.specialized.function.solvedRequirements
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics
  assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments
  body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body
  covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True) (rowIndex generation record))
    body.tree
  native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)
  closed : CellAwareInvocationAcceptedCallExpressions.ClosedCalls generation record called
  ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers) generation record
  bodyScope : Staging.Recursive.Scope
  bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function bodyScope

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (support : SelectedCompilationNamedSupport.Support whole)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {called : DeclarationInstantiation → Prop}
  (rows : ∀ header, header ∈ headers → called header.instantiation → Row (headers := headers) called header)

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem row_source {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) {child : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function child) :
    child.source = (rowIndex row.generation row.record).source := by
  show child.source = CallableIndexedNamedGeneration.source row.named
  rw [← row.sameNamed]
  exact ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source

include support in
private theorem row_unique {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) :
    NodeOccurrencesUnique (CallableIndexedNamedGeneration.source row.named) := by
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [← row.sameNamed]
  simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique

include profile receiver support artifact checked wellFormed rows in
/-- Every family body has its accepted-expression meaning on the
slot-retaining protocol at every grade, for every owner key with physical
locations and every registry scope of its function. -/
theorem expressions (size : Nat) :
    ∀ header (member : header ∈ headers) (admitted : called header.instantiation) (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex (rows header member admitted).generation (rows header member admitted).record) stages child faults
        size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member admitted owner keyPhysical child selected
    have applications : ∀ callee, callee ∈ headers → called callee.instantiation →
        CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size ∧
        CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size := by
      intro callee calleeMember calleeAdmitted
      let row := rows callee calleeMember calleeAdmitted
      refine ⟨fun smaller less => ?_, fun smaller less => ?_⟩
      · exact CellAwareInvocationAcceptedNamedApplication.preserves profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed smaller
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
      · exact CellAwareInvocationAcceptedNamedApplication.reflects profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native smaller row.bodySelected
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
    let row := rows header member admitted
    exact CellAwareInvocationAcceptedCallExpressions.expressions row.generation row.record called owner keyPhysical
      stages child faults row.closed size (row_source row selected) completion.result.extension
      (CellAwareInvocationAcceptedNamedInvocation.reads row.generation row.record row.issuer receiver
        (row_unique support row))
      support.registryBodies wellFormed row.ports applications

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's application input holds for every admitted header
at every Source grade. -/
theorem preserves (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.preserves profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed size
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's native application input holds for every admitted
header at every native grade. -/
theorem reflects (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.reflects profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native size row.bodySelected
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
