import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCoreAssignmentFaultSites
import Solcore.Frontend.ProgramChecking

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
    (rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer)
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
