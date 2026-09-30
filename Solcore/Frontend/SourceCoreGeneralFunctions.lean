import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Frontend.SourceCoreGeneralTypes
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreDataFaultSites
import Solcore.Frontend.SourceCoreDataMatches
import Solcore.Frontend.SourceCoreDataPlaceFaultSites

/-! Monomorphic functions and closed catalog data share ordinary Core execution.
Preparation authenticates the plan, compiles reachable closures once, and checks
each assembled entry against the actual recursive data definitions. This slice
supports monomorphic local bindings and structural place assignments. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreGeneralFunctions

open SourceInference
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Signature := SourceCoreCalls.Signature

inductive Error where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreDataCatalog.Error)
  | lowering (error : SourceCoreBasic.Error)
  | diagnostics (error : SourceCoreDataPlaceFaultSites.Error)
  | invalidFunctionType (key : Key)
  | resultMetadataMismatch (key : Key)
  | assumptionsUnsupported (key : Key)
  | stagedResultUnsupported (key : Key)
  | missingGlobal (key : Key)
  | missingDiagnostics (key : Key)
  | expectedStatementRoot (id : ExpressionId)
  deriving Repr, DecidableEq

structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List (TypedBinder × Core.Ty)
  deriving Repr

private def prepareInputs (checked : Checked) (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List (TypedBinder × Core.Ty))
  | _, [] => pure []
  | scope, binder :: rest => do
      let type ← (SourceCoreGeneralTypes.lowerBinder checked source scope binder).mapError Error.lowering
      let remaining ← prepareInputs checked source ((binder.id, type) :: scope) rest
      pure ((binder, type) :: remaining)

private def prepareFunction (checked : Checked) (specialized : SourceSpecialization.SpecializedFunction) :
    Except Error Function := do
  let function := specialized.function
  unless specialized.assumptions.isEmpty do throw (.assumptionsUnsupported specialized.key)
  if function.returnComptime then throw (.stagedResultUnsupported specialized.key)
  let (parameter, result) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.invalidFunctionType specialized.key)
  if result ≠ function.inferredBodyType then throw (.resultMetadataMismatch specialized.key)
  let site := SourceCoreElaboration.ErrorSite.declaration specialized.key.declaration
  let parameterType ← (SourceCoreGeneralTypes.projectType checked site parameter).mapError Error.lowering
  let resultType ← (SourceCoreGeneralTypes.projectType checked site result).mapError Error.lowering
  let inputs ← prepareInputs checked function.typedBody [] function.typedBody.inputs
  pure { specialized, inputs, signature := { key := specialized.key, parameterType, resultType } }

def bodyLowerer (checked : Checked) (signatures : ProgramSignatures)
    (solvedRequirements : List SolvedRequirement) (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key) :
    SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreGeneralTypes.readStatement checked
      lowerBinder := SourceCoreGeneralTypes.lowerBinder checked
      lowerAssignment := SourceCoreGeneralTypes.lowerAssignment checked
      lowerMatch := some (SourceCoreDataMatches.lowerWithReasons
        { checked, signatures, solvedRequirements })
      assignEqual := some fun expression fuel source scope site assignment rhs output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment .equal
          (some rhs) output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none) Core.Word.zero
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
      assignValue := some fun expression fuel source scope site assignment operator rhs output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment operator
          (some rhs) output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none)
          (assignments.reasonAt site assignment.target.root (.value operator))
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
      assignBitNotWithExpression := some fun expression fuel source scope site assignment output next reasonAt =>
        SourceCoreDataPlaces.lower checked signatures expression fuel source scope site assignment .equal
          none output next reasonAt
          (diagnostics.placeReason owner site assignment.target.root none)
          (assignments.reasonAt site assignment.target.root .bitNot)
          (fun type => diagnostics.placeReason owner site assignment.target.root (some type))
    } fuel source scope statements result reasonAt fellThrough escaped

private def compileClosure (checked : Checked) (signatures : ProgramSignatures) (plan : Plan)
    (globals : List Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (fuel : Nat) (function : Function) : Except Error Core.Expr := do
  let source := function.specialized.function.typedBody
  let own ← match diagnostics.base.find? function.signature.key with
    | some own => pure own
    | none => throw (.missingDiagnostics function.signature.key)
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => throw (.expectedStatementRoot id)
  let context : SourceCoreFunctions.Context := {
    plan, globals, owner := function.signature.key, administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lowerBody := bodyLowerer checked signatures function.specialized.function.solvedRequirements own.assignments
    diagnostics function.signature.key
  let policy := SourceCoreGeneralTypes.policy checked signatures
  let body ← (lowerBody
    (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody budget context source scope id reasonAt)
    fuel source (function.inputs.reverse.map (fun (binder, type) => (binder.id, type))) statements
    function.signature.resultType (diagnostics.reasonAt function.signature.key)
    own.fellThroughReason own.table.escapedReason).mapError Error.lowering
  pure (.lambda function.signature.parameterType (Core.LanguageResult.resultType function.signature.resultType)
    (SourceCoreFunctions.bindParameters function.inputs function.signature.resultType body))

private def assemble (globals : List Signature) (functions : List Function) (closures : List Core.Expr)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) {checked : Checked}
    (request : SourceCoreGeneralEntry.BodyRequest checked) : Except Error SourceCoreGeneralEntry.LoweredBody := do
  let (function, index) ← match functions.zipIdx.find? (fun entry => decide (entry.1.signature.key = request.specialized.key)) with
    | some found => pure found
    | none => throw (.missingGlobal request.specialized.key)
  let arguments := SourceCoreCalls.packArguments (request.inputs.zipIdx.map fun (input, index) =>
    ⟨input.type, Core.OptionalCell.read input.type
      (.var (globals.length + (request.inputs.length - 1 - index))) Core.Word.zero⟩)
  (SourceCoreBasic.ensureType (.declaration function.signature.key.declaration)
    function.signature.parameterType arguments.type).mapError Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  pure {
    expression := SourceCoreRecursiveEntry.allocateGlobals globals.reverse
      (SourceCoreRecursiveEntry.installFunctions closures invoked)
    faultSites := diagnostics.rootTable
  }

/-- A supplied catalog is checked before lowering; the entry checker certifies
the assembled closures, helpers, and seed call under those exact definitions. -/
def prepareWithCatalog (program : CheckedProgram) (plan : Plan) (checked : Checked) (fuel : Nat) :
    Except (SourceCoreGeneralEntry.CompileError Error) (SourceCoreGeneralEntry.PreparedProgram checked) := do
  let plan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError
    (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.plan)
  let functions ← (plan.specializations.reverse.mapM (prepareFunction checked)).mapError
    SourceCoreGeneralEntry.CompileError.lowering
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure { plan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreDataPlaceFaultSites.prepare checked program.signatures plan first).mapError
        (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.diagnostics)
      let closures ← (functions.mapM (compileClosure checked program.signatures plan globals diagnostics fuel)).mapError
        SourceCoreGeneralEntry.CompileError.lowering
      SourceCoreGeneralEntry.prepare program plan checked fuel (fun _ request =>
        assemble globals functions closures diagnostics request)

end Solcore.Frontend.SourceCoreGeneralFunctions
