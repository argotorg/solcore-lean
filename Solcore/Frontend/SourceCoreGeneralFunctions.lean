import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Frontend.SourceCoreGeneralTypes
import Solcore.Frontend.SourceCoreEvidence
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreDataFaultSites
import Solcore.Frontend.SourceCoreDataMatches
import Solcore.Frontend.SourceCoreDataPlaceFaultSites

/-! Closed function instances and catalog data share ordinary Core execution.
Preparation authenticates the plan, compiles reachable closures once, and checks
each assembled entry against the actual recursive data definitions. This slice
supports finite contextual local-lambda bundles and structural place assignments. -/

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
  | localInstances (error : SourceCoreLocalPolymorphism.Error)
  | invalidFunctionType (key : Key)
  | resultMetadataMismatch (key : Key)
  | assumptionsUnsupported (key : Key)
  | stagedResultUnsupported (key : Key)
  | missingGlobal (key : Key)
  | missingDiagnostics (key : Key)
  | expectedStatementRoot (id : ExpressionId)
  deriving Repr

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

private def prepareFunction (program : CheckedProgram) (checked : Checked) (specialized : SourceSpecialization.SpecializedFunction) :
    Except Error Function := do
  let function := specialized.function
  discard <| (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program specialized.key specialized.assumptions)
    |>.mapError Error.plan
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
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key)
    (lowerBinder : TypedSource → SourceCoreBasic.Scope → TypedBinder → Except SourceCoreBasic.Error Core.Ty :=
      SourceCoreGeneralTypes.lowerBinder checked) : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreGeneralTypes.readStatement checked
      lowerBinder := lowerBinder
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

private def localError (id : ExpressionId) (node : ExpressionNode)
    (error : SourceCoreLocalPolymorphism.Error) : SourceCoreBasic.Error :=
  match error with
  | .metadata error => error
  | _ => .unsupportedExpression id node.form

private def contextualBinder (checked : Checked) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : Key) (active : TypeSystem.Substitution) (source : TypedSource)
    (scope : SourceCoreBasic.Scope) (binder : TypedBinder) : Except SourceCoreBasic.Error Core.Ty :=
  if binder.scheme.quantified.isEmpty then SourceCoreGeneralTypes.lowerBinder checked source scope binder
  else (SourceCoreLocalPolymorphism.lowerBinder locals owner active source scope binder).mapError fun
    | .metadata error => error
    | _ => .polymorphicBinding binder.id

/-- Contextual local instances re-enter the shared expression traversal with
concrete metadata. Every closure captures the same lexical references; the
bundle is constructed before the generalized binding's cell is allocated. -/
private def lowerContextualExpression (program : CheckedProgram) (checked : Checked)
    (signatures : ProgramSignatures) (locals : SourceCoreLocalPolymorphism.Catalog)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (context : SourceCoreFunctions.Context)
    (active : TypeSystem.Substitution) (skipInitializer : Option ExpressionId) :
    SourceCoreFunctions.ExpressionLowerer
  | 0, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id, reasonAt => do
      let bind := contextualBinder checked locals context.owner active
      let lowerBody := bodyLowerer checked signatures context.solvedRequirements assignments diagnostics context.owner bind
      let policy := { SourceCoreGeneralTypes.policy checked signatures with
        lowerBinder := bind
        lowerSpecial? := some fun current child budget source scope id reasonAt => do
          let node ← match source.lookupExpression? id with
            | some node => pure node
            | none => throw (.missingExpression id)
          let initialized := locals.bindings.find? fun binding =>
            decide (binding.caller = current.owner ∧ binding.initializer = id)
          if let some initialized := initialized.filter (fun _ => skipInitializer ≠ some id) then
            let binding ← (locals.binding current.owner initialized.binder.id).mapError (localError id node)
            let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding active fun candidate => do
              let lowered ← (lowerContextualExpression program checked signatures locals assignments diagnostics current
                candidate.origin.substitution (some id) (min budget fuel) candidate.source scope id reasonAt)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              match lowered.expression with
              | .inRight .word closure => pure closure
              | _ => throw (.initializerMetadataMismatch id)).mapError (localError id node)
            return some lowered
          let evidence ← SourceCoreEvidence.lower program checked current child budget source scope id reasonAt
          if let some lowered := evidence then return some lowered
          match node.form with
          | .reference _ (.local binder) =>
              if locals.bindings.any (fun binding => decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
                let lowered ← (SourceCoreLocalPolymorphism.lowerRead locals current.owner active source scope id (reasonAt id))
                  |>.mapError (localError id node)
                return some lowered
              else return none
          | _ => return none }
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt
termination_by fuel => fuel

private def compileClosure (program : CheckedProgram) (checked : Checked) (signatures : ProgramSignatures) (plan : Plan)
    (globals : List Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (fuel : Nat) (function : Function) : Except Error Core.Expr := do
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
    diagnostics function.signature.key (contextualBinder checked locals function.signature.key [])
  let body ← (lowerBody
    (lowerContextualExpression program checked signatures locals own.assignments diagnostics context [] none)
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
  let locals ← (SourceCoreLocalPolymorphism.prepare checked plan).mapError
    (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.localInstances)
  let functions ← (plan.specializations.reverse.mapM (prepareFunction program checked)).mapError
    SourceCoreGeneralEntry.CompileError.lowering
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure { plan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreDataPlaceFaultSites.prepare checked program.signatures plan first).mapError
        (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.diagnostics)
      let closures ← (functions.mapM (compileClosure program checked program.signatures plan globals diagnostics locals fuel)).mapError
        SourceCoreGeneralEntry.CompileError.lowering
      SourceCoreGeneralEntry.prepareValidated plan checked fuel (fun _ request =>
        assemble globals functions closures diagnostics request) true

end Solcore.Frontend.SourceCoreGeneralFunctions
