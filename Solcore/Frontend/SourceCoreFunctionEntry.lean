import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreFunctions

/-! Prepared programs whose internal cells and signatures include monomorphic
function values. Global installation, parameter allocation, and entry invocation
reuse the ordinary recursive-entry helpers. The public seed boundary retains
BasicEntry's scalar/product input validation and result projection; function
inputs and outputs are currently rejected there.

Core checking establishes machine type safety for the generated body. A source
heap relation for captured closures and administrative cells remains separate;
this module does not claim complete source semantic preservation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFunctionEntry

open SourceInference

abbrev Key := SourceCoreRecursiveEntry.Key
abbrev Plan := SourceCoreRecursiveEntry.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Input := SourceCoreBasicEntry.Input
abbrev Entry := SourceCoreBasicEntry.Entry
abbrev PreparedProgram := SourceCoreBasicEntry.PreparedProgram
abbrev Error := SourceCoreRecursiveEntry.Error

structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List Input
  sourceResultType : TypeSystem.Ty
  deriving Repr

private def prepareInputs (key : Key) (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List Input)
  | _, [] => pure []
  | scope, binder :: rest => do
      let type ← (SourceCoreFunctionTypes.lowerBinder source scope { binder with comptime := false }).mapError SourceCoreRecursiveEntry.Error.lowering
      let inputs ← prepareInputs key source ((binder.id, type) :: scope) rest
      pure ({ id := binder.id, sourceType := binder.scheme.body, type, comptime := binder.comptime } :: inputs)

private def prepareFunction (specialized : SourceSpecialization.SpecializedFunction) : Except Error Function := do
  let key := specialized.key
  let function := specialized.function
  if function.returnComptime then throw (.entry (.stagedResultUnsupported key))
  unless specialized.assumptions.isEmpty do
    throw (.entry (.assumptionsUnsupported key specialized.assumptions.length))
  let (sourceParameterType, sourceResultType) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.entry (.invalidFunctionType key))
  if sourceResultType ≠ function.inferredBodyType then throw (.entry (.resultMetadataMismatch key))
  let parameterType ← (SourceCoreFunctionTypes.projectType (.declaration key.declaration) sourceParameterType).mapError SourceCoreRecursiveEntry.Error.lowering
  let resultType ← (SourceCoreFunctionTypes.projectType (.declaration key.declaration) sourceResultType).mapError SourceCoreRecursiveEntry.Error.lowering
  let inputs ← prepareInputs key function.typedBody [] function.typedBody.inputs
  pure { specialized, inputs, sourceResultType, signature := { key, parameterType, resultType } }

/-- Lambda bodies and global bodies share the same function-value policy. -/
def bodyLowerer : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } fuel source scope statements result reasonAt fellThrough escaped

/-- Nested lambdas retain their owning function's assignment reason provider. -/
def bodyLowererWithAssignments (assignments : SourceCoreAssignmentFaultSites.Table) :
    SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy (SourceCoreAssignmentPolicy.attach {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } assignments) fuel source scope statements result reasonAt fellThrough escaped

private def compileClosure (plan : Plan) (globals : List Signature)
    (diagnostics : SourceCoreProgramFaultSites.Program) (compilationFuel : Nat)
    (function : Function) : Except Error Core.Expr := do
  let source := function.specialized.function.typedBody
  let ownSites ← match diagnostics.find? function.signature.key with
    | some sites => pure sites
    | none => .error (.missingDiagnostics function.signature.key)
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => .error (.entry (.expectedStatementRoot id))
  let context : SourceCoreFunctions.Context := {
    plan, globals, owner := function.signature.key, administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lowerBody := bodyLowererWithAssignments ownSites.assignments
  let body ← (lowerBody
    (fun fuel source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithReasons lowerBody fuel context source scope id reasonAt)
    compilationFuel source (SourceCoreBasicEntry.inputScope function.inputs) statements
    function.signature.resultType ownSites.table.reasonAt ownSites.fellThroughReason
    ownSites.table.escapedReason).mapError SourceCoreRecursiveEntry.Error.lowering
  pure (.lambda function.signature.parameterType
    (Core.LanguageResult.resultType function.signature.resultType)
    (SourceCoreRecursiveEntry.bindParameters function.inputs function.signature.resultType body))

private def assembleEntry (plan : Plan) (functions : List Function)
    (globals : List Signature) (closures : List Core.Expr) (key : Key) : Except Error Entry := do
  let (function, index) ← match functions.zipIdx.find? (fun item => decide (item.1.signature.key = key)) with
    | some item => pure item
    | none => .error (.missingGlobal key)
  -- Retain the existing public value boundary, even though internal function
  -- parameters and returned closures have broader representations.
  let inputs ← (SourceCoreBasicEntry.prepareInputs function.specialized.function.typedBody).mapError SourceCoreRecursiveEntry.Error.entry
  let projected ← match projection : SourceCoreScalar.lowerType
      (.declaration function.signature.key.declaration) function.sourceResultType with
    | .ok resultType => pure (⟨resultType, projection⟩ : { resultType : Core.Ty //
        SourceCoreScalar.lowerType (.declaration function.signature.key.declaration)
          function.sourceResultType = .ok resultType })
    | .error error => .error (.lowering (.typeProjection error))
  (SourceCoreBasic.ensureType (.declaration key.declaration) projected.val function.signature.resultType).mapError SourceCoreRecursiveEntry.Error.lowering
  let diagnostics ← (SourceCoreProgramFaultSites.prepare plan key).mapError SourceCoreRecursiveEntry.Error.programFaultSites
  let arguments := SourceCoreRecursiveEntry.seedArguments globals inputs
  (SourceCoreBasic.ensureType (.declaration key.declaration) function.signature.parameterType arguments.type).mapError SourceCoreRecursiveEntry.Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  let body := SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures invoked)
  if checked : Core.infer? (SourceCoreBasicEntry.inputContext inputs) body =
      some (Core.LanguageResult.resultType projected.val) then
    pure {
      key := function.signature.key, inputs
      sourceResultType := function.sourceResultType
      resultType := projected.val, resultProjection := projected.property
      faultSites := diagnostics.rootTable
      body, bodyTyped := Core.infer_sound checked
    }
  else
    throw (.entry (.coreCheckFailed key (Core.LanguageResult.resultType projected.val)
      (Core.infer? (SourceCoreBasicEntry.inputContext inputs) body)))

/-- Authenticate the plan and compile every reachable global once. Public seed
values remain scalar/product; the internal policy admits monomorphic function
parameters, returned closures, shared captures, and indirect calls. -/
def prepare (program : CheckedProgram) (plan : Plan) (compilationFuel : Nat)
    (_reason : Core.Word) : Except Error PreparedProgram := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError SourceCoreRecursiveEntry.Error.preparation
  let functions ← executablePlan.specializations.reverse.mapM prepareFunction
  let globals := functions.map (·.signature)
  match executablePlan.seedKeys with
  | [] => pure { plan := executablePlan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreProgramFaultSites.prepare executablePlan first).mapError SourceCoreRecursiveEntry.Error.programFaultSites
      let closures ← functions.mapM (compileClosure executablePlan globals diagnostics compilationFuel)
      let entries ← executablePlan.seedKeys.mapM (assembleEntry executablePlan functions globals closures)
      pure { plan := executablePlan, entries }

end Solcore.Frontend.SourceCoreFunctionEntry
