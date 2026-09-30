import Solcore.Frontend.SourceCoreBasicEntry
import Solcore.Frontend.SourceCoreCalls
import Solcore.Frontend.SourceCoreProgramFaultSites

/-! Prepared scalar/product programs with monomorphic named recursion.
Compilation installs ordinary optional function cells before entering a seed.
Closures retain the shared global references and allocate source parameters in
source order on every call. Invocation reuses BasicEntry's checked input and
checkpoint APIs; it does not compile or interpret source code.

The resulting Core store also contains wrapper inputs and administrative
function cells. This module proves Core typing through the checker; it does
not assert the old equal-index source/Core heap correspondence. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRecursiveEntry

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Input := SourceCoreBasicEntry.Input
abbrev Entry := SourceCoreBasicEntry.Entry
abbrev PreparedProgram := SourceCoreBasicEntry.PreparedProgram

inductive Error where
  | preparation (error : SourceCompilationPlan.Error)
  | entry (error : SourceCoreBasicEntry.Error)
  | lowering (error : SourceCoreBasic.Error)
  | programFaultSites (error : SourceCoreProgramFaultSites.Error)
  | missingDiagnostics (key : Key)
  | missingGlobal (key : Key)
  | stagedInputUnsupported (key : Key) (binder : Resolved.LocalId)
  deriving Repr, DecidableEq

/-- All metadata required to compile one closed specialization. -/
structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List Input
  sourceResultType : TypeSystem.Ty
  resultProjection : SourceCoreElaboration.lowerType (.declaration signature.key.declaration)
    sourceResultType = .ok signature.resultType
  deriving Repr

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
  let parameterType ← (SourceCoreBasic.projectType (.declaration key.declaration) sourceParameterType).mapError Error.lowering
  let projected ← match projection : SourceCoreElaboration.lowerType (.declaration key.declaration) sourceResultType with
    | .ok resultType => pure (⟨resultType, projection⟩ : { resultType : Core.Ty //
        SourceCoreElaboration.lowerType (.declaration key.declaration) sourceResultType = .ok resultType })
    | .error error => .error (.lowering (.typeProjection error))
  let inputs ← (SourceCoreBasicEntry.prepareInputs function.typedBody).mapError Error.entry
  for input in inputs do
    if input.comptime then throw (.stagedInputUnsupported key input.id)
  pure {
    specialized, inputs, sourceResultType
    signature := { key, parameterType, resultType := projected.val }
    resultProjection := projected.property
  }

/-- Select one argument from source's Unit/single/right-product bundle.
Only indices below the original parameter count are used by bindParameters. -/
def argumentProjection (index : Nat) : Nat → Core.Expr → Core.Expr
  | 0, _ => .unit
  | 1, bundle => bundle
  | count + 2, bundle =>
      if index = 0 then .first bundle
      else argumentProjection (index - 1) (count + 1) (.second bundle)

/-- The incoming raw bundle follows the already allocated parameter cells.
The helper's weakening accounts for its temporary successful payload. -/
def bindParameters (inputs : List Input) (resultType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  inputs.zipIdx.foldr (fun (input, index) continuation =>
    Core.LocalSequence.letInitialized resultType input.type
      (Core.LanguageResult.success (argumentProjection index inputs.length (.var index))) continuation) body

/-- Allocate in plan order, producing global references in newest-first order. -/
def allocateGlobals (planOrder : List Signature) (body : Core.Expr) : Core.Expr :=
  planOrder.foldr (fun signature continuation =>
    .letE (Core.OptionalCell.allocate signature.functionType) continuation) body

/-- Every write is expressed in the same global environment. Its Unit result
is weakened into the remainder, including any subsequent closure bodies. -/
def installFunctions (closures : List Core.Expr) (body : Core.Expr) : Core.Expr :=
  closures.zipIdx.foldr (fun (closure, index) continuation =>
    .letE (.storeCell (.var index) (.inRight .unit closure)) (continuation.weakenAt 0)) body

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
  let context : SourceCoreCalls.Context := {
    plan, globals
    owner := function.signature.key
    administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let body ← (SourceCoreLoops.lowerStatementsWithExpression
    (fun fuel source scope id reasonAt =>
      SourceCoreCalls.lowerExpressionWithReasons fuel context source scope id reasonAt)
    compilationFuel source (SourceCoreBasicEntry.inputScope function.inputs) statements
    function.signature.resultType ownSites.table.reasonAt ownSites.fellThroughReason
    ownSites.table.escapedReason).mapError Error.lowering
  pure (.lambda function.signature.parameterType
    (Core.LanguageResult.resultType function.signature.resultType)
    (bindParameters function.inputs function.signature.resultType body))

/-- Wrapper input cells are read in original parameter order. The seed callee
then allocates its own source parameter cells just like every other call. -/
def seedArguments (globals : List Signature) (inputs : List Input) : SourceCoreBasic.LoweredExpr :=
  SourceCoreCalls.packArguments (inputs.zipIdx.map fun (input, index) =>
    ⟨input.type, Core.OptionalCell.read input.type
      (.var (globals.length + (inputs.length - 1 - index))) Core.Word.zero⟩)

private def assembleEntry (plan : Plan) (functions : List Function)
    (globals : List Signature) (closures : List Core.Expr) (key : Key) : Except Error Entry := do
  let (function, index) ← match functions.zipIdx.find? (fun item => decide (item.1.signature.key = key)) with
    | some item => pure item
    | none => .error (.missingGlobal key)
  let diagnostics ← (SourceCoreProgramFaultSites.prepare plan key).mapError Error.programFaultSites
  let arguments := seedArguments globals function.inputs
  (SourceCoreBasic.ensureType (.declaration key.declaration) function.signature.parameterType arguments.type).mapError Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  let body := allocateGlobals globals.reverse (installFunctions closures invoked)
  if checked : Core.infer? (SourceCoreBasicEntry.inputContext function.inputs) body =
      some (Core.LanguageResult.resultType function.signature.resultType) then
    pure {
      key := function.signature.key
      inputs := function.inputs
      sourceResultType := function.sourceResultType
      resultType := function.signature.resultType
      resultProjection := function.resultProjection
      faultSites := diagnostics.rootTable
      body
      bodyTyped := Core.infer_sound checked
    }
  else
    throw (.entry (.coreCheckFailed key (Core.LanguageResult.resultType function.signature.resultType)
      (Core.infer? (SourceCoreBasicEntry.inputContext function.inputs) body)))

/-- Canonical preparation and closure compilation happen once. Every seed
gets the same global installation and its own complete diagnostic projection.
Local lambdas, indirect calls, staged inputs/results, assumption dictionaries
and non-scalar/product source types remain explicit preparation failures. -/
def prepare (program : CheckedProgram) (plan : Plan) (compilationFuel : Nat)
    (_reason : Core.Word) : Except Error PreparedProgram := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.preparation
  let functions ← executablePlan.specializations.reverse.mapM prepareFunction
  let globals := functions.map (·.signature)
  match executablePlan.seedKeys with
  | [] => pure { plan := executablePlan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreProgramFaultSites.prepare executablePlan first).mapError Error.programFaultSites
      let closures ← functions.mapM (compileClosure executablePlan globals diagnostics compilationFuel)
      let entries ← executablePlan.seedKeys.mapM (assembleEntry executablePlan functions globals closures)
      pure { plan := executablePlan, entries }

end Solcore.Frontend.SourceCoreRecursiveEntry
