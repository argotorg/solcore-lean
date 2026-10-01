import Solcore.Frontend.SourceCoreGeneralEntry
import Solcore.Frontend.SourceCoreGeneralTypes
import Solcore.Frontend.SourceCoreEvidence
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreDataFaultSites
import Solcore.Frontend.SourceCoreDataMatches
import Solcore.Frontend.SourceCoreDataPlaceFaultSites
import Solcore.Frontend.SourceCoreCallableContracts
import Solcore.Frontend.SourceCoreCallableFaultSites

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
  | callableContracts (error : SourceCoreStageCodebook.Error)
  | callableDiagnostics (error : SourceCoreCallableFaultSites.Error)
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

/-- Representation hooks retain the common contextual traversal, evidence
validation and control flow. The enclosing artifact checks generated code under
its actual data definitions, including any source-allocation marker suffix. -/
structure Representation where
  expressions : SourceCoreFunctions.Policy
  allowStaged : Bool := false
  loops : List SolvedRequirement → SourceCoreAssignmentFaultSites.Table →
    SourceCoreDataPlaceFaultSites.Program → Key → SourceCoreFunctions.ExpressionLowerer →
    SourceCoreLoops.Policy
  rawLambdaBodyAt : Key → TypeSystem.Substitution → SourceCoreFunctions.RawLambdaBodyHook :=
    fun _ _ => expressions.rawLambdaBody
  rawLambdaExpressionAt : Key → TypeSystem.Substitution → SourceCoreFunctions.RawLambdaExpressionHook :=
    fun _ _ => expressions.rawLambdaExpression
  /-- The assembled checker validates this hook after all named parameter
  cells have been bound. Its body still has the original raw argument slot. -/
  rawNamedBody : Function → Core.Expr → Except SourceCoreBasic.Error Core.Expr :=
    fun _ body => pure body
  /-- Preserve per-occurrence metadata after selecting a generalized local
  bundle. This does not change its representation type or select evidence. -/
  localReadView : Key → TypeSystem.Substitution → TypedSource → SourceCoreBasic.Scope →
    ExpressionId → SourceCoreBasic.LoweredExpr → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr :=
    fun _ _ _ _ _ lowered => pure lowered
  allocatorAt : Key → TypeSystem.Substitution → Option SourceCoreSourceCells.Allocator :=
    fun _ _ => expressions.sourceCells
  loopsWithSourceCells : Option SourceCoreSourceCells.Allocator →
    List SolvedRequirement → SourceCoreAssignmentFaultSites.Table →
    SourceCoreDataPlaceFaultSites.Program → Key → SourceCoreFunctions.ExpressionLowerer →
    SourceCoreLoops.Policy := fun cells solved assignments diagnostics owner expression =>
      {loops solved assignments diagnostics owner expression with sourceCells := cells}

def Representation.atContext (representation : Representation) (owner : Key)
    (active : TypeSystem.Substitution) : Representation :=
  {representation with expressions := {representation.expressions with
    sourceCells := representation.allocatorAt owner active
    rawLambdaBody := representation.rawLambdaBodyAt owner active
    rawLambdaExpression := representation.rawLambdaExpressionAt owner active}}

private def prepareInputs (representation : Representation) (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List (TypedBinder × Core.Ty))
  | _, [] => pure []
  | scope, binder :: rest => do
      let type ← (representation.expressions.lowerBinder source scope binder).mapError Error.lowering
      let remaining ← prepareInputs representation source ((binder.id, type) :: scope) rest
      pure ((binder, type) :: remaining)

def prepareFunctionWithRepresentation (program : CheckedProgram) (representation : Representation) (specialized : SourceSpecialization.SpecializedFunction) :
    Except Error Function := do
  let function := specialized.function
  discard <| (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program specialized.key specialized.assumptions)
    |>.mapError Error.plan
  if function.returnComptime && !representation.allowStaged then throw (.stagedResultUnsupported specialized.key)
  let (parameter, result) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.invalidFunctionType specialized.key)
  if result ≠ function.inferredBodyType then throw (.resultMetadataMismatch specialized.key)
  let site := SourceCoreElaboration.ErrorSite.declaration specialized.key.declaration
  let parameterType ← (representation.expressions.projectType site parameter).mapError Error.lowering
  let resultType ← (representation.expressions.projectType site result).mapError Error.lowering
  let inputs ← prepareInputs representation function.typedBody [] function.typedBody.inputs
  pure { specialized, inputs, signature := { key := specialized.key, parameterType, resultType } }

/-- The strict catalog uses the same compiler entry as other representations. -/
def strictRepresentation (checked : Checked) (signatures : ProgramSignatures) : Representation := {
  expressions := SourceCoreGeneralTypes.policy checked signatures
  allowStaged := checked.catalog.callableContracts
  loops := fun solvedRequirements assignments diagnostics owner expression => {
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
    }
}

def bodyLowererWithRepresentation (representation : Representation)
    (solvedRequirements : List SolvedRequirement) (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key)
    (lowerBinder : TypedSource → SourceCoreBasic.Scope → TypedBinder → Except SourceCoreBasic.Error Core.Ty :=
      representation.expressions.lowerBinder) : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      representation.loopsWithSourceCells representation.expressions.sourceCells
        solvedRequirements assignments diagnostics owner expression with
      sourceCells := representation.expressions.sourceCells
      lowerBinder
    } fuel source scope statements result reasonAt fellThrough escaped

/-- Existing strict callers retain their catalog and diagnostics API. -/
def bodyLowerer (checked : Checked) (signatures : ProgramSignatures)
    (solvedRequirements : List SolvedRequirement) (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (owner : Key)
    (lowerBinder : TypedSource → SourceCoreBasic.Scope → TypedBinder → Except SourceCoreBasic.Error Core.Ty :=
      SourceCoreGeneralTypes.lowerBinder checked) : SourceCoreFunctions.BodyLowerer :=
  bodyLowererWithRepresentation (strictRepresentation checked signatures)
    solvedRequirements assignments diagnostics owner lowerBinder

private def localError (id : ExpressionId) (node : ExpressionNode)
    (error : SourceCoreLocalPolymorphism.Error) : SourceCoreBasic.Error :=
  match error with
  | .metadata error => error
  | _ => .unsupportedExpression id node.form

/-- The production binder policy, retained in static receipts connecting an
accepted function body to its exact contextual statement traversal. -/
def contextualBinder (representation : Representation) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : Key) (active : TypeSystem.Substitution) (source : TypedSource)
    (scope : SourceCoreBasic.Scope) (binder : TypedBinder) : Except SourceCoreBasic.Error Core.Ty :=
  if binder.scheme.quantified.isEmpty then representation.expressions.lowerBinder source scope binder
  else (SourceCoreLocalPolymorphism.lowerBinder locals owner active source scope binder).mapError fun
    | .metadata error => error
    | _ => .polymorphicBinding binder.id

def contextualSource (program : CheckedProgram) (plan : Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : Key)
    (parent : Option SourceCoreLocalEvidence.Prepared) (source : TypedSource) (id : ExpressionId) :
    Except SourceCoreBasic.Error TypedSource := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  match node.form with
  | .reference _ (.local binder) =>
      if locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) then
        let binding ← (locals.binding owner binder).mapError (localError id node)
        (SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id).mapError fun
          | .plan error => .callPreparation error
          | .missingExpression missing => .missingExpression missing
          | _ => .unsupportedExpression id node.form
      else pure source
  | _ => pure source

/-- Authenticated callable metadata shared by the generated representation
and every indirect callsite in one prepared artifact. -/
structure CallableContext where
  table : SourceCoreStageCodebook.Table
  diagnostics : SourceCoreCallableFaultSites.Program

/-- The callable representation used by the general compiler. Keeping this
policy visible lets lowering proofs authenticate the actual emitted wrapper. -/
def callablePolicy (native : Option CallableContext) (active : TypeSystem.Substitution) :
    SourceCoreFunctions.CallablePolicy :=
  match native with
  | none => {}
  | some native => {
      functionType := Core.CallableContract.functionType
      allowStaged := true
      decorateCallable := fun context _ node origin parameter result raw => do
        let origin := match origin with
          | .named key => SourceCoreStageCodebook.Origin.named key
          | .lambda id => .lambda context.owner id active
          | .builtin function => .builtin function
        let descriptor ← (SourceCoreCallableContracts.descriptor native.table origin).mapError fun _ =>
          SourceCoreBasic.Error.unsupportedExpression node.id node.form
        pure (match raw with
          | .inRight .word value => Core.LanguageResult.success (descriptor.wrap value)
          | _ => Core.LanguageResult.bind (Core.CallableContract.functionType parameter result) raw
              (Core.LanguageResult.success (descriptor.wrap (.var 0))))
      callCallable := fun context _ node result callee arguments => do
        match node.form with
        | .call _ _ (.indirect _) =>
            let site ← (SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
              native.diagnostics.reasonAt).mapError fun _ =>
                SourceCoreBasic.Error.unsupportedExpression node.id node.form
            pure (site.lower native.diagnostics.unknown result callee arguments)
        | .call _ _ (.builtinFunction function) =>
            let descriptor ← (SourceCoreCallableContracts.descriptor native.table (.builtin function)).mapError fun _ =>
              SourceCoreBasic.Error.unsupportedExpression node.id node.form
            pure (Core.CallableContract.call [⟨descriptor.id, none, none⟩]
              native.diagnostics.unknown result callee arguments)
        | _ => throw (.unsupportedExpression node.id node.form) }

/-- Contextual local instances re-enter the shared expression traversal with
concrete metadata. Every closure captures the same lexical references; the
bundle is constructed before the generalized binding's cell is allocated. -/
def lowerContextualExpression (program : CheckedProgram) (representation : Representation)
    (signatures : ProgramSignatures) (locals : SourceCoreLocalPolymorphism.Catalog)
    (candidateParents : List SourceCoreLocalEvidence.Prepared)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (context : SourceCoreFunctions.Context)
    (native : Option CallableContext)
    (parent : Option SourceCoreLocalEvidence.Prepared) (skipInitializer : Option ExpressionId) :
    SourceCoreFunctions.ExpressionLowerer
  | 0, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id, reasonAt => do
      let active := parent.map SourceCoreLocalEvidence.Prepared.substitution |>.getD []
      let representation := representation.atContext context.owner active
      let callables := callablePolicy native active
      let caller ← match parent with
        | some prepared => pure prepared.caller
        | none => (SourceCompilationPlan.exactSpecialization context.plan context.owner)
            |>.mapError SourceCoreBasic.Error.callPreparation
      let bind := contextualBinder representation locals context.owner active
      let lowerBody := bodyLowererWithRepresentation representation context.solvedRequirements assignments diagnostics context.owner bind
      let policy := { representation.expressions with
        callables
        lowerBinder := bind
        readExpression := fun source id => do
          let source ← contextualSource program context.plan locals context.owner parent source id
          representation.expressions.readExpression source id
        lowerSpecial? := some fun current child budget source scope id reasonAt => do
          let source ← contextualSource program current.plan locals current.owner parent source id
          let node ← match source.lookupExpression? id with
            | some node => pure node
            | none => throw (.missingExpression id)
          let initialized := locals.bindings.find? fun binding =>
            decide (binding.caller = current.owner ∧ binding.initializer = id)
          if let some initialized := initialized.filter (fun _ => skipInitializer ≠ some id) then
            let binding ← (locals.binding current.owner initialized.binder.id).mapError (localError id node)
            let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding active fun candidate => do
              let emission ← (SourceCoreLocalEvidence.prepareForEmission program current.plan candidate parent candidateParents).mapError fun _ =>
                SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch id
              let prepared := emission.prepared
              let childContext := { current with solvedRequirements := prepared.caller.function.solvedRequirements }
              let lowered ← (lowerContextualExpression program representation signatures locals candidateParents assignments diagnostics childContext native
                (some prepared) (some id) (min budget fuel) prepared.source scope id reasonAt)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
                |>.mapError SourceCoreLocalPolymorphism.Error.metadata
              match lowered.expression with
              | .inRight .word closure => pure closure
              | _ => throw (.initializerMetadataMismatch id)).mapError (localError id node)
            return some lowered
          let evidence ← SourceCoreEvidence.lowerWithProjector program representation.expressions.projectType caller current child budget source scope id reasonAt callables
          if let some lowered := evidence then return some lowered
          match node.form with
          | .reference _ (.local binder) =>
              if locals.bindings.any (fun binding => decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
                let lowered ← (SourceCoreLocalPolymorphism.lowerRead locals current.owner active source scope id (reasonAt id))
                  |>.mapError (localError id node)
                let viewed ← representation.localReadView current.owner active source scope id lowered
                SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
                return some viewed
              else return none
          | _ => return none }
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt
termination_by fuel => fuel

def compileClosureWithRepresentation (program : CheckedProgram) (representation : Representation) (signatures : ProgramSignatures) (plan : Plan)
    (globals : List Signature) (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (locals : SourceCoreLocalPolymorphism.Catalog) (native : Option CallableContext)
    (fuel : Nat) (function : Function) : Except Error Core.Expr := do
  let representation := representation.atContext function.signature.key []
  let source := function.specialized.function.typedBody
  let candidateParents ← (SourceCoreStageCodebook.prepareContexts program plan
    (locals.bindings.flatMap (·.instances))).mapError Error.callableContracts
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
  let lowerBody := bodyLowererWithRepresentation representation function.specialized.function.solvedRequirements own.assignments
    diagnostics function.signature.key (contextualBinder representation locals function.signature.key [])
  let body ← (lowerBody
    (lowerContextualExpression program representation signatures locals candidateParents own.assignments diagnostics context native none none)
    fuel source (function.inputs.reverse.map (fun (binder, type) => (binder.id, type))) statements
    function.signature.resultType (diagnostics.reasonAt function.signature.key)
    own.fellThroughReason own.table.escapedReason).mapError Error.lowering
  let body ← match representation.expressions.sourceCells with
    | none => pure (SourceCoreFunctions.bindParameters function.inputs function.signature.resultType body)
    | some allocate => (SourceCoreSourceCells.bindParameters allocate source [] function.inputs
        function.signature.resultType SourceCoreFunctions.argumentProjection body).mapError Error.lowering
  let body ← (representation.rawNamedBody function body).mapError Error.lowering
  pure (.lambda function.signature.parameterType (Core.LanguageResult.resultType function.signature.resultType) body)

def assembleCall (globals : List Signature) (functions : List Function) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let (function, index) ← match functions.zipIdx.find? (fun entry => decide (entry.1.signature.key = key)) with
    | some found => pure found
    | none => throw (.missingGlobal key)
  (SourceCoreBasic.ensureType (.declaration function.signature.key.declaration)
    function.signature.parameterType arguments.type).mapError Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  pure (SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures invoked))

private def assemble (globals : List Signature) (functions : List Function) (closures : List Core.Expr)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) {checked : Checked}
    (request : SourceCoreGeneralEntry.BodyRequest checked) : Except Error SourceCoreGeneralEntry.LoweredBody := do
  let arguments := SourceCoreCalls.packArguments (request.inputs.zipIdx.map fun (input, index) =>
    ⟨input.type, Core.OptionalCell.read input.type
      (.var (globals.length + (request.inputs.length - 1 - index))) Core.Word.zero⟩)
  let expression ← assembleCall globals functions closures request.specialized.key arguments
  pure {
    expression
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
  let representation := strictRepresentation checked program.signatures
  let functions ← (plan.specializations.reverse.mapM (prepareFunctionWithRepresentation program representation)).mapError
    SourceCoreGeneralEntry.CompileError.lowering
  let globals := functions.map (·.signature)
  match plan.seedKeys with
  | [] => pure { plan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreDataPlaceFaultSites.prepare checked program.signatures plan first).mapError
        (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.diagnostics)
      let native ← if checked.catalog.callableContracts then do
          let table ← (SourceCoreStageCodebook.prepare program plan checked).mapError
            (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.callableContracts)
          let callableDiagnostics ← (SourceCoreCallableFaultSites.prepare plan table diagnostics.rootTable).mapError
            (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.callableDiagnostics)
          pure (some { table, diagnostics := callableDiagnostics : CallableContext })
        else pure none
      let locals ← match native with
        | none => pure locals
        | some native => (locals.withCallableContracts (fun caller initializer active =>
            native.table.idAt? (.lambda caller initializer active))).mapError (SourceCoreGeneralEntry.CompileError.lowering ∘ Error.localInstances)
      let diagnostics := match native with
        | none => diagnostics
        | some native => { diagnostics with rootTable := native.diagnostics.rootTable }
      let closures ← (functions.mapM (compileClosureWithRepresentation program representation program.signatures plan globals diagnostics locals native fuel)).mapError
        SourceCoreGeneralEntry.CompileError.lowering
      SourceCoreGeneralEntry.prepareValidated plan checked fuel (fun _ request =>
        assemble globals functions closures diagnostics request) true

end Solcore.Frontend.SourceCoreGeneralFunctions
