import Solcore.Frontend.SourceCoreGeneralTypes

/-! Closed evidence is authenticated against the prepared source plan before
being erased from Core function signatures. Retained operator and coercion
methods use the same cached global cells as ordinary calls. This pass generates
Core code; no source evaluator is used at invocation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreEvidence

open SourceInference TypeSystem
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Context := SourceCoreFunctions.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev Lowered := SourceCoreBasic.LoweredExpr
abbrev Child := SourceCoreFunctions.ExpressionLowerer
abbrev Key := SourceSpecialization.SpecializationKey

private def project (checked : Checked) (node : ExpressionNode) (type : Ty) : Except Error Core.Ty :=
  SourceCoreGeneralTypes.projectType checked (.occurrence node.id.occurrence) type

private def signature (checked : Checked) (context : Context) (node : ExpressionNode) (key : Key)
    (callables : SourceCoreFunctions.CallablePolicy) :
    Except Error (Nat × SourceCoreCalls.Signature) := do
  let actual ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  if !callables.allowStaged &&
      (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime)) then
    throw (.unsupportedExpression node.id node.form)
  let (parameter, result) ← match actual.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => throw (.callPreparation (.invalidFunctionType key actual.function.type))
  let (stored, index) ← match context.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
    | [entry] => pure entry
    | [] => throw (.callPreparation (.missingSpecialization key))
    | entries => throw (.callPreparation (.duplicateSpecialization key entries.length))
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.parameterType (← project checked node parameter)
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.resultType (← project checked node result)
  pure (index, stored)

private def invoke (checked : Checked) (context : Context) (scope : Scope) (node : ExpressionNode)
    (key : Key) (arguments : Lowered) (callables : SourceCoreFunctions.CallablePolicy) :
    Except Error Lowered := do
  let (index, selected) ← signature checked context node key callables
  SourceCoreBasic.ensureType (.occurrence node.id.occurrence) selected.parameterType arguments.type
  pure ⟨selected.resultType, SourceCoreCalls.call selected
    (scope.length + context.administrativePrefix + index) arguments.expression context.internalReason⟩

private def methodKey (context : Context) (node : ExpressionNode)
    (method : ExecutableImplMethods.CheckedMethod) : Except Error Key :=
  (SourceCompilationPlan.exactCallKey context.plan context.owner node.id method.specialized.key)
    |>.mapError SourceCoreBasic.Error.callPreparation

private def applyCoercions (program : CheckedProgram) (checked : Checked) (context : Context)
    (caller : SourceSpecialization.SpecializedFunction) (available : SourceCompilationPlan.EvidenceEnvironment)
    (scope : Scope) (node : ExpressionNode) (callables : SourceCoreFunctions.CallablePolicy) :
    Lowered → List CoercionStep → Except Error Lowered
  | value, [] => pure value
  | value, step :: rest => do
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project checked node step.source) value.type
      let method ← (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
        |>.mapError SourceCoreBasic.Error.callPreparation
      discard <| (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
        |>.mapError SourceCoreBasic.Error.callPreparation
      let key ← methodKey context node method
      let result ← invoke checked context scope node key value callables
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project checked node step.target) result.type
      applyCoercions program checked context caller available scope node callables result rest

private def withNode (source : TypedSource) (node : ExpressionNode) : TypedSource :=
  { source with nodes := source.nodes.map fun
      | .expression old => if old.id = node.id then .expression node else .expression old
      | .statement old => .statement old }

/-- The prepared plan authenticates closed evidence and selected helper edges.
Each special occurrence rechecks its ledger and endpoint types before emitting
ordinary Core calls, including output coercions and indirect argument coercions. -/
def lowerWithCaller (program : CheckedProgram) (checked : Checked)
    (caller : SourceSpecialization.SpecializedFunction) (context : Context) (child : Child)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) (callables : SourceCoreFunctions.CallablePolicy := {}) :
    Except Error (Option Lowered) := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => throw (.missingExpression id)
  let hasIndirectCoercions := match node.form with
    | .call _ _ (.indirect metadata) => !metadata.argumentCoercions.isEmpty
    | _ => false
  let ordinary ← match node.form with
    | .call _ _ (.declaration _) | .reference _ (.declaration _) => pure []
    | _ => match SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | some requirements => pure requirements
        | none => throw (.callPreparation (.unsupportedRequirements node.requirements))
  let isNativeLiteral := match node.form with | .integerLiteral .. => true | _ => false
  if node.coercions.isEmpty && !hasIndirectCoercions && (node.requirements.isEmpty || isNativeLiteral) then
    return none
  unless node.hasValidCoercionPath do throw (.coercionsPresent id)
  if caller.key ≠ context.owner then throw (.ownerMismatch context.owner.declaration caller.key.declaration)
  let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    |>.mapError SourceCoreBasic.Error.callPreparation
  let raw := {node with type := node.rawType, requirements := ordinary, coercions := []}
  let result ← match node.form with
    | .call callee arguments (.declaration instantiation) => do
        (SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let evidence ← (SourceCompilationPlan.exactDirectCallRuntimeEvidence caller node available instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
        let key ← (SourceCompilationPlan.exactCallKey context.plan context.owner id target).mapError SourceCoreBasic.Error.callPreparation
        let selected ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
        (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key selected.assumptions evidence)
          |>.mapError SourceCoreBasic.Error.callPreparation
        if arguments.length ≠ selected.function.typedBody.inputs.length then
          throw (.callPreparation (.argumentArityMismatch selected.function.typedBody.inputs.length arguments.length))
        let arguments ← arguments.mapM fun argument => child fuel source scope argument reasonAt
        invoke checked context scope raw key (SourceCoreCalls.packArguments arguments) callables
    | .reference _ (.declaration instantiation) => do
        let evidence ← (SourceCompilationPlan.exactDeclarationReferenceRuntimeEvidence caller node available instantiation)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
        let key ← (SourceCompilationPlan.exactReferenceKey context.plan context.owner id target).mapError SourceCoreBasic.Error.callPreparation
        let selected ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
        (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key selected.assumptions evidence)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let (index, stored) ← signature checked context raw key callables
        let identity ← match Core.Word.ofNat? (index + 1) with
          | some identity => pure identity
          | none => throw (.unsupportedExpression id node.form)
        let expression ← callables.decorateCallable context source node (.named key)
          stored.parameterType stored.resultType
          (SourceCoreFunctions.namedReference stored (scope.length + context.administrativePrefix + index)
            identity context.internalReason)
        pure ⟨callables.functionType stored.parameterType stored.resultType, expression⟩
    | .call callee arguments (.indirect metadata) => do
        (SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata)
          |>.mapError SourceCoreBasic.Error.callPreparation
        let callee ← child fuel source scope callee reasonAt
        let arguments ← arguments.mapM fun argument => child fuel source scope argument reasonAt
        let packed ← applyCoercions program checked context caller available scope node callables
          (SourceCoreCalls.packArguments arguments) metadata.argumentCoercions
        let resultType ← project checked node node.rawType
        let parameterType ← project checked node metadata.argumentTypeAfterCoercion
        SourceCoreBasic.ensureType (.occurrence id.occurrence) parameterType packed.type
        SourceCoreBasic.ensureType (.occurrence id.occurrence)
          (callables.functionType parameterType resultType) callee.type
        let expression ← callables.callCallable context source node resultType callee.expression packed.expression
        pure ⟨resultType, expression⟩
    | .unary operator operand => do
        if ordinary.isEmpty then child fuel (withNode source raw) scope id reasonAt
        else
          let selected ← (SourceCompilationPlan.checkedUnaryOperatorMethod program caller raw available operator)
            |>.mapError SourceCoreBasic.Error.callPreparation
          discard <| (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller raw selected)
            |>.mapError SourceCoreBasic.Error.callPreparation
          let key ← methodKey context raw selected.method
          let operand ← child fuel source scope operand reasonAt
          invoke checked context scope raw key operand callables
    | .binary left operator right => do
        if ordinary.isEmpty then child fuel (withNode source raw) scope id reasonAt
        else
          let selected ← (SourceCompilationPlan.checkedBinaryOperatorMethod program caller raw available operator)
            |>.mapError SourceCoreBasic.Error.callPreparation
          discard <| (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller raw selected)
            |>.mapError SourceCoreBasic.Error.callPreparation
          let key ← methodKey context raw selected.method
          let arguments ← [left, right].mapM fun argument => child fuel source scope argument reasonAt
          invoke checked context scope raw key (SourceCoreCalls.packArguments arguments) callables
    | _ => child fuel (withNode source raw) scope id reasonAt
  SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project checked node node.rawType) result.type
  let result ← applyCoercions program checked context caller available scope node callables result node.coercions
  SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project checked node node.type) result.type
  pure (some result)

/-- Ordinary occurrences use the exact authenticated plan caller. Contextual
local lambdas supply an authenticated rebinding of the same caller ledger to
`lowerWithCaller`; helper edges and selected globals still use the same plan. -/
def lower (program : CheckedProgram) (checked : Checked) (context : Context) (child : Child)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) (callables : SourceCoreFunctions.CallablePolicy := {}) :
    Except Error (Option Lowered) := do
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner)
    |>.mapError SourceCoreBasic.Error.callPreparation
  lowerWithCaller program checked caller context child fuel source scope id reasonAt callables

end Solcore.Frontend.SourceCoreEvidence
