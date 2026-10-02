import Solcore.Frontend.SourceCoreEvidence

/-! The real coercion compiler selects ordered methods and global cells before
emitting nested native calls. These static receipts retain complete method and
dictionary data; they do not assert source method selection or body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
open Core Frontend SourceInference
abbrev Lowered := SourceCoreBasic.LoweredExpr
abbrev Context := SourceCoreFunctions.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Projector := SourceCoreEvidence.Projector
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev RuntimeEvidence := SourceCompilationPlan.EvidenceEnvironment
abbrev Key := SourceCompilationPlan.Key

structure Call where
  signature : SourceCoreCalls.Signature
  index : Nat
  deriving Repr, DecidableEq

def emit (reason : Word) (input : Expr) : List Call → Expr
  | [] => input
  | call :: calls => emit reason (SourceCoreCalls.call call.signature call.index input reason) calls

/-- One actual checked edge, including its ordered dictionary and exact unique
global row. The saved method is not reconstructed from its key or native type. -/
structure Step (program : CheckedProgram) (project : Projector) (context : Context)
    (caller : Specialized) (available : RuntimeEvidence) (scope : Scope)
    (node : ExpressionNode) (policy : SourceCoreFunctions.CallablePolicy)
    (input : Lowered) (step : CoercionStep) (output : Lowered) (call : Call) where
  method : ExecutableImplMethods.CheckedMethod
  dictionary : RuntimeEvidence
  key : Key
  specialized : Specialized
  parameter : TypeSystem.Ty
  result : TypeSystem.Ty
  globalIndex : Nat
  sourceProjected : project (.occurrence node.id.occurrence) step.source = .ok input.type
  selectedMethod : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method
  materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method = .ok dictionary
  edge : SourceCompilationPlan.exactCallKey context.plan context.owner node.id method.specialized.key = .ok key
  selected : SourceCompilationPlan.exactSpecialization context.plan key = .ok specialized
  staged : (!policy.allowStaged && (specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime))) = false
  functionType : specialized.function.type = .function parameter result
  global : context.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = [(call.signature, globalIndex)]
  parameterProjected : project (.occurrence node.id.occurrence) parameter = .ok call.signature.parameterType
  resultProjected : project (.occurrence node.id.occurrence) result = .ok call.signature.resultType
  inputType : call.signature.parameterType = input.type
  location : call.index = scope.length + context.administrativePrefix + globalIndex
  emitted : output = ⟨call.signature.resultType, SourceCoreCalls.call call.signature call.index input.expression context.internalReason⟩
  targetProjected : project (.occurrence node.id.occurrence) step.target = .ok output.type

inductive Spine (program : CheckedProgram) (project : Projector) (context : Context)
    (caller : Specialized) (available : RuntimeEvidence) (scope : Scope)
    (node : ExpressionNode) (policy : SourceCoreFunctions.CallablePolicy) :
    Lowered → List CoercionStep → Lowered → List Call → Prop where
  | nil {input} : Spine program project context caller available scope node policy input [] input []
  | cons {input step middle rest output call calls}
      (head : Step program project context caller available scope node policy input step middle call)
      (tail : Spine program project context caller available scope node policy middle rest output calls) :
      Spine program project context caller available scope node policy input (step :: rest) output (call :: calls)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem discard_ok {α ε : Type} {action : Except ε α} {returned : Unit}
    (accepted : (discard action : Except ε Unit) = .ok returned) : ∃ value, action = .ok value := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl⟩

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {returned : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok returned) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted <;> simp_all

/-- The compiler's recursive helper supplies every row, endpoint and emitted
call. There is no independent premise for an intermediate selector. -/
theorem of_accepted {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List CoercionStep}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy input steps = .ok output) :
    ∃ calls, Spine program project context caller available scope node policy input steps output calls := by
  induction steps generalizing input with
  | nil => cases accepted; exact ⟨[], .nil⟩
  | cons step rest ih =>
    unfold SourceCoreEvidence.applyCoercions at accepted
    obtain ⟨sourceType, projectedSource, accepted⟩ := bind_ok accepted
    obtain ⟨_, sourceTypeEq, accepted⟩ := bind_ok accepted
    obtain ⟨method, methodAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨_, dictionaryAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨dictionary, dictionaryAccepted⟩ := discard_ok dictionaryAccepted
    obtain ⟨key, edge, accepted⟩ := bind_ok accepted
    obtain ⟨middle, invoked, accepted⟩ := bind_ok accepted
    obtain ⟨targetType, projectedTarget, accepted⟩ := bind_ok accepted
    obtain ⟨_, targetTypeEq, accepted⟩ := bind_ok accepted
    obtain ⟨calls, tail⟩ := ih accepted
    obtain ⟨pair, signatureAccepted, invoked⟩ := bind_ok invoked
    rcases pair with ⟨index, stored⟩
    obtain ⟨_, inputTypeEq, emitted⟩ := bind_ok invoked
    change (pure ⟨stored.resultType, SourceCoreCalls.call stored
      (scope.length + context.administrativePrefix + index) input.expression context.internalReason⟩ : Except SourceCoreBasic.Error Lowered) = .ok middle at emitted
    have middleEq := (Except.ok.inj emitted).symm
    change ((do
      let actual ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
      if !policy.allowStaged && (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime)) then
        throw (.unsupportedExpression node.id node.form)
      let (parameter, result) ← match actual.function.type with
        | .function parameter result => pure (parameter, result)
        | _ => throw (.callPreparation (.invalidFunctionType key actual.function.type))
      let (stored, index) ← match context.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
        | [row] => pure row
        | [] => throw (.callPreparation (.missingSpecialization key))
        | rows => throw (.callPreparation (.duplicateSpecialization key rows.length))
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.parameterType (← project (.occurrence node.id.occurrence) parameter)
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.resultType (← project (.occurrence node.id.occurrence) result)
      pure (index, stored)) : Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) = .ok (index, stored) at signatureAccepted
    obtain ⟨actual, selected, signatureAccepted⟩ := bind_ok signatureAccepted
    by_cases staged : (!policy.allowStaged && (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime))) = true
    · simp [staged, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at signatureAccepted
    · simp only [staged] at signatureAccepted
      cases functionType : actual.function.type <;>
        simp only [functionType, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at signatureAccepted <;>
        try contradiction
      rename_i parameter result
      generalize global : context.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = rows at signatureAccepted
      cases rows with
      | nil => cases signatureAccepted
      | cons row rows =>
        cases rows with
        | cons second rest => cases signatureAccepted
        | nil =>
          rcases row with ⟨selectedStored, selectedIndex⟩
          obtain ⟨parameterType, projectedParameter, signatureAccepted⟩ := bind_ok signatureAccepted
          obtain ⟨_, parameterTypeEq, signatureAccepted⟩ := bind_ok signatureAccepted
          obtain ⟨resultType, projectedResult, signatureAccepted⟩ := bind_ok signatureAccepted
          obtain ⟨_, resultTypeEq, same⟩ := bind_ok signatureAccepted
          cases same
          refine ⟨⟨selectedStored, scope.length + context.administrativePrefix + selectedIndex⟩ :: calls, .cons ?_ tail⟩
          exact {
            method, dictionary, key, specialized := actual, parameter, result, globalIndex := selectedIndex
            sourceProjected := by change project (.occurrence node.id.occurrence) step.source = .ok sourceType at projectedSource; rwa [ensure_eq sourceTypeEq] at projectedSource
            selectedMethod := mapError_ok methodAccepted
            materialized := mapError_ok dictionaryAccepted
            edge := mapError_ok edge
            selected := mapError_ok selected
            staged := by simpa using staged
            functionType, global
            parameterProjected := by rwa [← ensure_eq parameterTypeEq] at projectedParameter
            resultProjected := by rwa [← ensure_eq resultTypeEq] at projectedResult
            inputType := ensure_eq inputTypeEq
            location := rfl
            emitted := middleEq
            targetProjected := by change project (.occurrence node.id.occurrence) step.target = .ok targetType at projectedTarget; rwa [ensure_eq targetTypeEq] at projectedTarget }

theorem Spine.code {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls) :
    output.expression = emit context.internalReason input.expression calls := by
  induction receipt with
  | nil => rfl
  | cons head _ ih => simpa only [emit, head.emitted] using ih

theorem Spine.length {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls) : calls.length = steps.length := by
  induction receipt with
  | nil => rfl
  | cons _ _ ih => simpa using ih

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
