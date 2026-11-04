import Solcore.Frontend.SourceCoreEvidence
import Solcore.Frontend.ProgramChecking
import Solcore.Core.Renaming
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize

/-!
# Coercions: spines and preparation

The static receipts of a coercion spine and their evaluation, the reflection of specialization comparison, plan provenance and the preparation steps.

This file stays below `SourceCoreCallablePrincipals`: the proofs of the instances derived here fail once the private `BEq TypedBinder` of that module is visible.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
/-! Full reflection of the existing carrier comparison. Runtime comparisons
remain unchanged: every source node, ordered evidence tree and stage entry is
part of the equality returned here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
open Frontend SourceInference

deriving instance ReflBEq, LawfulBEq for BuiltinFunctionId
deriving instance ReflBEq, LawfulBEq for BuiltinTraitId
deriving instance ReflBEq, LawfulBEq for ProgramTraitId
deriving instance ReflBEq, LawfulBEq for BuiltinImplId
deriving instance ReflBEq, LawfulBEq for ProgramImplId
deriving instance ReflBEq, LawfulBEq for ProgramPredicate
deriving instance ReflBEq, LawfulBEq for RequirementId
deriving instance ReflBEq, LawfulBEq for OccurrenceId
deriving instance ReflBEq, LawfulBEq for Syntax.SourceOrigin
deriving instance ReflBEq, LawfulBEq for Syntax.SourceId
deriving instance ReflBEq, LawfulBEq for Syntax.SourceSpan
deriving instance ReflBEq, LawfulBEq for Syntax.Located
deriving instance ReflBEq, LawfulBEq for Syntax.CoreLiteralValue
deriving instance ReflBEq, LawfulBEq for Syntax.UnaryOp
deriving instance ReflBEq, LawfulBEq for Syntax.BinaryOp
deriving instance ReflBEq, LawfulBEq for Syntax.ValueAssignOp
deriving instance ReflBEq, LawfulBEq for ProgramDataConstructorId
deriving instance ReflBEq, LawfulBEq for LocalSchemeRequirement
deriving instance ReflBEq, LawfulBEq for TypedBinder
deriving instance ReflBEq, LawfulBEq for DeclarationInstantiation
deriving instance ReflBEq, LawfulBEq for DataConstructorInstantiation
deriving instance ReflBEq, LawfulBEq for CoercionStep
deriving instance ReflBEq, LawfulBEq for IntegerLiteralResolution
deriving instance ReflBEq, LawfulBEq for MatchPatternSource
deriving instance ReflBEq, LawfulBEq for MatchPatternInstruction
deriving instance ReflBEq, LawfulBEq for MatchPatternResolution
deriving instance ReflBEq, LawfulBEq for TypedMatchPattern
deriving instance ReflBEq, LawfulBEq for IndirectCallResolution
deriving instance ReflBEq, LawfulBEq for ReferenceResolution
deriving instance ReflBEq, LawfulBEq for CallResolution
deriving instance ReflBEq, LawfulBEq for ExpressionId
deriving instance ReflBEq, LawfulBEq for StatementId
deriving instance ReflBEq, LawfulBEq for TypedMatchCase
deriving instance ReflBEq, LawfulBEq for MatchResolution
deriving instance ReflBEq, LawfulBEq for PlaceProjection
deriving instance ReflBEq, LawfulBEq for PlaceResolution
deriving instance ReflBEq, LawfulBEq for AssignmentResolution
deriving instance ReflBEq, LawfulBEq for ForItemForm
deriving instance ReflBEq, LawfulBEq for NodeId
deriving instance ReflBEq, LawfulBEq for ExpressionForm
deriving instance ReflBEq, LawfulBEq for ExpressionNode
deriving instance ReflBEq, LawfulBEq for StatementForm
deriving instance ReflBEq, LawfulBEq for StatementNode
deriving instance ReflBEq, LawfulBEq for Node
deriving instance ReflBEq, LawfulBEq for TypedSource
deriving instance ReflBEq, LawfulBEq for PredicateEvidence
deriving instance ReflBEq, LawfulBEq for SolvedRequirement
deriving instance ReflBEq, LawfulBEq for CheckedFunction
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.Stage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.ExpressionStage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.BinderStage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.Analysis
deriving instance ReflBEq, LawfulBEq for SourceSpecialization.SpecializationKey
deriving instance ReflBEq, LawfulBEq for SourceSpecialization.SpecializedFunction

theorem eq_of_beq {left right : SourceSpecialization.SpecializedFunction}
    (same : (left == right) = true) : left = right := by
  exact LawfulBEq.eq_of_beq same

end Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
/-! Method selection and the original program check retain their actual
successful budgets. Complete checker results agree across those budgets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
open Frontend SourceInference

abbrev Checked (program : CheckedProgram) : Prop :=
  ∃ checkingFuel, ImplementationMethodBodiesChecked program.environment program.signatures checkingFuel
    (implementationMethodCheckTargets program.signatures) program.methods

theorem of_loaded {loaded : LoadedProgram} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkLoadedProgram loaded checkingFuel = .ok program) : Checked program :=
  ⟨checkingFuel, (checkLoadedProgram_success_body_checks accepted).2⟩

theorem of_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkProgram raw checkingFuel = .ok program) : Checked program := by
  obtain ⟨loaded, _loaded, accepted⟩ := checkProgram_success_load accepted
  exact of_loaded accepted

theorem of_empty_loaded {loaded : LoadedProgram} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkLoadedProgram loaded checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  have _ := empty
  exact of_loaded accepted

theorem of_empty_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkProgram raw checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  have _ := empty
  exact of_checked accepted

end Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
/-! Public worklist extension retains the complete supplied root and every
previously selected carrier. These static facts do not reconstruct a source
method or closure history from a key. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
open Frontend SourceInference SourceSpecializationWorklist
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Key := SourceSpecialization.SpecializationKey

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem next_fresh {program : CheckedProgram} {seen : List Key}
    {queue rest : List Request} {request : Request} {selected : Specialized}
    (accepted : nextUnseen program seen queue = .ok (some (request, selected, rest))) : selected.key ∉ seen := by
  induction queue generalizing request selected with
  | nil => cases accepted
  | cons current tail ih =>
    unfold nextUnseen at accepted
    obtain ⟨value, _, accepted⟩ := bind_ok accepted
    split at accepted
    · exact ih accepted
    · rename_i skipped
      have fresh : value.key ∉ seen := by
        intro member
        exact skipped (by simpa only [List.any_eq_true, decide_eq_true_eq, exists_eq_right] using member)
      cases accepted
      exact fresh

/-- Once a key is in the actual worklist's seen vector, its complete ordered
filter is unchanged by every finite continuation, including budget exhaustion. -/
theorem runAux_filter {program : CheckedProgram} {seeds seen : List Key} {queue : List Request}
    {entries : List Specialized} {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome} {key : Key}
    (known : key ∈ seen)
    (accepted : runAux program seeds queue seen entries calls references budget = .ok outcome) :
    outcome.plan.specializations.filter (fun entry => decide (entry.key = key)) =
      entries.filter (fun entry => decide (entry.key = key)) := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; rfl
    | some value => rcases value with ⟨request, selected, rest⟩; cases accepted; rfl
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, selected, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; rfl
    | some value =>
      rcases value with ⟨request, value, rest⟩
      have different : value.key ≠ key := fun same => next_fresh selected (same ▸ known)
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      have continued := ih (List.mem_cons_of_mem _ known) accepted
      simpa only [List.filter_append, List.filter_cons, List.filter_nil, decide_eq_false different, Bool.false_eq_true,
        if_false, List.append_nil] using continued

private theorem checked_none {duplicate : Option (Key × Nat)}
    (accepted : (match duplicate with
      | none => Except.ok ()
      | some (key, count) => Except.error (Error.duplicatePlanSpecializations key count)) = .ok ()) :
    duplicate = none := by
  cases duplicate with
  | none => rfl
  | some value => rcases value with ⟨key, count⟩; cases accepted

private theorem unique_keys {plan : Plan} (accepted : validatePlanSpecializationsUnique plan = .ok ()) :
    (plan.specializations.map (·.key)).Nodup := by
  rcases plan with ⟨seeds, entries, calls, references⟩
  induction entries with
  | nil => exact .nil
  | cons head rest ih =>
    unfold validatePlanSpecializationsUnique at accepted
    have noDuplicate := checked_none accepted
    change (if (rest.filter (fun entry => decide (entry.key = head.key))).isEmpty then _
      else some (head.key, (rest.filter (fun entry => decide (entry.key = head.key))).length + 1)) = none at noDuplicate
    split at noDuplicate
    · have absent : head.key ∉ rest.map (·.key) := by
        have empty : rest.filter (fun entry => decide (entry.key = head.key)) = [] := List.isEmpty_iff.mp ‹_ = true›
        intro member
        obtain ⟨entry, member, same⟩ := List.mem_map.mp member
        have : entry ∈ rest.filter (fun entry => decide (entry.key = head.key)) := List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using same⟩
        rw [empty] at this
        cases this
      have tailAccepted : validatePlanSpecializationsUnique ⟨seeds, rest, calls, references⟩ = .ok () := by
        unfold validatePlanSpecializationsUnique
        rw [noDuplicate]
        rfl
      exact List.nodup_cons.mpr ⟨absent, ih tailAccepted⟩
    · cases noDuplicate

private theorem find_filter {entries : List Specialized} {key : Key} {selected : Specialized}
    (unique : (entries.map (·.key)).Nodup)
    (found : entries.find? (fun entry => decide (entry.key = key)) = some selected) :
    entries.filter (fun entry => decide (entry.key = key)) = [selected] := by
  induction entries with
  | nil => cases found
  | cons head rest ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    by_cases same : head.key = key
    · simp only [List.find?_cons, same, decide_true] at found
      cases found
      have empty : rest.filter (fun entry => decide (entry.key = key)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro entry member
        intro picked
        have selected : entry.key = key := of_decide_eq_true picked
        exact absent (List.mem_map.mpr ⟨entry, member, selected.trans same.symm⟩)
      simp only [List.filter_cons, same, decide_true, if_true, empty]
    · simp only [List.find?_cons, decide_eq_false same] at found
      simpa only [List.filter_cons, decide_eq_false same, Bool.false_eq_true, if_false] using ih unique found

private theorem exact_filter {plan : Plan} {key : Key} {selected : Specialized}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    plan.specializations.filter (fun entry => decide (entry.key = key)) = [selected] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  assumption

private theorem exact_of_filter {plan : Plan} {key : Key} {selected : Specialized}
    (found : plan.specializations.filter (fun entry => decide (entry.key = key)) = [selected]) :
    SourceCompilationPlan.exactSpecialization plan key = .ok selected := by
  simp only [SourceCompilationPlan.exactSpecialization, found]

private theorem none_filter {entries : List Specialized} {key : Key}
    (missing : entries.find? (fun entry => decide (entry.key = key)) = none) :
    entries.filter (fun entry => decide (entry.key = key)) = [] := by
  exact List.filter_eq_nil_iff.mpr (List.find?_eq_none.mp missing)

private theorem key_mem {entries : List Specialized} {key : Key} {selected : Specialized}
    (found : entries.filter (fun entry => decide (entry.key = key)) = [selected]) : key ∈ entries.map (·.key) := by
  have member : selected ∈ entries.filter (fun entry => decide (entry.key = key)) := by rw [found]; simp
  obtain ⟨member, same⟩ := List.mem_filter.mp member
  exact List.mem_map.mpr ⟨selected, member, of_decide_eq_true same⟩

/-- Both root insertion and existing-root acceptance preserve exact carriers.
The public action itself supplies uniqueness and full-record comparison; no
additional validity or uniqueness premise is needed. -/
theorem extend {program : CheckedProgram} {plan : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program plan root edge budget = .ok outcome) :
    SourceCompilationPlan.exactSpecialization outcome.plan root.key = .ok root ∧
    ∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
      SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := by
  unfold extendCompletePlan at accepted
  obtain ⟨checked, unique, accepted⟩ := bind_ok accepted
  cases checked
  have unique := unique_keys unique
  split at accepted <;> try contradiction
  have finish : ∀ (entries : List Specialized) (requests : List Request) (calls : List CallEdge) (references : List ReferenceEdge),
      entries.filter (fun entry => decide (entry.key = root.key)) = [root] →
      (∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
        entries.filter (fun entry => decide (entry.key = key)) = [selected]) →
      runAux program plan.seedKeys requests (entries.map (·.key)) entries calls references budget = .ok outcome →
      SourceCompilationPlan.exactSpecialization outcome.plan root.key = .ok root ∧
        ∀ key selected, SourceCompilationPlan.exactSpecialization plan key = .ok selected →
          SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := by
    intro entries requests calls references rootFilter oldFilters completed
    constructor
    · exact exact_of_filter ((runAux_filter (key_mem rootFilter) completed).trans rootFilter)
    · intro key selected given
      have found := oldFilters key selected given
      exact exact_of_filter ((runAux_filter (key_mem found) completed).trans found)
  dsimp only at accepted
  split at accepted
  · rename_i missing
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    apply finish _ _ _ _ ?_ ?_ accepted
    · have empty := none_filter missing
      simp only [List.filter_append, empty, List.filter_cons, decide_true, if_true, List.filter_nil, List.nil_append]
    · intro key selected given
      have empty := none_filter missing
      have selectedFilter := exact_filter given
      have different : root.key ≠ key := by
        intro same
        rw [same, selectedFilter] at empty
        cases empty
      simpa only [List.filter_append, List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false,
        List.filter_nil, List.append_nil] using selectedFilter
  · rename_i previous found
    split at accepted <;> try contradiction
    rename_i same
    have equal := CallableSpecializationEquality.eq_of_beq same
    subst previous
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact finish _ _ _ _ (find_filter unique found) (fun _ _ given => exact_filter given) accepted

/-- Completion exposes the supplied root through the emitter's exact lookup. -/
theorem complete_root {program : CheckedProgram} {plan completed : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat}
    (accepted : extendCompletePlan program plan root edge budget = .ok (.complete completed)) :
    SourceCompilationPlan.exactSpecialization completed root.key = .ok root := (extend accepted).1

/-- Existing exact selections survive the real public extension action. -/
theorem selected_after {program : CheckedProgram} {plan : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome} {key : Key} {selected : Specialized}
    (accepted : extendCompletePlan program plan root edge budget = .ok outcome)
    (before : SourceCompilationPlan.exactSpecialization plan key = .ok selected) :
    SourceCompilationPlan.exactSpecialization outcome.plan key = .ok selected := (extend accepted).2 _ _ before

private theorem call_key {plan : Plan} {caller target selected : Key} {id : ExpressionId}
    (accepted : SourceCompilationPlan.exactCallKey plan caller id target = .ok selected) : selected = target := by
  unfold SourceCompilationPlan.exactCallKey at accepted
  split at accepted <;> try contradiction
  rename_i edge edges
  cases accepted
  have member : edge ∈ plan.callEdges.filter (fun edge => decide (edge.caller = caller) && decide (edge.occurrence = id) && decide (edge.callee = target)) := by rw [edges]; simp
  have same := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at same
  exact same.2

/-- The emitted step's selected carrier is the complete checked method root,
when its actual plan is the returned extension. No identity-only cast occurs. -/
theorem step_specialized {program : CheckedProgram} {project : CallableCoercionSpine.Projector}
    {context : CallableCoercionSpine.Context} {caller : Specialized}
    {available : CallableCoercionSpine.RuntimeEvidence} {scope : CallableCoercionSpine.Scope}
    {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {coercion : CoercionStep} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call)
    {before : Plan} {edge : CallEdge} {budget : Nat}
    (extended : extendCompletePlan program before step.method.specialized edge budget = .ok (.complete context.plan)) :
    step.specialized = step.method.specialized := by
  have selected := complete_root extended
  have sameKey := call_key step.edge
  have emitted := step.selected
  rw [sameKey] at emitted
  exact Except.ok.inj (emitted.symm.trans selected)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPlanProvenance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps
/-! Exact growth of the actual specialization worklist and finite preparation
loops. Positions and complete selected records survive later extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps
open Frontend SourceInference SourceSpecializationWorklist
abbrev Specialized := SourceSpecialization.SpecializedFunction

theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- Growth retains both the vector prefix and the emitter's exact lookup. -/
structure Extends (before after : Plan) : Prop where
  entries : before.specializations <+: after.specializations
  selected : ∀ key value, SourceCompilationPlan.exactSpecialization before key = .ok value →
    SourceCompilationPlan.exactSpecialization after key = .ok value

theorem Extends.refl (plan : Plan) : Extends plan plan :=
  ⟨List.prefix_refl _, fun _ _ given => given⟩

theorem Extends.trans {first middle last : Plan} (left : Extends first middle) (right : Extends middle last) :
    Extends first last := ⟨left.entries.trans right.entries, fun key value given => right.selected key value (left.selected key value given)⟩

theorem Extends.at {before after : Plan} (growth : Extends before after) {index : Nat} {value : Specialized}
    (found : before.specializations[index]? = some value) : after.specializations[index]? = some value := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨Nat.lt_of_lt_of_le bound growth.entries.length_le, (growth.entries.getElem bound).symm.trans same⟩

/-- The real queue appends complete records, including at budget exhaustion. -/
theorem runAux_prefix {program : CheckedProgram} {seeds seen : List SourceSpecialization.SpecializationKey}
    {queue : List Request} {entries : List Specialized} {calls : List CallEdge} {references : List ReferenceEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : runAux program seeds queue seen entries calls references budget = .ok outcome) :
    entries <+: outcome.plan.specializations := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact List.prefix_refl _
    | some value => rcases value with ⟨request, selected, rest⟩; cases accepted; exact List.prefix_refl _
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact List.prefix_refl _
    | some value =>
      rcases value with ⟨request, value, rest⟩
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      exact (show entries <+: entries ++ [value] from ⟨[value], rfl⟩).trans (ih accepted)

theorem extend {program : CheckedProgram} {before : Plan} {root : Specialized} {edge : CallEdge}
    {budget : Nat} {outcome : Outcome}
    (accepted : extendCompletePlan program before root edge budget = .ok outcome) : Extends before outcome.plan := by
  refine ⟨?_, (CallableCoercionPlanProvenance.extend accepted).2⟩
  unfold extendCompletePlan at accepted
  obtain ⟨checked, _, accepted⟩ := bind_ok accepted
  cases checked
  split at accepted <;> try contradiction
  dsimp only at accepted
  split at accepted
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact (show before.specializations <+: before.specializations ++ [root] from ⟨[root], rfl⟩).trans (runAux_prefix accepted)
  · split at accepted <;> try contradiction
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨⟨requests, calls, references⟩, _, accepted⟩ := bind_ok accepted
    exact runAux_prefix accepted

/-- Coverage is obtained from each actual loop step, in its original order.
The law does not remove repeated input items. -/
theorem forIn_coverage {α ε : Type} {items : List α} {initial final : Plan}
    {step : α → Plan → Except ε (ForInStep Plan)} {done : α → Plan → Prop}
    (accepted : forIn items initial step = .ok final)
    (monotone : ∀ item before after, Extends before after → done item before → done item after)
    (next : ∀ item ∈ items, ∀ before outcome, step item before = .ok outcome →
      ∃ after, outcome = .yield after ∧ Extends before after ∧ done item after) :
    Extends initial final ∧ ∀ item ∈ items, done item final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst final
    exact ⟨.refl _, by simp⟩
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, executed, finished⟩ := bind_ok accepted
    obtain ⟨after, rfl, growth, doneItem⟩ := next item (by simp) initial outcome executed
    obtain ⟨tailGrowth, doneRest⟩ := ih finished (fun value member => next value (by simp [member]))
    refine ⟨growth.trans tailGrowth, ?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact monotone _ _ _ tailGrowth doneItem
    · exact doneRest value member

/-- A visit retains the real selector, dictionary and extension action. Only
static plan lookup is transported to the eventual prepared plan. -/
structure Visit (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode)
    (coercion : CoercionStep) (final : Plan) where
  method : ExecutableImplMethods.CheckedMethod
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  before : Plan
  inserted : Plan
  budget : Nat
  selected : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method
  staged : SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized = .ok ()
  materialized : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method = .ok dictionary
  extended : extendCompletePlan program before method.specialized
    ⟨caller.key, node.id, method.specialized.key⟩ budget = .ok (.complete inserted)
  finalSelected : SourceCompilationPlan.exactSpecialization final method.specialized.key = .ok method.specialized

def Visit.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {coercion : CoercionStep} {before after : Plan}
    (visit : Visit program caller available node coercion before) (growth : Extends before after) :
    Visit program caller available node coercion after :=
  {visit with finalSelected := growth.selected _ _ visit.finalSelected}

/-- This premise is the actual private helper's body by definitional equality;
no replacement helper is evaluated. -/
theorem coercion_accepted {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {coercion : CoercionStep} {before after : Plan} {budget : Nat}
    (accepted : (do
      let method ← SourceCompilationPlan.checkedCoercionMethod program caller node available coercion
      SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized
      discard <| SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method
      let outcome ← match extendCompletePlan program before method.specialized
          ⟨caller.key, node.id, method.specialized.key⟩ budget with
        | .ok outcome => pure outcome
        | .error error => throw (.coercionMethodWorklist caller.key node.id coercion.requirement error)
      match outcome with
      | .complete extended => pure extended
      | .budgetExhausted _ next pending =>
          throw (.coercionMethodSpecializationBudgetExhausted caller.key node.id coercion.requirement next pending.length)
      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) :
    Extends before after ∧ Nonempty (Visit program caller available node coercion after) := by
  obtain ⟨method, selected, accepted⟩ := bind_ok accepted
  obtain ⟨returned, staged, accepted⟩ := bind_ok accepted
  cases returned
  obtain ⟨returned, materialized, accepted⟩ := bind_ok accepted
  cases returned
  have materialized : ∃ dictionary, SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method = .ok dictionary := by
    cases result : SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node coercion method with
    | error error => rw [result] at materialized; cases materialized
    | ok value => exact ⟨value, rfl⟩
  obtain ⟨dictionary, materialized⟩ := materialized
  cases extended : extendCompletePlan program before method.specialized ⟨caller.key, node.id, method.specialized.key⟩ budget with
  | error error => rw [extended] at accepted; cases accepted
  | ok outcome =>
    rw [extended] at accepted
    cases outcome with
    | budgetExhausted plan next pending => cases accepted
    | complete inserted =>
      cases accepted
      exact ⟨extend extended, ⟨⟨method, dictionary, before, _, budget, selected, staged, materialized,
        extended, CallableCoercionPlanProvenance.complete_root extended⟩⟩⟩


/-- Only the two forms traversed by the real operator preparation phase. -/
def OperatorForm (node : ExpressionNode) : Prop :=
  match node.form with
  | .unary _ _ | .binary _ _ _ => True
  | _ => False

def operatorOwnedNode (node : ExpressionNode) (requirements : List RequirementId) : ExpressionNode :=
  {node with type := node.rawType, requirements, coercions := []}

/-- The complete actual operator visit survives later worklist growth. The
owned requirements, staged boundary, materialized dictionary and complete
selected body are all retained separately. -/
structure OperatorVisit (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (final : Plan) where
  requirements : List RequirementId
  owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  nonempty : requirements ≠ []
  selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod
  arguments : List ExpressionId
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  before : Plan
  inserted : Plan
  budget : Nat
  selected : (match (operatorOwnedNode node requirements).form with
    | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
        (operatorOwnedNode node requirements) available operator
    | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
        (operatorOwnedNode node requirements) available operator
    | _ => throw (.unsupportedRequirements requirements)
    : Except SourceTypedRuntime.RuntimeError SourceCompilationPlan.CheckedRuntimeOperatorMethod) = .ok selection
  argumentsSelected : (match (operatorOwnedNode node requirements).form with
    | .unary _ operand => pure [operand]
    | .binary left _ right => pure [left, right]
    | _ => throw (.unsupportedRequirements requirements)
    : Except SourceTypedRuntime.RuntimeError (List ExpressionId)) = .ok arguments
  staged : SourceCompilationPlan.validateStagedCallBoundary caller (operatorOwnedNode node requirements)
    arguments selection.method.specialized = .ok ()
  materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
    (operatorOwnedNode node requirements) selection = .ok dictionary
  extended : extendCompletePlan program before selection.method.specialized
    ⟨caller.key, node.id, selection.method.specialized.key⟩ budget = .ok (.complete inserted)
  finalSelected : SourceCompilationPlan.exactSpecialization final selection.method.specialized.key =
    .ok selection.method.specialized

def OperatorVisit.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (visit : OperatorVisit program caller available node before) (growth : Extends before after) :
    OperatorVisit program caller available node after :=
  {visit with finalSelected := growth.selected _ _ visit.finalSelected}

def OperatorCovered (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (final : Plan) : Prop :=
  ∀ requirements, SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements →
    requirements ≠ [] → OperatorForm node → Nonempty (OperatorVisit program caller available node final)

theorem OperatorCovered.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (covered : OperatorCovered program caller available node before) (growth : Extends before after) :
    OperatorCovered program caller available node after := by
  intro requirements owned nonempty form
  obtain ⟨visit⟩ := covered requirements owned nonempty form
  exact ⟨visit.later growth⟩

/-- Successful operator closure preserves the same carriers while the outer
pass moves on to coercions. Its body is only unfolded in this proof premise. -/
theorem operator_accepted_with_visit {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {before after : Plan} {budget : Nat}
    (accepted : (do
  let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then
    pure before
  else
    let ownedNode := {
      node with
      type := node.rawType
      requirements
      coercions := []
    }
    let selection ← match ownedNode.form with
      | .unary operator _ =>
          SourceCompilationPlan.checkedUnaryOperatorMethod program caller ownedNode available
            operator
      | .binary _ operator _ =>
          SourceCompilationPlan.checkedBinaryOperatorMethod program caller ownedNode available
            operator
      | _ => throw (.unsupportedRequirements requirements)
    let arguments ← match ownedNode.form with
      | .unary _ operand => pure [operand]
      | .binary left _ right => pure [left, right]
      | _ => throw (.unsupportedRequirements requirements)
    SourceCompilationPlan.validateStagedCallBoundary caller ownedNode arguments
      selection.method.specialized
    discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller ownedNode
      selection
    let outerEdge : SourceSpecializationWorklist.CallEdge := {
      caller := caller.key
      occurrence := node.id
      callee := selection.method.specialized.key
    }
    let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
        before selection.method.specialized outerEdge budget with
      | .ok outcome => pure outcome
      | .error error => throw (.operatorMethodWorklist caller.key node.id
          error)
    match outcome with
    | .complete extended => pure extended
    | .budgetExhausted _ next pending =>
        throw (.operatorMethodSpecializationBudgetExhausted caller.key
          node.id next pending.length)

      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) :
    Extends before after ∧ OperatorCovered program caller available node after := by
  cases owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => simp only [owned, bind, Except.bind, pure, Except.pure] at accepted; cases accepted
  | some requirements =>
    simp only [owned] at accepted
    obtain ⟨actualRequirements, sameRequirements, accepted⟩ := bind_ok accepted
    have sameRequirements : actualRequirements = requirements := (Except.ok.inj sameRequirements).symm
    subst actualRequirements
    cases requirements with
    | nil =>
      simp only [List.isEmpty_nil, ite_true, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      refine ⟨.refl _, ?_⟩
      intro requirements selected nonempty _
      have same := Option.some.inj (selected.symm.trans owned)
      exact False.elim (nonempty same)
    | cons primary remaining =>
      try simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at accepted
      cases form : node.form <;> simp only [form] at accepted <;> try cases accepted
      all_goals
        obtain ⟨selection, selected, accepted⟩ := bind_ok accepted
        obtain ⟨arguments, argumentsSelected, accepted⟩ := bind_ok accepted
        obtain ⟨returned, staged, accepted⟩ := bind_ok accepted
        cases returned
        obtain ⟨returned, materialized, accepted⟩ := bind_ok accepted
        cases returned
        have materialized : ∃ dictionary, SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
            (operatorOwnedNode node (primary :: remaining)) selection = .ok dictionary := by
          have materializedOwned : (discard (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
              (operatorOwnedNode node (primary :: remaining)) selection) : Except SourceTypedRuntime.RuntimeError PUnit) = .ok PUnit.unit := by
            simpa only [operatorOwnedNode, form] using materialized
          cases result : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
              (operatorOwnedNode node (primary :: remaining)) selection with
          | error error => rw [result] at materializedOwned; cases materializedOwned
          | ok dictionary => exact ⟨dictionary, rfl⟩
        obtain ⟨dictionary, materialized⟩ := materialized
        cases extended : extendCompletePlan program before selection.method.specialized
            ⟨caller.key, node.id, selection.method.specialized.key⟩ budget with
        | error error => rw [extended] at accepted; cases accepted
        | ok outcome =>
          rw [extended] at accepted
          cases outcome with
          | budgetExhausted plan next pending => cases accepted
          | complete inserted =>
            cases accepted
            refine ⟨extend extended, ?_⟩
            intro _ _ _ _
            refine ⟨{
              requirements := primary :: remaining, owned := owned, nonempty := List.cons_ne_nil _ _
              selection := selection, arguments := arguments, dictionary := dictionary
              before := before, inserted := after, budget := budget
              selected := ?_, argumentsSelected := ?_, staged := ?_, materialized := materialized
              extended := extended, finalSelected := CallableCoercionPlanProvenance.complete_root extended }⟩
            · simpa only [operatorOwnedNode, form] using selected
            · simpa only [operatorOwnedNode, form] using argumentsSelected
            · simpa only [operatorOwnedNode, form] using staged

/-- Successful operator closure preserves the same carriers while the outer
pass moves on to coercions. Its body is only unfolded in this proof premise. -/
theorem operator_accepted {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode}
    {before after : Plan} {budget : Nat}
    (accepted : (do
  let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  if requirements.isEmpty then
    pure before
  else
    let ownedNode := {
      node with
      type := node.rawType
      requirements
      coercions := []
    }
    let selection ← match ownedNode.form with
      | .unary operator _ =>
          SourceCompilationPlan.checkedUnaryOperatorMethod program caller ownedNode available
            operator
      | .binary _ operator _ =>
          SourceCompilationPlan.checkedBinaryOperatorMethod program caller ownedNode available
            operator
      | _ => throw (.unsupportedRequirements requirements)
    let arguments ← match ownedNode.form with
      | .unary _ operand => pure [operand]
      | .binary left _ right => pure [left, right]
      | _ => throw (.unsupportedRequirements requirements)
    SourceCompilationPlan.validateStagedCallBoundary caller ownedNode arguments
      selection.method.specialized
    discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller ownedNode
      selection
    let outerEdge : SourceSpecializationWorklist.CallEdge := {
      caller := caller.key
      occurrence := node.id
      callee := selection.method.specialized.key
    }
    let outcome ← match SourceSpecializationWorklist.extendCompletePlan program
        before selection.method.specialized outerEdge budget with
      | .ok outcome => pure outcome
      | .error error => throw (.operatorMethodWorklist caller.key node.id
          error)
    match outcome with
    | .complete extended => pure extended
    | .budgetExhausted _ next pending =>
        throw (.operatorMethodSpecializationBudgetExhausted caller.key
          node.id next pending.length)

      : Except SourceTypedRuntime.RuntimeError Plan) = .ok after) : Extends before after :=
  (operator_accepted_with_visit accepted).1

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparationSteps
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
/-! Successful executable-plan preparation supplies actual coercion visits for
all returned carriers, including detached methods and helpers appended during
the scan. Source-view alignment, installed closures and source call execution
remain separate. Fresh trait headers still require their independent origin
profile when an AssembledFrom judgment is requested. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
open Frontend SourceInference SourceSpecializationWorklist CallableCoercionPreparationSteps

/-- Both lists are traversed by the actual preparation pass; this describes
only the indirect-call argument phase, following the output phase. -/
def argumentSteps (node : ExpressionNode) : List CoercionStep :=
  match node.form with
  | .call _ _ (.indirect metadata) => metadata.argumentCoercions
  | _ => []

def NodeCovered (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (plan : Plan) : Prop :=
  ∀ step ∈ node.coercions ++ argumentSteps node, Nonempty (Visit program caller available node step plan)

def Covered (program : CheckedProgram) (caller : Specialized) (plan : Plan) : Prop :=
  ∃ available, SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
    ∀ node, .expression node ∈ caller.function.typedBody.nodes → NodeCovered program caller available node plan

theorem NodeCovered.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (covered : NodeCovered program caller available node before) (growth : Extends before after) :
    NodeCovered program caller available node after := by
  intro step member
  obtain ⟨visit⟩ := covered step member
  exact ⟨visit.later growth⟩

theorem Covered.later {program : CheckedProgram} {caller : Specialized} {before after : Plan}
    (covered : Covered program caller before) (growth : Extends before after) : Covered program caller after := by
  obtain ⟨available, resolved, covered⟩ := covered
  exact ⟨available, resolved, fun node member => (covered node member).later growth⟩

private theorem ended {entries : List Specialized} {next index : Nat} {caller : Specialized}
    (done : entries[next]? = none) (bound : next ≤ index) (found : entries[index]? = some caller) : False := by
  have size := List.getElem?_eq_none_iff.mp done
  have position := (List.getElem?_eq_some_iff.mp found).1
  omega

/-- Actual operator visits are retained alongside every original coercion visit. -/
def NodeCoveredWith (program : CheckedProgram) (caller : Specialized)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) (node : ExpressionNode) (plan : Plan) : Prop :=
  NodeCovered program caller available node plan ∧ OperatorCovered program caller available node plan

def CoveredWith (program : CheckedProgram) (caller : Specialized) (plan : Plan) : Prop :=
  ∃ available, SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
    ∀ node, .expression node ∈ caller.function.typedBody.nodes → NodeCoveredWith program caller available node plan

theorem NodeCoveredWith.later {program : CheckedProgram} {caller : Specialized}
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment} {node : ExpressionNode} {before after : Plan}
    (covered : NodeCoveredWith program caller available node before) (growth : Extends before after) :
    NodeCoveredWith program caller available node after :=
  ⟨covered.1.later growth, covered.2.later growth⟩

theorem CoveredWith.later {program : CheckedProgram} {caller : Specialized} {before after : Plan}
    (covered : CoveredWith program caller before) (growth : Extends before after) : CoveredWith program caller after := by
  obtain ⟨available, resolved, covered⟩ := covered
  exact ⟨available, resolved, fun node member => (covered node member).later growth⟩

theorem CoveredWith.coercions {program : CheckedProgram} {caller : Specialized} {plan : Plan}
    (covered : CoveredWith program caller plan) : Covered program caller plan := by
  obtain ⟨available, resolved, covered⟩ := covered
  exact ⟨available, resolved, fun node member => (covered node member).1⟩

/-- The strengthened index invariant covers every returned position at or
beyond `next`. Exact prefix growth makes newly appended methods part of this
same actual traversal. -/
theorem aux_with {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    Extends before after ∧ ∀ index caller, next ≤ index → after.specializations[index]? = some caller → CoveredWith program caller after := by
  induction fuel generalizing next before after with
  | zero =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i done
      cases accepted
      exact ⟨.refl _, fun _ _ bound found => False.elim (ended done bound found)⟩
    · cases accepted
  | succ fuel ih =>
    unfold SourceCompilationPlan.prepareExecutablePlanEvidenceAux at accepted
    split at accepted
    · rename_i done
      cases accepted
      exact ⟨.refl _, fun _ _ bound found => False.elim (ended done bound found)⟩
    · rename_i caller found
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨extended, scan, rest⟩ := bind_ok accepted
      obtain ⟨available, resolved, scan⟩ := bind_ok scan
      obtain ⟨loopFinal, loop, returned⟩ := bind_ok scan
      cases returned
      have scanned : Extends before extended ∧ CoveredWith program caller extended := by
        have result := forIn_coverage
          (done := fun (item : Node) (final : Plan) => ∀ (node : ExpressionNode), item = .expression node → NodeCoveredWith program caller available node final)
          loop (by
            intro item previous final growth done node same
            exact (done node same).later growth) ?_
        · exact ⟨result.1, available, resolved, fun node member => result.2 _ member node rfl⟩
        intro item member current outcome nodeAccepted
        cases item with
        | statement statement =>
          cases nodeAccepted
          exact ⟨current, rfl, .refl _, fun _ same => by cases same⟩
        | expression node =>
          suffices ∃ final, outcome = .yield final ∧ Extends current final ∧ NodeCoveredWith program caller available node final by
            obtain ⟨final, same, growth, covered⟩ := this
            exact ⟨final, same, growth, fun other same => by cases same; exact covered⟩
          cases form : node.form <;> simp only [form] at nodeAccepted
          case' call callee arguments resolution => cases resolution
          case' reference name resolution => cases resolution
          all_goals
            first
            | (obtain ⟨opPlan, opAccepted, nodeAccepted⟩ := bind_ok nodeAccepted
               have operatorReceipt := operator_accepted_with_visit opAccepted
               have opGrowth := operatorReceipt.1
               have opCovered := operatorReceipt.2)
            | (let opPlan := current
               have opGrowth : Extends current opPlan := .refl _
               have opCovered : OperatorCovered program caller available node opPlan := by
                 intro _ _ _ impossible
                 simp only [OperatorForm, form] at impossible)
          all_goals
            obtain ⟨outputPlan, outputLoop, nodeAccepted⟩ := bind_ok nodeAccepted
            have outputCovered := forIn_coverage
              (done := fun step final => Nonempty (Visit program caller available node step final)) outputLoop
              (fun _ _ _ growth ⟨visit⟩ => ⟨visit.later growth⟩) (by
                intro step _ previous outcome accepted
                obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                cases returned
                have head := coercion_accepted headAccepted
                exact ⟨_, rfl, head.1, head.2⟩)
          all_goals try rw [form] at nodeAccepted
          all_goals try dsimp only at nodeAccepted
          all_goals
            iterate 8 all_goals first
              | (have empty : argumentSteps node = [] := by simp only [argumentSteps, form]
                 exact ⟨outputPlan, (Except.ok.inj nodeAccepted).symm, opGrowth.trans outputCovered.1,
                   (by simpa only [NodeCovered, empty, List.append_nil] using outputCovered.2),
                   opCovered.later outputCovered.1⟩)
              | (obtain ⟨argumentPlan, argumentLoop, nodeAccepted⟩ := bind_ok nodeAccepted
                 have argumentCovered := forIn_coverage
                   (done := fun step final => Nonempty (Visit program caller available node step final)) argumentLoop
                   (fun _ _ _ growth ⟨visit⟩ => ⟨visit.later growth⟩) (by
                     intro step _ previous outcome accepted
                     obtain ⟨updated, headAccepted, returned⟩ := bind_ok accepted
                     cases returned
                     have head := coercion_accepted headAccepted
                     exact ⟨_, rfl, head.1, head.2⟩)
                 refine ⟨argumentPlan, (Except.ok.inj nodeAccepted).symm,
                   opGrowth.trans (outputCovered.1.trans argumentCovered.1), ?_,
                   opCovered.later (outputCovered.1.trans argumentCovered.1)⟩
                 intro step member
                 rcases List.mem_append.mp member with member | member
                 · obtain ⟨visit⟩ := outputCovered.2 step member
                   exact ⟨visit.later argumentCovered.1⟩
                 · apply argumentCovered.2 step
                   simpa only [argumentSteps, form] using member)
              | (obtain ⟨_, _, nodeAccepted⟩ := bind_ok nodeAccepted)
              | split at nodeAccepted
              | contradiction
      obtain ⟨tailGrowth, tailCovered⟩ := ih rest
      refine ⟨scanned.1.trans tailGrowth, ?_⟩
      intro index selected bound lookup
      by_cases same : index = next
      · subst index
        have atNext := (scanned.1.trans tailGrowth).at found
        have same := Option.some.inj (lookup.symm.trans atNext)
        subst selected
        exact scanned.2.later tailGrowth
      · exact tailCovered index selected (by omega) lookup

/-- Public preparation success inspects every final carrier, including those
that were absent from the original input vector. -/
theorem of_accepted_with {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after) :
    Extends before after ∧ ∀ caller ∈ after.specializations, CoveredWith program caller after := by
  obtain ⟨prepared, inspected, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, returned⟩ := bind_ok accepted
  cases returned
  obtain ⟨growth, covered⟩ := aux_with inspected
  refine ⟨growth, ?_⟩
  intro caller member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact covered index caller (Nat.zero_le _) found

/-- Legacy coercion coverage projects the same preparation traversal. -/
theorem aux {program : CheckedProgram} {budget fuel next : Nat} {before after : Plan}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceAux program budget fuel next before = .ok after) :
    Extends before after ∧ ∀ index caller, next ≤ index → after.specializations[index]? = some caller → Covered program caller after := by
  obtain ⟨growth, covered⟩ := aux_with accepted
  exact ⟨growth, fun index caller bound found => (covered index caller bound found).coercions⟩

theorem of_accepted {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after) :
    Extends before after ∧ ∀ caller ∈ after.specializations, Covered program caller after := by
  obtain ⟨growth, covered⟩ := of_accepted_with accepted
  exact ⟨growth, fun caller member => (covered caller member).coercions⟩

/-- The returned plan retains the original operator selection and full row,
including operators in helpers appended during this same actual scan. -/
theorem operator_visit {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (form : OperatorForm node) {requirements : List RequirementId}
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) (nonempty : requirements ≠ [])
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available) :
    Nonempty (OperatorVisit program caller available node after) := by
  obtain ⟨actual, actualResolved, covered⟩ := (of_accepted_with accepted).2 caller member
  have same := Except.ok.inj (actualResolved.symm.trans resolved)
  subst actual
  exact (covered node nodeMember).2 requirements owned nonempty form

/-- A supplied emitter dictionary must be the actual caller resolver result.
The full node and step position remain tied to that same final caller. -/
theorem visit {program : CheckedProgram} {before after : Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok after)
    {caller : Specialized} (member : caller ∈ after.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available) :
    Nonempty (Visit program caller available node coercion after) := by
  obtain ⟨actual, actualResolved, covered⟩ := (of_accepted accepted).2 caller member
  have same := Except.ok.inj (actualResolved.symm.trans resolved)
  subst actual
  exact covered node nodeMember coercion site

private theorem call_key {plan : Plan} {caller target selected : SourceSpecialization.SpecializationKey} {id : ExpressionId}
    (accepted : SourceCompilationPlan.exactCallKey plan caller id target = .ok selected) : selected = target := by
  unfold SourceCompilationPlan.exactCallKey at accepted
  split at accepted <;> try contradiction
  rename_i edge edges
  cases accepted
  have member : edge ∈ plan.callEdges.filter (fun edge => decide (edge.caller = caller) && decide (edge.occurrence = id) && decide (edge.callee = target)) := by rw [edges]; simp
  have same := (List.mem_filter.mp member).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at same
  exact same.2

/-- The exact edge is the same action used by the actual emitter. -/
theorem exact_call_key {plan : Plan} {caller target selected : SourceSpecialization.SpecializationKey} {id : ExpressionId}
    (accepted : SourceCompilationPlan.exactCallKey plan caller id target = .ok selected) : selected = target :=
  call_key accepted

/-- The outer preparation supplies the former per-method extension premise.
Both selectors are compared as the same action on complete caller/node data. -/
theorem step_specialized {program : CheckedProgram} {before : Plan} {fuel budget : Nat}
    {project : CallableCoercionSpine.Projector} {context : CallableCoercionSpine.Context}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before fuel budget = .ok context.plan)
    {caller : Specialized} (member : caller ∈ context.plan.specializations)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ argumentSteps node)
    {available : CallableCoercionSpine.RuntimeEvidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {scope : CallableCoercionSpine.Scope} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : CallableCoercionSpine.Lowered} {call : CallableCoercionSpine.Call}
    (step : CallableCoercionSpine.Step program project context caller available scope node policy input coercion output call) :
    step.specialized = step.method.specialized := by
  obtain ⟨receipt⟩ := visit accepted member nodeMember site resolved
  have sameMethod := Except.ok.inj (receipt.selected.symm.trans step.selectedMethod)
  have retained := receipt.finalSelected
  rw [sameMethod] at retained
  have emitted := step.selected
  rw [call_key step.edge] at emitted
  exact Except.ok.inj (emitted.symm.trans retained)

end Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation
/-! Finite native execution of the actual ordered coercion calls. Saved closure
code and captures are observed from the store, without identifying them with a
source method body. Source coercion judgments need that separate connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
open Core Frontend CoreProof

/-- A native call either propagates an earlier failure, reads an absent global,
or enters the exact stored closure. Sum tags and closure annotations remain the
actual values; no typing premise is silently inferred from a compiler row. -/
inductive Invoke (environment : Environment) (reason : Word) (call : Call) :
    Store → Value → Value → Store → Prop where
  | skipped {store : Store} {tag : Ty} {payload : Value} :
      Invoke environment reason call store (.inLeft tag payload)
        (.inLeft call.signature.resultType payload) store
  | absent {store : Store} {tag cellType absentTag : Ty} {argument absentPayload : Value}
      {location : Location}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : store.read? location = some (.inLeft absentTag absentPayload)) :
      Invoke environment reason call store (.inRight tag argument)
        (.inLeft call.signature.resultType (.word reason)) store
  | applied {before after : Store} {tag cellType storedTag parameter result : Ty}
      {argument value : Value} {location : Location} {body : Expr} {captured : Environment}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : before.read? location = some (.inRight storedTag (.closure parameter result body captured)))
      (bodyEvaluation : Evaluates (argument :: captured) before body value after) :
      Invoke environment reason call before (.inRight tag argument) value after

inductive Runs (environment : Environment) (reason : Word) :
    Store → Value → List Call → Value → Store → Prop where
  | nil {store : Store} {value : Value} : Runs environment reason store value [] value store
  | cons {before middle after : Store} {input result value : Value} {call : Call} {calls : List Call}
      (head : Invoke environment reason call before input result middle)
      (tail : Runs environment reason middle result calls value after) :
      Runs environment reason before input (call :: calls) value after

/-- Ordered native calls can retain additional receipts for each actual
invocation without changing the intermediate stores or call order. -/
inductive RunsFor (invocation : Call → Store → Value → Value → Store → Prop) :
    Store → Value → List Call → Value → Store → Prop where
  | nil {store : Store} {value : Value} : RunsFor invocation store value [] value store
  | cons {before middle after : Store} {input result value : Value} {call : Call} {calls : List Call}
      (head : invocation call before input result middle)
      (tail : RunsFor invocation middle result calls value after) :
      RunsFor invocation before input (call :: calls) value after

theorem RunsFor.map {invocation target : Call → Store → Value → Value → Store → Prop}
    (transform : ∀ {call before input result after}, invocation call before input result after →
      target call before input result after)
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor invocation before input calls value after) :
    RunsFor target before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons (transform head) ih

theorem Runs.toFor {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : Runs environment reason before input calls value after) :
    RunsFor (Invoke environment reason) before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

theorem RunsFor.toRuns {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor (Invoke environment reason) before input calls value after) :
    Runs environment reason before input calls value after := by
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

/-- Applied calls retain the body child of the original native completion.
The actual closure annotations, code, captures and cell observation remain. -/
inductive InvokeSized (budget : Nat) (environment : Environment) (reason : Word) (call : Call) :
    Store → Value → Value → Store → Prop where
  | skipped {store : Store} {tag : Ty} {payload : Value} :
      InvokeSized budget environment reason call store (.inLeft tag payload)
        (.inLeft call.signature.resultType payload) store
  | absent {store : Store} {tag cellType absentTag : Ty} {argument absentPayload : Value}
      {location : Location}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : store.read? location = some (.inLeft absentTag absentPayload)) :
      InvokeSized budget environment reason call store (.inRight tag argument)
        (.inLeft call.signature.resultType (.word reason)) store
  | applied {before after : Store} {tag cellType storedTag parameter result : Ty}
      {argument value : Value} {location : Location} {body : Expr} {captured : Environment} {bodySize : Nat}
      (reference : environment[call.index]? = some (.cellRef cellType location))
      (read : before.read? location = some (.inRight storedTag (.closure parameter result body captured)))
      (bodyEvaluation : EvaluationSize bodySize (argument :: captured) before body value after)
      (smaller : bodySize < budget) :
      InvokeSized budget environment reason call before (.inRight tag argument) value after

theorem InvokeSized.mono {budget larger : Nat} {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {input value : Value}
    (invoked : InvokeSized budget environment reason call before input value after)
    (bound : budget ≤ larger) : InvokeSized larger environment reason call before input value after := by
  cases invoked with
  | skipped => exact .skipped
  | absent reference read => exact .absent reference read
  | applied reference read evaluated smaller =>
    exact .applied reference read evaluated (Nat.lt_of_lt_of_le smaller bound)

theorem InvokeSized.forget {budget : Nat} {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {input value : Value}
    (invoked : InvokeSized budget environment reason call before input value after) :
    Invoke environment reason call before input value after := by
  cases invoked with
  | skipped => exact .skipped
  | absent reference read => exact .absent reference read
  | applied reference read evaluated _ => exact .applied reference read evaluated.sound

theorem RunsFor.forget {invocation : Call → Store → Value → Value → Store → Prop}
    {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor invocation before input calls value after)
    (forgetInvocation : ∀ {call before input result after}, invocation call before input result after →
      Invoke environment reason call before input result after) :
    Runs environment reason before input calls value after :=
  (runs.map forgetInvocation).toRuns

theorem RunsFor.mono {budget larger : Nat} {environment : Environment} {reason : Word}
    {before after : Store} {input value : Value} {calls : List Call}
    (runs : RunsFor (InvokeSized budget environment reason) before input calls value after)
    (bound : budget ≤ larger) :
    RunsFor (InvokeSized larger environment reason) before input calls value after :=
  runs.map (fun invoked => invoked.mono bound)


theorem Invoke.evaluates {environment : Environment} {reason : Word} {call : Call}
    {before middle after : Store} {input value : Value} {arguments : Expr}
    (argumentsEvaluation : Evaluates environment before arguments input middle)
    (invoked : Invoke environment reason call middle input value after) :
    Evaluates environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after := by
  cases invoked with
  | skipped => exact .caseLeft argumentsEvaluation (.inLeft (.var rfl))
  | absent reference read =>
    exact .caseRight argumentsEvaluation (.caseLeft
      (.caseLeft (.loadCell (.var (by simpa using reference)) read) (.inLeft .word))
      (.inLeft (.var rfl)))
  | applied reference read bodyEvaluation =>
    exact .caseRight argumentsEvaluation (.caseRight
      (.caseRight (.loadCell (.var (by simpa using reference)) read) (.inRight (.var rfl)))
      (.apply (.var rfl) (.var rfl) bodyEvaluation))

/-- Completion itself supplies the argument trace, actual cell observation and
saved-body trace. It cannot supply source method authenticity. -/
theorem call_complete_sized {environment : Environment} {reason : Word} {call : Call}
    {size : Nat} {before after : Store} {value : Value} {arguments : Expr}
    (completed : EvaluationSize size environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after) :
    ∃ argumentSize input middle, argumentSize < size ∧
      EvaluationSize argumentSize environment before arguments input middle ∧
      InvokeSized size environment reason call middle input value after := by
  cases completed with
  | caseLeft argument branch =>
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst_vars
        exact ⟨_, _, _, by omega, argument, .skipped⟩
  | caseRight argument branch =>
    cases branch with
    | caseLeft loaded branch =>
      cases loaded with
      | caseLeft loaded absent =>
        cases loaded with
        | loadCell reference read =>
          cases reference with
          | var reference =>
            cases absent with
            | inLeft reasonValue =>
              cases reasonValue
              cases branch with
              | inLeft payload =>
                cases payload with
                | var found =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                  subst_vars
                  exact ⟨_, _, _, by omega, argument, .absent (by simpa using reference) read⟩
      | caseRight loaded present => cases present
    | caseRight loaded branch =>
      cases loaded with
      | caseLeft loaded absent => cases absent
      | caseRight loaded present =>
        cases loaded with
        | loadCell reference read =>
          cases reference with
          | var reference =>
            cases present with
            | inRight payload =>
              cases payload with
              | var found =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst_vars
                cases branch with
                | apply function argumentValue body =>
                  cases function with
                  | var functionFound =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at functionFound
                    subst_vars
                    cases argumentValue with
                    | var argumentFound =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                        Option.some.injEq] at argumentFound
                      subst_vars
                      exact ⟨_, _, _, by omega, argument, .applied (by simpa using reference) read body (by omega)⟩

theorem call_complete {environment : Environment} {reason : Word} {call : Call}
    {before after : Store} {value : Value} {arguments : Expr}
    (completed : Evaluates environment before (SourceCoreCalls.call call.signature call.index arguments reason) value after) :
    ∃ input middle, Evaluates environment before arguments input middle ∧
      Invoke environment reason call middle input value after := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  obtain ⟨_, input, middle, _, argumentsEvaluation, invoked⟩ := call_complete_sized sized
  exact ⟨input, middle, argumentsEvaluation.sound, invoked.forget⟩

/-- Each body bound is inherited from its original call child. The initial
operand keeps its original size; it is strict exactly when a call is present. -/
theorem emit_complete_sized {environment : Environment} {reason : Word} {calls : List Call}
    {size : Nat} {before after : Store} {input : Expr} {value : Value}
    (completed : EvaluationSize size environment before (emit reason input calls) value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before input initial middle ∧
      RunsFor (InvokeSized size environment reason) middle initial calls value after := by
  induction calls generalizing input size with
  | nil => exact ⟨size, _, _, Nat.le_refl _, by simp, completed, .nil⟩
  | cons call calls ih =>
    obtain ⟨callSize, result, reached, callBound, _, head, tail⟩ := ih completed
    obtain ⟨child, initial, middle, childLess, first, invoked⟩ := call_complete_sized head
    have smaller := Nat.lt_of_lt_of_le childLess callBound
    exact ⟨child, initial, middle, Nat.le_of_lt smaller, fun _ => smaller,
      first, .cons (invoked.mono callBound) tail⟩

/-- Forward native execution follows the retained ordered call trace. -/
theorem Runs.evaluates {environment : Environment} {reason : Word} {calls : List Call}
    {before middle after : Store} {input : Expr} {initial value : Value}
    (runs : Runs environment reason middle initial calls value after)
    (first : Evaluates environment before input initial middle) :
    Evaluates environment before (emit reason input calls) value after := by
  induction runs generalizing input before with
  | nil => exact first
  | cons head _ ih => exact ih (head.evaluates first)

theorem emit_evaluates_iff {environment : Environment} {reason : Word} {calls : List Call}
    {before after : Store} {input : Expr} {value : Value} :
    Evaluates environment before (emit reason input calls) value after ↔
      ∃ initial middle, Evaluates environment before input initial middle ∧
        Runs environment reason middle initial calls value after := by
  constructor
  · intro completed
    obtain ⟨size, sized⟩ := evaluation_has_size completed
    obtain ⟨_, initial, middle, _, _, first, runs⟩ := emit_complete_sized sized
    exact ⟨initial, middle, first.sound, runs.forget InvokeSized.forget⟩
  · rintro ⟨_, _, first, runs⟩
    exact runs.evaluates first

/-- Syntax renaming moves the selected caller slot and input expression. It
never renames an already captured closure value. -/
theorem call_rename (call : Call) (arguments : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCalls.call call.signature call.index arguments reason).rename ξ =
      SourceCoreCalls.call call.signature (ξ call.index) (arguments.rename ξ) reason := by
  simp [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

def Call.rename (ξ : Renaming) (call : Call) : Call := {call with index := ξ call.index}

theorem emit_rename (reason : Word) (input : Expr) (calls : List Call) (ξ : Renaming) :
    (emit reason input calls).rename ξ =
      emit reason (input.rename ξ) (calls.map (Call.rename ξ)) := by
  induction calls generalizing input with
  | nil => rfl
  | cons call calls ih => simp only [emit, List.map_cons, ih, call_rename, Call.rename]

def finalType (input : Ty) : List Call → Ty
  | [] => input
  | call :: calls => finalType call.signature.resultType calls

theorem Runs.failure (environment : Environment) (reason : Word) (store : Store)
    (tag : Ty) (payload : Value) (calls : List Call) :
    Runs environment reason store (.inLeft tag payload) calls
      (.inLeft (finalType tag calls) payload) store := by
  induction calls generalizing tag with
  | nil => exact .nil
  | cons call calls ih => exact .cons .skipped (ih call.signature.resultType)

theorem failure_suffix {environment : Environment} {reason : Word} {before after : Store}
    {input : Expr} {tag : Ty} {payload : Value} (calls : List Call)
    (failed : Evaluates environment before input (.inLeft tag payload) after) :
    Evaluates environment before (emit reason input calls)
      (.inLeft (finalType tag calls) payload) after :=
  emit_evaluates_iff.mpr ⟨_, _, failed, Runs.failure environment reason after tag payload calls⟩

theorem failure_store {environment : Environment} {reason : Word} {before reached after : Store}
    {input : Expr} {tag : Ty} {payload value : Value} {calls : List Call}
    (failed : Evaluates environment before input (.inLeft tag payload) reached)
    (completed : Evaluates environment before (emit reason input calls) value after) :
    value = .inLeft (finalType tag calls) payload ∧ after = reached :=
  evaluation_deterministic completed (failure_suffix calls failed)


theorem Spine.final_type {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls) :
    finalType input.type calls = output.type := by
  induction receipt with
  | nil => rfl
  | cons head _ ih => simpa only [head.emitted, finalType] using ih

/-- The actual emitted spine keeps the operand child and every stored-body
child below the same original native budget. Source grades are independent. -/
theorem Spine.completed_sized {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {size : Nat} {environment : Environment} {before after : Store} {value : Value}
    (completed : EvaluationSize size environment before output.expression value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before input.expression initial middle ∧
      RunsFor (InvokeSized size environment context.internalReason) middle initial calls value after := by
  rw [receipt.code] at completed
  exact emit_complete_sized completed

/-- Renaming changes only the caller lookups. Actual stored closure captures
and body subderivations stay in the original native completion. -/
theorem Spine.renamed_completed_sized {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    (ξ : Renaming) {size : Nat} {environment : Environment} {before after : Store} {value : Value}
    (completed : EvaluationSize size environment before (output.expression.rename ξ) value after) :
    ∃ child initial middle, child ≤ size ∧ (calls ≠ [] → child < size) ∧
      EvaluationSize child environment before (input.expression.rename ξ) initial middle ∧
      RunsFor (InvokeSized size environment context.internalReason) middle initial (calls.map (Call.rename ξ)) value after := by
  rw [receipt.code, emit_rename] at completed
  obtain ⟨child, initial, middle, inclusive, strict, operand, runs⟩ := emit_complete_sized completed
  exact ⟨child, initial, middle, inclusive, fun nonempty => strict (by simpa using nonempty), operand, runs⟩

/-- Actual compiler success and finite completion determine the ordered native
trace. This includes absent globals and failures returned by actual bodies. -/
theorem Spine.completed_iff {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {environment : Environment} {before after : Store} {value : Value} :
    Evaluates environment before output.expression value after ↔
      ∃ initial middle, Evaluates environment before input.expression initial middle ∧
        Runs environment context.internalReason middle initial calls value after := by
  rw [receipt.code]
  exact emit_evaluates_iff

/-- Hidden temporary slots are handled by renaming the real emitted code. The
native trace observes closures in that actual environment without modifying
stored captures. -/
theorem Spine.renamed_completed_iff {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    (ξ : Renaming) {environment : Environment} {before after : Store} {value : Value} :
    Evaluates environment before (output.expression.rename ξ) value after ↔
      ∃ initial middle, Evaluates environment before (input.expression.rename ξ) initial middle ∧
        Runs environment context.internalReason middle initial (calls.map (Call.rename ξ)) value after := by
  rw [receipt.code, emit_rename]
  exact emit_evaluates_iff

/-- An earlier language failure skips every method, even if those globals are
absent. The final result has the compiler's actual output tag and exact store. -/
theorem Spine.input_failure {program : CheckedProgram} {project : Projector} {context : Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope}
    {node : SourceInference.ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy}
    {input output : Lowered} {steps : List SourceInference.CoercionStep} {calls : List Call}
    (receipt : Spine program project context caller available scope node policy input steps output calls)
    {environment : Environment} {before after : Store} {payload : Value}
    (failed : Evaluates environment before input.expression (.inLeft input.type payload) after) :
    Evaluates environment before output.expression (.inLeft output.type payload) after := by
  rw [receipt.code, ← receipt.final_type]
  exact failure_suffix calls failed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSpine
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable
/-! Source parameter and result shapes are checked on each actual selected
coercion method in the finite final compilation plan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable
open Core Frontend SourceInference

structure Shape (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) : Prop where
  parameters : method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [step.source]
  result : method.specialized.function.inferredBodyType = step.target

def validateShape (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) : Option (PLift (Shape step method)) :=
  if parameters : method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [step.source] then
    if result : method.specialized.function.inferredBodyType = step.target then some ⟨⟨parameters,result⟩⟩
    else none
  else none

def StepReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep) : Prop :=
  ∀ available method,
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available →
    SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method → Shape step method

def validateStep (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep) : Option (PLift (StepReady program caller node step)) :=
  match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
  | .error _ => some ⟨by
      intro available method actual _selected
      rw [resolved] at actual
      cases actual⟩
  | .ok available =>
      match selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step with
      | .error _ => some ⟨by
          intro actualAvailable method actualResolved actualSelected
          have same := Except.ok.inj (resolved.symm.trans actualResolved)
          subst actualAvailable
          rw [selected] at actualSelected
          cases actualSelected⟩
      | .ok method => do
          let ⟨shape⟩ ← validateShape step method
          return ⟨by
            intro actualAvailable actualMethod actualResolved actualSelected
            have same := Except.ok.inj (resolved.symm.trans actualResolved)
            subst actualAvailable
            have same := Except.ok.inj (selected.symm.trans actualSelected)
            subst actualMethod
            exact shape⟩

private def validateSteps (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : (steps : List CoercionStep) →
    Option (PLift (∀ step ∈ steps, StepReady program caller node step))
  | [] => some ⟨by intro step member; cases member⟩
  | step :: steps => do
      let ⟨head⟩ ← validateStep program caller node step
      let ⟨tail⟩ ← validateSteps program caller node steps
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def NodeReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Prop :=
  ∀ step ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node, StepReady program caller node step

def expressions (caller : SourceSpecialization.SpecializedFunction) : List ExpressionNode :=
  caller.function.typedBody.nodes.filterMap fun
    | .expression node => some node
    | _ => none

private def validateNodes (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction) :
    (nodes : List ExpressionNode) → Option (PLift (∀ node ∈ nodes, NodeReady program caller node))
  | [] => some ⟨by intro node member; cases member⟩
  | node :: nodes => do
      let ⟨head⟩ ← validateSteps program caller node (node.coercions ++ CallableCoercionPreparation.argumentSteps node)
      let ⟨tail⟩ ← validateNodes program caller nodes
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def Ready (program : CheckedProgram) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ caller ∈ rows, ∀ node ∈ expressions caller, NodeReady program caller node

def validate (program : CheckedProgram) : (rows : List SourceSpecialization.SpecializedFunction) →
    Option (PLift (Ready program rows))
  | [] => some ⟨by intro caller member; cases member⟩
  | caller :: rows => do
      let ⟨head⟩ ← validateNodes program caller (expressions caller)
      let ⟨tail⟩ ← validate program rows
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

theorem Ready.shape {program : CheckedProgram} {rows : List SourceSpecialization.SpecializedFunction}
    (ready : Ready program rows) {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ rows)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method) :
    Shape coercion method :=
  ready caller member node (List.mem_filterMap.mpr ⟨.expression node, nodeMember, rfl⟩)
    coercion site available method resolved selected

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable
end
