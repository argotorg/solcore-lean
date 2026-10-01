import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyCertificates
import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Frontend.SourceCoreCompatibleOutputs

/-! Static selection of cached named code and the actual nil-argument call
shape. Source declaration/evidence agreement and native installation are
separate obligations; no native closure type invents either of them. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapM_at {α β ε : Type} {f : α → Except ε β} {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM f = .ok outputs) {index : Nat} {input : α}
    (selected : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ f input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => simp at selected
  | cons head rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨remaining, generatedRest, accepted⟩ := bind_ok accepted
    cases accepted
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst input; exact ⟨first, rfl, generated⟩
    | succ index =>
      obtain ⟨output, position, compiled⟩ := ih generatedRest selected
      exact ⟨output, position, compiled⟩

/-- The actual installer shifts free global/capture slots while retaining the
lambda argument at index zero. The body theorem uses this lifted renaming. -/
def installationRenaming : Nat → Renaming
  | 0 => Renaming.id
  | index + 1 => Renaming.comp (Renaming.insertion 0) (installationRenaming index)

private theorem installation_index (count index : Nat) : installationRenaming count index = count + index := by
  induction count with
  | zero => simp [installationRenaming, Renaming.id]
  | succ count ih => simp [installationRenaming, Renaming.comp, Renaming.insertion, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem installation_argument (count : Nat) : (installationRenaming count).lift 0 = 0 := rfl

theorem installation_reference (count index : Nat) :
    (installationRenaming count).lift (index + 1) = count + index + 1 := by
  simp only [Renaming.lift, installation_index]

private theorem installed_rename (count : Nat) (expression : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count expression = expression.rename (installationRenaming count) := by
  induction count with
  | zero => simp [SourceCoreCompatibleOutputs.installedTemplate, installationRenaming, Expr.rename_id]
  | succ count ih =>
    unfold SourceCoreCompatibleOutputs.installedTemplate
    rw [List.range_succ, List.foldl_append]
    change (SourceCoreCompatibleOutputs.installedTemplate count expression).weakenAt 0 = _
    rw [ih, ← Expr.rename_insertion, Expr.rename_comp]
    rfl

/-- Exact saved body syntax after installation, including its real named-hook
administrative reference. This grants no closure/source authority by itself. -/
theorem installed_lambda (count : Nat) (parameter result : Ty) (body : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count (.lambda parameter result body) =
      .lambda parameter result (body.rename (installationRenaming count).lift) := by
  rw [installed_rename]
  rfl

/-- Real second-pass success selects the compiler equation for this exact
plan function and the cached code at the same slot. -/
theorem compiled_at {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : prepared.base.functions[index]? = some named) :
    ∃ diagnostics code,
      prepared.base.diagnostics = some diagnostics ∧
      prepared.secondPass.closures[index]? = some code ∧
      SourceCoreGeneralFunctions.compileClosureWithRepresentation prepared.base.sourceProgram
        (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
        prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
        (match prepared.base.callableContext with
          | none => diagnostics.program
          | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
        prepared.base.locals prepared.base.callableContext prepared.fuel named = .ok code := by
  have accepted := prepared.secondPass.compiled
  unfold SourceCoreCompatibleMarkedFunctions.compileClosures at accepted
  by_cases empty : prepared.base.functions.isEmpty = true
  · have absent := List.isEmpty_iff.mp empty
    rw [absent] at selected
    simp at selected
  · simp only [empty, Bool.false_eq_true, ↓reduceIte] at accepted
    cases diagnosticResult : prepared.base.diagnostics with
    | none => simp [diagnosticResult, bind, Except.bind] at accepted
    | some diagnostics =>
      simp only [diagnosticResult, bind, Except.bind, pure, Except.pure, Except.mapError] at accepted
      split at accepted
      · cases accepted
      · rename_i codes generated
        cases accepted
        obtain ⟨code, position, compiled⟩ := mapM_at generated selected
        exact ⟨diagnostics, code, rfl, position, compiled⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem zipIdx_selected {α : Type} {inputs : List α} {input : α} {index : Nat}
    (member : (input, index) ∈ inputs.zipIdx) : inputs[index]? = some input := by
  have facts := List.mem_zipIdx member
  simpa using (List.getElem?_eq_getElem (by simpa using facts.2.1)).trans (congrArg some facts.2.2.symm)

/-- The accepted action retains the canonical instantiation target, actual
plan edge, exact specialization and unique native global slot. These facts
come from the checks that ran; matching native types alone is insufficient. -/
theorem selected_signature_facts
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature)) :
    ∃ caller target specialized,
      source.owner = compilation.owner.declaration ∧
      SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller ∧
      caller.assumptions = [] ∧
      SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok target ∧
      (if isReference then SourceCompilationPlan.exactReferenceKey compilation.plan compilation.owner node.id target
        else SourceCompilationPlan.exactCallKey compilation.plan compilation.owner node.id target) = .ok signature.key ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      specialized.assumptions = [] ∧ compilation.globals[index]? = some signature := by
  unfold SourceCoreFunctions.selectedSignature at accepted
  by_cases owner : source.owner = compilation.owner.declaration
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    obtain ⟨caller, callerReceipt, accepted⟩ := bind_ok accepted
    have callerReceipt := mapError_ok callerReceipt
    split at accepted
    · obtain ⟨target, targetReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨key, edgeReceipt, accepted⟩ := bind_ok accepted
      obtain ⟨specialized, specializationReceipt, accepted⟩ := bind_ok accepted
      split at accepted
      · split at accepted
        · cases accepted
        · split at accepted
          all_goals simp only [pure, Except.pure, bind, Except.bind] at accepted
          all_goals try contradiction
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨selection, globalReceipt, accepted⟩ := bind_ok accepted
          rcases selection with ⟨selectedIndex, selectedSignature⟩
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          cases accepted
          change ((match compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
            | [] => .error (.callPreparation (.missingSpecialization key))
            | [(signature, index)] => .ok (index, signature)
            | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))) :
              Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) =
              .ok (selectedIndex, selectedSignature) at globalReceipt
          split at globalReceipt
          · cases globalReceipt
          · rename_i signature index filtered
            cases globalReceipt
            have member : (selectedSignature, selectedIndex) ∈ compilation.globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) := by
              rw [filtered]; exact .head _
            have facts := List.mem_filter.mp member
            have keyEq : selectedSignature.key = key := of_decide_eq_true facts.2
            refine ⟨caller, target, specialized, by simpa using owner, callerReceipt,
              List.isEmpty_iff.mp (by assumption), mapError_ok targetReceipt, ?_, ?_,
              List.isEmpty_iff.mp (by assumption), zipIdx_selected facts.1⟩
            · simpa only [keyEq] using mapError_ok edgeReceipt
            · simpa only [keyEq] using mapError_ok specializationReceipt
          · cases globalReceipt
      · cases accepted
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [owner, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

private theorem edge_target {plan : SourceSpecializationWorklist.Plan}
    {caller target selected : SourceSpecialization.SpecializationKey} {id : ExpressionId} {reference : Bool}
    (accepted : (if reference then SourceCompilationPlan.exactReferenceKey plan caller id target
      else SourceCompilationPlan.exactCallKey plan caller id target) = .ok selected) : selected = target := by
  cases reference <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
  all_goals
    first | unfold SourceCompilationPlan.exactCallKey at accepted
          | unfold SourceCompilationPlan.exactReferenceKey at accepted
    split at accepted
    · cases accepted
    · rename_i edge filtered
      cases accepted
      have member : edge ∈ [edge] := .head _
      rw [← filtered] at member
      have facts := (List.mem_filter.mp member).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at facts
      exact facts.2
    · cases accepted

/-- The exact edge check cannot silently redirect the canonical target. -/
theorem selected_signature_target
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node instantiation isReference =
      .ok (index, signature)) :
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[index]? = some signature := by
  obtain ⟨_, target, _, _, _, _, targeted, edge, _, _, global⟩ := selected_signature_facts accepted
  have key := edge_target edge
  exact ⟨key.symm ▸ targeted, global⟩

/-- Real ordinary direct-call lowering with no argument children emits the
global-cell helper. The selected signature is exposed without asserting source
declaration identity from its native parameter/result types. -/
theorem nil_call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee [] (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments []).expression compilation.internalReason ∧
      lowered.type = type := by
  cases hook : policy.lowerSpecial? <;>
    simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [bind, Except.bind, pure, Except.pure, form, read, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted
    · cases accepted
    · obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
      rcases selection with ⟨index, signature⟩
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
      · obtain ⟨_, _, accepted⟩ := bind_ok accepted
        simp only [List.mapM_nil, bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        cases accepted
        exact ⟨index, signature, selectionReceipt, rfl, rfl⟩

/-- An accepted declaration reference retains its real callable-decoration
request. Its descriptor origin is the selected key, not a native type guess. -/
theorem reference_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature identity,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation true = .ok (index, signature) ∧
      Word.ofNat? (index + 1) = some identity ∧
      policy.callables.decorateCallable compilation source node (.named signature.key)
        signature.parameterType signature.resultType
        (SourceCoreFunctions.namedReference signature
          (scope.length + compilation.administrativePrefix + index) identity compilation.internalReason) =
        .ok lowered.expression ∧ lowered.type = type := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook,
      bind, Except.bind, pure, Except.pure] at accepted
    try rw [special] at accepted
    simp only [bind, Except.bind, pure, Except.pure, form, read] at accepted
    obtain ⟨selection, selectionReceipt, accepted⟩ := bind_ok accepted
    rcases selection with ⟨index, signature⟩
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · rename_i identity wordReceipt
      obtain ⟨expression, decorated, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨index, signature, identity, selectionReceipt, wordReceipt, decorated, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted

/-- Nil argument packing is a concrete static typed argument certificate. -/
theorem nil_arguments_typed (environment : Core.Context) (definitions : DataEnvironment) :
    HasType environment (SourceCoreCalls.packArguments []).expression
      (LanguageResult.resultType .unit) definitions :=
  .inRight .word .unit

theorem nil_arguments_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (SourceCoreCalls.packArguments []).expression (.inRight .word .unit) store :=
  .inRight .unit

end Solcore.SourceSemantics.CoreLowering.NamedCalls
