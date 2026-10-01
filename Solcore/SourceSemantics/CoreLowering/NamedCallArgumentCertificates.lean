import Solcore.SourceSemantics.CoreLowering.NamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralCertificates

/-! Actual ordinary named-call lowering retains every argument compiler
result. These are static receipts; argument and body execution remain in the
independent semantic relations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem type_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {value : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok value) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- The actual selected canonical target and ordered argument traversal.
The compiler checked the original arity and packed native parameter type. -/
theorem call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature specialized codes,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      arguments.length = specialized.function.typedBody.inputs.length ∧
      arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes ∧
      signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
      signature.resultType = type ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
      lowered.type = type := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
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
      obtain ⟨specialized, specialization, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted
      · rename_i arity
        obtain ⟨_, resultChecked, accepted⟩ := bind_ok accepted
        obtain ⟨codes, argumentCodes, accepted⟩ := bind_ok accepted
        obtain ⟨_, parameterChecked, accepted⟩ := bind_ok accepted
        cases accepted
        refine ⟨index, signature, specialized, codes, selectionReceipt, ?_, ?_, argumentCodes, ?_, ?_, rfl, rfl⟩
        · cases actual : SourceCompilationPlan.exactSpecialization compilation.plan signature.key <;>
            simp [actual, Except.mapError] at specialization ⊢
          exact specialization
        · exact Classical.not_not.mp arity
        · exact type_eq parameterChecked
        · exact type_eq resultChecked

private theorem argument_types {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (children : DataExpressionSequence.Tree source
      (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) scope ids types codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction children with
  | nil => rfl
  | single found child => simp [child.projected found, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | cons found child _ ih => simp [List.mapM_cons, child.projected found, ih, Functor.map, Except.map, bind, Except.bind]

/-- Instantiate successful argument traversal with concrete General trees.
Raw source argument types and per-binder projections are independent static
typing facts. Packed type equality alone cannot recover source arity. -/
theorem arguments_of_functions
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {bindings : List (TypedBinder × Ty)}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.declaration instantiation))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (children : ∀ codes, arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes →
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt)
        scope arguments (bindings.map (fun binding => binding.1.scheme.body)) codes)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ index signature specialized codes,
      SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) ∧
      SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized ∧
      arguments.length = specialized.function.typedBody.inputs.length ∧
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt)
        scope arguments (bindings.map (fun binding => binding.1.scheme.body)) codes ∧
      codes.map (·.type) = bindings.map Prod.snd ∧
      signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
      signature.resultType = type ∧
      lowered.expression = SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
      lowered.type = type := by
  obtain ⟨index, signature, specialized, codes, selected, specializedReceipt, arity, codesReceipt,
    parameter, result, emitted, nativeType⟩ := call_of_accepted owner found read form special accepted
  have argumentTrees := children codes codesReceipt
  have nativeTypes := Except.ok.inj ((argument_types argumentTrees).symm.trans projected)
  exact ⟨index, signature, specialized, codes, selected, specializedReceipt, arity,
    argumentTrees, nativeTypes, parameter, result, emitted, nativeType⟩

/-- An occurrence retains the actual compiler action and the exact selected
slot and child results. Every field is static syntax or compiler success. -/
structure Emission (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) (signature : SourceCoreCalls.Signature)
    (codes : List SourceCoreBasic.LoweredExpr) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  reasonAt : ExpressionId → Word
  node : ExpressionNode
  type : Ty
  owner : id.occurrence.owner = source.owner
  found : source.lookupExpression? id = some node
  read : policy.readExpression source id = .ok (node, type)
  form : node.form = .call callee arguments (.declaration instantiation)
  special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
            compilation childSource childScope childId childReasonAt)
        (fuel + 1) source scope id reasonAt) = .ok none
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  index : Nat
  selection : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature)
  argumentsAccepted : arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
    compilation source scope argument reasonAt) = .ok codes

/-- The saved compiler actions determine the emitted helper and canonical
target. Equality is propositional; no executable Plan equality is assumed. -/
theorem Emission.equation {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {signature : SourceCoreCalls.Signature}
    {codes : List SourceCoreBasic.LoweredExpr} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation source scope id callee arguments instantiation signature codes lowered) :
    lowered.expression = SourceCoreCalls.call signature
      (scope.length + compilation.administrativePrefix + receipt.index)
      (SourceCoreCalls.packArguments codes).expression compilation.internalReason ∧
    signature.parameterType = (SourceCoreCalls.packArguments codes).type ∧
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[receipt.index]? = some signature := by
  obtain ⟨index, selectedSignature, specialized, actualCodes, selected, _, _, compiled, parameter, _, emitted, _⟩ :=
    call_of_accepted receipt.owner receipt.found receipt.read receipt.form receipt.special receipt.accepted
  have same := Except.ok.inj (selected.symm.trans receipt.selection)
  cases same
  have sameCodes := Except.ok.inj (compiled.symm.trans receipt.argumentsAccepted)
  cases sameCodes
  have target := NamedCalls.selected_signature_target receipt.selection
  exact ⟨emitted, parameter, target⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
