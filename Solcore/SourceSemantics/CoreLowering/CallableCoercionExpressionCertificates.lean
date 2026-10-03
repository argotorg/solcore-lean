import Solcore.SourceSemantics.CoreLowering.CallableCallEvidenceCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourcePathMeaning

/-! Receipts from the real outer evidence lowering, before and after its output
coercions. Raw-form semantics are not fields. The delegated branch retains the
actual sanitized source; direct calls retain the actual packed argument code
and selected global slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
open Core Frontend SourceInference
abbrev Lowered := SourceCoreBasic.LoweredExpr
abbrev Projector := SourceCoreEvidence.Projector
abbrev Context := SourceCoreFunctions.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Available := SourceCompilationPlan.EvidenceEnvironment

def rawNode (node : ExpressionNode) (ordinary : List RequirementId) : ExpressionNode :=
  {node with type := node.rawType, requirements := ordinary, coercions := []}

/-- The delegated cases of the actual match. Named/indirect calls and selected
operator methods use their separate compiler branches. -/
def Delegates (node : ExpressionNode) (ordinary : List RequirementId) : Prop :=
  match node.form with
  | .call _ _ (.declaration _) | .reference _ (.declaration _) | .call _ _ (.indirect _) => False
  | .unary .. | .binary .. => ordinary = []
  | _ => True

structure Suffix (program : CheckedProgram) (project : Projector) (compilation : Context)
    (caller : Specialized) (available : Available) (scope : Scope) (node : ExpressionNode)
    (policy : SourceCoreFunctions.CallablePolicy) (operand output : Lowered) : Prop where
  inputProjection : project (.occurrence node.id.occurrence) node.rawType = .ok operand.type
  accepted : SourceCoreEvidence.applyCoercions program project compilation caller available scope node policy operand node.coercions = .ok output
  outputProjection : project (.occurrence node.id.occurrence) node.type = .ok output.type

structure Output (program : CheckedProgram) (project : Projector) (caller : Specialized)
    (compilation : Context) (child : SourceCoreEvidence.Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word)
    (policy : SourceCoreFunctions.CallablePolicy) (node : ExpressionNode) (output : Lowered) where
  available : Available
  operand : Lowered
  found : source.lookupExpression? id = some node
  accepted : SourceCoreEvidence.lowerWithProjector program project caller compilation child fuel source scope id reasonAt policy = .ok (some output)
  pathValid : node.hasValidCoercionPath = true
  owner : caller.key = compilation.owner
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  suffix : Suffix program project compilation caller available scope node policy operand output

structure Delegated (program : CheckedProgram) (project : Projector) (caller : Specialized)
    (compilation : Context) (child : SourceCoreEvidence.Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word)
    (policy : SourceCoreFunctions.CallablePolicy) (node : ExpressionNode) (output : Lowered)
    extends Output program project caller compilation child fuel source scope id reasonAt policy node output where
  ordinary : List RequirementId
  ordinaryAccepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ordinary
  delegates : Delegates node ordinary
  childAccepted : child fuel (SourceCoreEvidence.withNode source (rawNode node ordinary)) scope id reasonAt = .ok operand

/-- Only actual selected signature/global rows and emitted call syntax are
retained here. No call or body evaluation is assumed. -/
structure NativeCall (compilation : Context) (scope : Scope) (key : SourceCompilationPlan.Key)
    (arguments operand : Lowered) where
  signature : SourceCoreCalls.Signature
  index : Nat
  global : compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = [(signature, index)]
  inputType : signature.parameterType = arguments.type
  emitted : operand = ⟨signature.resultType, SourceCoreCalls.call signature
    (scope.length + compilation.administrativePrefix + index) arguments.expression compilation.internalReason⟩

structure Direct (program : CheckedProgram) (project : Projector) (caller : Specialized)
    (compilation : Context) (child : SourceCoreEvidence.Child) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (id callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) (reasonAt : ExpressionId → Word)
    (policy : SourceCoreFunctions.CallablePolicy) (node : ExpressionNode) (output : Lowered)
    extends Output program project caller compilation child fuel source scope id reasonAt policy node output where
  form : node.form = .call callee arguments (.declaration instantiation)
  selection : CallableCallEvidenceCertificates.Selection program caller compilation node instantiation false
  sameAvailable : selection.available = available
  calleeAccepted : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation = .ok ()
  arity : arguments.length = selection.specialized.function.typedBody.inputs.length
  loweredArguments : List Lowered
  argumentsAccepted : arguments.mapM (fun argument => child fuel source scope argument reasonAt) = .ok loweredArguments
  native : NativeCall compilation scope selection.key (SourceCoreCalls.packArguments loweredArguments) operand

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {returned : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok returned) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted <;> simp_all

private theorem suffix {program : CheckedProgram} {project : Projector} {compilation : Context}
    {caller : Specialized} {available : Available} {scope : Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy} {operand output : Lowered}
    (accepted : (do
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project (.occurrence node.id.occurrence) node.rawType) operand.type
      let result ← SourceCoreEvidence.applyCoercions program project compilation caller available scope node policy operand node.coercions
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) (← project (.occurrence node.id.occurrence) node.type) result.type
      pure (some result) : Except SourceCoreBasic.Error (Option Lowered)) = .ok (some output)) :
    Suffix program project compilation caller available scope node policy operand output := by
  obtain ⟨inputType, inputProjection, accepted⟩ := bind_ok accepted
  obtain ⟨_, inputEq, accepted⟩ := bind_ok accepted
  obtain ⟨result, path, accepted⟩ := bind_ok accepted
  obtain ⟨outputType, outputProjection, accepted⟩ := bind_ok accepted
  obtain ⟨_, outputEq, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨by rwa [ensure_eq inputEq] at inputProjection, path,
    by rwa [ensure_eq outputEq] at outputProjection⟩

variable {program : CheckedProgram} {project : Projector} {caller : Specialized} {compilation : Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}

private theorem delegated_finish {ordinary : List RequirementId}
    (found : source.lookupExpression? id = some node)
    (ordinaryAccepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ordinary)
    (delegates : Delegates node ordinary)
    (original : SourceCoreEvidence.lowerWithProjector program project caller compilation child fuel source scope id reasonAt policy = .ok (some output))
    (accepted : (do
      if node.coercions.isEmpty && (node.requirements.isEmpty || (match node.form with | .integerLiteral .. => true | _ => false)) then
        return none
      unless node.hasValidCoercionPath do throw (.coercionsPresent id)
      if caller.key ≠ compilation.owner then throw (.ownerMismatch compilation.owner.declaration caller.key.declaration)
      let available ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions).mapError SourceCoreBasic.Error.callPreparation
      let operand ← child fuel (SourceCoreEvidence.withNode source (rawNode node ordinary)) scope id reasonAt
      SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project (.occurrence node.id.occurrence) node.rawType) operand.type
      let result ← SourceCoreEvidence.applyCoercions program project compilation caller available scope node policy operand node.coercions
      SourceCoreBasic.ensureType (.occurrence id.occurrence) (← project (.occurrence node.id.occurrence) node.type) result.type
      pure (some result) : Except SourceCoreBasic.Error (Option Lowered)) = .ok (some output)) :
    Nonempty (Delegated program project caller compilation child fuel source scope id reasonAt policy node output) := by
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  by_cases bypass : (node.coercions.isEmpty && (node.requirements.isEmpty || (match node.form with | .integerLiteral .. => true | _ => false))) = true
  · simp only [bypass, ↓reduceIte] at accepted
    cases accepted
  · simp only [bypass] at accepted
    by_cases path : node.hasValidCoercionPath = true
    · by_cases owner : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owner, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, accepted⟩ := bind_ok accepted
        obtain ⟨operand, childAccepted, accepted⟩ := bind_ok accepted
        refine ⟨{
          available := available, operand := operand, found := found, accepted := original,
          pathValid := path, owner := owner,
          resolved := by simpa only [owner] using mapError_ok resolved,
          suffix := ?_, ordinary := ordinary, ordinaryAccepted := ordinaryAccepted,
          delegates := delegates, childAccepted := childAccepted }⟩
        apply suffix
        rw [← (lookupExpression?_sound found).2] at accepted
        exact accepted
      · simp [path, owner] at accepted
    · simp [path] at accepted

/-- No source-view equality is inferred from this acceptance. The exact raw
sanitizer and child call remain visible in the returned receipt. -/
theorem delegated_of_accepted {ordinary : List RequirementId}
    (found : source.lookupExpression? id = some node)
    (ordinaryAccepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some ordinary)
    (delegates : Delegates node ordinary)
    (accepted : SourceCoreEvidence.lowerWithProjector program project caller compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    Nonempty (Delegated program project caller compilation child fuel source scope id reasonAt policy node output) := by
  apply delegated_finish found ordinaryAccepted delegates accepted
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  cases form : node.form with
  | literal literal =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | integerLiteral literal resolution =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | reference name resolution =>
    cases resolution <;> simp_all [Delegates, rawNode, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    all_goals exact accepted
  | group inner =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | tuple elements =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | unary operator operand =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, delegates, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | binary left operator right =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, delegates, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | conditional condition left right =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | lambda parameters type body =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | call callee arguments resolution =>
    cases resolution <;> simp_all [Delegates, rawNode, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    all_goals exact accepted
  | constructor instantiation arguments =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | member base name index =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | proxy type =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted
  | index base index =>
    simp only [Delegates, form] at delegates
    simp [rawNode, found, form, ordinaryAccepted, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted ⊢
    exact accepted

/-- Direct acceptance exposes the real ordered child calls, global slot and raw
call result before the same outer coercion helper. -/
theorem direct_of_accepted {callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (original : SourceCoreEvidence.lowerWithProjector program project caller compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    Nonempty (Direct program project caller compilation child fuel source scope id callee arguments instantiation reasonAt policy node output) := by
  obtain ⟨selection, selectedCallee, selectedArity⟩ := CallableCallEvidenceCertificates.direct_of_accepted found form original
  have accepted := original
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · by_cases path : node.hasValidCoercionPath = true
    · by_cases owned : caller.key = compilation.owner
      · simp only [path, ↓reduceIte, owned, ne_eq, not_true_eq_false] at accepted
        obtain ⟨available, resolved, accepted⟩ := bind_ok accepted
        obtain ⟨validated, calleeAccepted, branch⟩ := bind_ok accepted
        obtain ⟨actual, materialized, branch⟩ := bind_ok branch
        obtain ⟨target, targeted, branch⟩ := bind_ok branch
        obtain ⟨key, edge, branch⟩ := bind_ok branch
        obtain ⟨specialized, selected, branch⟩ := bind_ok branch
        obtain ⟨authenticatedUnit, authenticated, branch⟩ := bind_ok branch
        split at branch
        · cases branch
        · rename_i arity
          have availableEq : selection.available = available := Except.ok.inj (selection.resolved.symm.trans (by simpa only [owned] using mapError_ok resolved))
          have targetEq : selection.target = target := Except.ok.inj (selection.targetSelected.symm.trans (mapError_ok targeted))
          have keyEq : selection.key = key := by
            have edgeAccepted := mapError_ok edge
            rw [← (lookupExpression?_sound found).2, ← targetEq] at edgeAccepted
            exact Except.ok.inj (selection.edge.symm.trans edgeAccepted)
          obtain ⟨loweredArguments, argumentsAccepted, branch⟩ := bind_ok branch
          obtain ⟨operand, invoked, branch⟩ := bind_ok branch
          have suffixReceipt : Suffix program project compilation caller available scope node policy operand output := by
            apply suffix
            rw [← (lookupExpression?_sound found).2] at branch
            exact branch
          obtain ⟨pair, signatureAccepted, invoked⟩ := bind_ok invoked
          rcases pair with ⟨index, stored⟩
          obtain ⟨_, inputTypeEq, emitted⟩ := bind_ok invoked
          change (pure ⟨stored.resultType, SourceCoreCalls.call stored
            (scope.length + compilation.administrativePrefix + index) (SourceCoreCalls.packArguments loweredArguments).expression
              compilation.internalReason⟩ : Except SourceCoreBasic.Error Lowered) = .ok operand at emitted
          have operandEq := (Except.ok.inj emitted).symm
          change ((do
            let actual ← (SourceCompilationPlan.exactSpecialization compilation.plan key).mapError SourceCoreBasic.Error.callPreparation
            if !policy.allowStaged && (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime)) then
              throw (.unsupportedExpression node.id (.call callee arguments (.declaration instantiation)))
            let (parameter, result) ← match actual.function.type with
              | .function parameter result => pure (parameter, result)
              | _ => throw (.callPreparation (.invalidFunctionType key actual.function.type))
            let (stored, index) ← match compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
              | [row] => pure row
              | [] => throw (.callPreparation (.missingSpecialization key))
              | rows => throw (.callPreparation (.duplicateSpecialization key rows.length))
            SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.parameterType (← project (.occurrence node.id.occurrence) parameter)
            SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.resultType (← project (.occurrence node.id.occurrence) result)
            pure (index, stored)) : Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) = .ok (index, stored) at signatureAccepted
          obtain ⟨actualFunction, _, signatureAccepted⟩ := bind_ok signatureAccepted
          by_cases staged : (!policy.allowStaged && (actualFunction.function.returnComptime || actualFunction.function.typedBody.inputs.any (·.comptime))) = true
          · simp [staged, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at signatureAccepted
          · simp only [staged] at signatureAccepted
            cases functionType : actualFunction.function.type <;>
              simp only [functionType, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at signatureAccepted <;>
              try contradiction
            rename_i parameter result
            generalize global : compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = rows at signatureAccepted
            cases rows with
            | nil => cases signatureAccepted
            | cons row rows =>
              cases rows with
              | cons second rest => cases signatureAccepted
              | nil =>
                rcases row with ⟨selectedStored, selectedIndex⟩
                obtain ⟨_, _, signatureAccepted⟩ := bind_ok signatureAccepted
                obtain ⟨_, _, signatureAccepted⟩ := bind_ok signatureAccepted
                obtain ⟨_, _, signatureAccepted⟩ := bind_ok signatureAccepted
                obtain ⟨_, _, same⟩ := bind_ok signatureAccepted
                cases same
                exact ⟨{
                  available, operand, found, accepted := original, pathValid := path, owner := owned,
                  resolved := by simpa only [owned] using mapError_ok resolved, suffix := suffixReceipt, form, selection, sameAvailable := availableEq,
                  calleeAccepted := by cases validated; exact mapError_ok calleeAccepted,
                  arity := selectedArity,
                  loweredArguments, argumentsAccepted,
                  native := ⟨selectedStored, selectedIndex, by simpa only [keyEq] using global, ensure_eq inputTypeEq, operandEq⟩ }⟩
      · simp [owned, path] at accepted
    · simp [path] at accepted

end Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
