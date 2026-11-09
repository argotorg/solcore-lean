import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionMethods
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins

/-!
# Coercions: expressions

Certificates and meaning of coerced expressions and raw groups.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
/-! Outer coercions compose with laws for the original uncoerced expression
form. These laws are explicit theorem arguments, including the original owned
requirements; no whole-expression meaning is a field of a compiler receipt.
The raw sanitizer's child semantics and recursive grammar closure are separate
obligations. Generalized local reads are outside this nonlocal interface. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates

def RawOutcome (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (node : ExpressionNode) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value value => Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value after
  | .fault reason => Dynamic.ExpressionFormFaults program context evidence source environment before
      node.form node.requirements node.coercions reason after

def Path (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (before : Dynamic.Heap) (steps : List CoercionStep) (value : Dynamic.Value)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionPathExecutes program context evidence before steps value result after
  | .fault reason => Dynamic.CoercionPathFaults program context evidence before steps value reason after

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (node : ExpressionNode) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | rawFault {reason after}
      (raw : RawOutcome program context evidence source environment before node (.fault reason) after) :
      Trace program context evidence source environment before node (.fault reason) after
  | path {value middle outcome after}
      (raw : RawOutcome program context evidence source environment before node (.value value) middle)
      (path : Path program context evidence middle node.coercions value outcome after) :
      Trace program context evidence source environment before node outcome after

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem source_inv {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    Trace program context evidence source environment before node outcome after := by
  have contains := lookupExpression?_sound found
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw path
    | generalizedLocal other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form other raw => exact .rawFault (contains_unique unique other contains ▸ raw)
    | coercion other raw failed =>
      have same := contains_unique unique other contains
      subst same
      exact .path raw failed
    | generalizedLocalRequirement other form _ _ _ _ _ _ _ | generalizedLocalCoercion other form _ _ _ _ _ _ _ =>
      have same := contains_unique unique other contains
      subst same
      exact False.elim (notLocal _ _ form)

theorem Trace.source {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? id = some node)
    (trace : Trace program context evidence source environment before node outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | rawFault raw => exact .fault (.form (lookupExpression?_sound found) raw)
  | path raw path =>
    cases outcome with
    | value value => exact .value (.intro (lookupExpression?_sound found) raw path)
    | fault reason => exact .fault (.coercion (lookupExpression?_sound found) raw path)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

/-- A pointwise law for the original raw form, not for an already coerced
ExpressionEvaluates outcome and not for a rewritten source graph. -/
def RawFormPreserves (faults : FunctionCalls.FaultRep) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) (node : ExpressionNode)
    (ξ : Renaming) (operand : Lowered) : Prop :=
  ∀ {outcome after}, RawOutcome (Program.ofChecked compilerProgram) context evidence source environment before node outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (operand.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.rawType operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-- Completion reflection for that same original raw form. -/
def RawFormReflects (faults : FunctionCalls.FaultRep) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (caller : Environment)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) (node : ExpressionNode)
    (ξ : Renaming) (operand : Lowered) : Prop :=
  ∀ {value finalStore}, Evaluates caller store (operand.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      RawOutcome (Program.ofChecked compilerProgram) context evidence source environment before node outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.rawType operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

section Common

/-- The original raw trace and the reached ordered path stay separate. The
path relation may retain the actual selected dictionaries and body receipts. -/
inductive TraceFor (raw : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop)
    (path : Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | rawFault {reason after} (trace : raw (.fault reason) after) : TraceFor raw path (.fault reason) after
  | path {value middle outcome after} (trace : raw (.value value) middle)
      (tail : path middle value outcome after) : TraceFor raw path outcome after

theorem Trace.toFor {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (trace : Trace program context evidence source environment before node outcome after) :
    TraceFor (RawOutcome program context evidence source environment before node)
      (fun heap value => Path program context evidence heap node.coercions value) outcome after := by
  cases trace with
  | rawFault raw => exact .rawFault raw
  | path raw path => exact .path raw path

theorem TraceFor.toTrace {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (trace : TraceFor (RawOutcome program context evidence source environment before node)
      (fun heap value => Path program context evidence heap node.coercions value) outcome after) :
    Trace program context evidence source environment before node outcome after := by
  cases trace with
  | rawFault raw => exact .rawFault raw
  | path raw path => exact .path raw path

variable {State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type}
  (extend : ∀ {mapping finalMap world finalWorld before after store finalStore},
    State mapping world before store → LocationMap.Extends mapping finalMap → WorldExtends world finalWorld →
    AdministrativePreserved mapping store finalMap finalStore → Dynamic.HeapMetadataExtend before after →
    State finalMap finalWorld after finalStore)
  {rawTrace : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
  {pathTrace : Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
  {sourceType targetType : TypeSystem.Ty} {output : Lowered}
  {calls : List CallableCoercionSpine.Call} {reason : Word}
  (finalType : CallableCoercionSpine.finalType operand.type calls = output.type)
  (entry : State mapping world before store)

include extend finalType entry in
/-- The sole outer preservation joins the original raw outcome and ordered
path. Concrete callers discharge both continuations from their static receipts. -/
theorem preserves_for
    (emitted : output.expression.rename ξ = CallableCoercionSpine.emit reason (operand.expression.rename ξ) calls)
    (rawMeaning : ∀ {outcome after}, rawTrace outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates caller store (operand.expression.rename ξ) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld sourceType operand.type faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after)
    (pathMeaning : ∀ {mapping world before after store input native outcome},
      State mapping world before store →
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
      ValueRep values.checked registry functions mapping world sourceType input native operand.type →
      pathTrace before input outcome after →
      ∃ value finalStore finalMap finalWorld,
        CallableCoercionSpine.Runs caller reason store (.inRight .word native) calls value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld targetType output.type faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (State finalMap finalWorld after finalStore))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : TraceFor rawTrace pathTrace outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld targetType output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  cases trace with
  | rawFault raw =>
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning raw
    cases related with
    | @fault fault token represented =>
      refine ⟨.inLeft output.type (.word token), finalStore, finalMap, finalWorld, ?_, .fault represented,
        heaps, maps, worlds, admin, metadata, ⟨extend entry maps worlds admin metadata⟩⟩
      rw [emitted]
      have runs := CallableCoercionSpine.Runs.failure caller reason finalStore operand.type (.word token) calls
      simpa only [finalType] using runs.evaluates evaluated
  | path raw path =>
    obtain ⟨native, middleStore, middleMap, middleWorld, evaluated, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning raw
    cases related with
    | value represented =>
      obtain ⟨result, finalStore, finalMap, finalWorld, runs, related, finalHeaps, tailMaps, tailWorlds,
        tailAdmin, tailMetadata, finalEntry⟩ :=
        pathMeaning (extend entry maps worlds admin metadata) heaps represented path
      refine ⟨result, finalStore, finalMap, finalWorld, ?_, related, finalHeaps, maps.trans tailMaps,
        worlds.trans tailWorlds, admin.trans tailAdmin, metadata.trans tailMetadata, finalEntry⟩
      rw [emitted]
      exact runs.evaluates evaluated

include extend finalType entry in
/-- Original completion supplies an operand receipt and ordered invocations.
The receipt relation retains any measured child without recomputing a grade. -/
theorem reflects_for {E : Value → Store → Prop}
    {R : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, R call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    (rawMeaning : ∀ {value finalStore}, E value finalStore →
      ∃ outcome after finalMap finalWorld,
        rawTrace outcome after ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld sourceType operand.type faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after)
    (pathMeaning : ∀ {mapping world before store finalStore input native value},
      State mapping world before store →
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
      ValueRep values.checked registry functions mapping world sourceType input native operand.type →
      CallableCoercionSpine.RunsFor R store (.inRight .word native) calls value finalStore →
      ∃ outcome after finalMap finalWorld,
        pathTrace before input outcome after ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld targetType output.type faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (State finalMap finalWorld after finalStore))
    {value : Value} {finalStore : Store}
    (completedPrefix : ∃ native middleStore, E native middleStore ∧
      CallableCoercionSpine.RunsFor R middleStore native calls value finalStore) :
    ∃ outcome after finalMap finalWorld,
      TraceFor rawTrace pathTrace outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld targetType output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  obtain ⟨native, middleStore, evaluated, runs⟩ := completedPrefix
  obtain ⟨rawOutcome, middle, middleMap, middleWorld, raw, related, heaps, maps, worlds, admin, metadata⟩ := rawMeaning evaluated
  cases related with
  | fault represented =>
    obtain ⟨rfl, rfl⟩ := failed_runs ((runs.map forget).toRuns)
    refine ⟨_, _, _, _, .rawFault raw, ?_, heaps, maps, worlds, admin, metadata,
      ⟨extend entry maps worlds admin metadata⟩⟩
    rw [finalType]
    exact .fault represented
  | value represented =>
    obtain ⟨outcome, after, finalMap, finalWorld, path, related, finalHeaps, tailMaps, tailWorlds,
      tailAdmin, tailMetadata, finalEntry⟩ :=
      pathMeaning (extend entry maps worlds admin metadata) heaps represented runs
    exact ⟨_, _, _, _, .path raw path, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
      admin.trans tailAdmin, metadata.trans tailMetadata, finalEntry⟩
end Common

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  (receipt : Output compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry in
/-- Preserve an independent whole source outcome with its original raw form and
ordered coercions. The raw law is the remaining expression-grammar interface. -/
theorem preserves [FunctionCalls.FaultTokens faults]
    (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (rawMeaning : RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  have codeEq : output.expression.rename ξ = CallableCoercionSpine.emit compilation.internalReason
      (receipt.operand.expression.rename ξ) (methods.map (·.call)) := by
    rw [emitted.spine.code, CallableCoercionSpine.emit_rename, ← emitted.calls_eq]
  refine preserves_for functions (State := Entry methods ambient.definitions caller)
    (fun entry maps worlds admin metadata => entry.extend maps worlds admin metadata)
    chain.final_type entry codeEq rawMeaning ?_ (source_inv receipt.found unique notLocal trace).toFor
  intro middleMap middleWorld middle after middleStore input native outcome next heaps represented path
  have pathTrace : PathOutcome methods middle input outcome after := by
    cases outcome <;> simpa only [PathOutcome, Path, steps] using path
  exact CallableCoercionSourcePathMeaning.preserves checkedAccepted ledger functions extension definitions registered
    faithful observations runtimeViews uninitialized missing emitted chain next heaps represented pathTrace
    compilation.internalReason

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry in
/-- Reflect only finite completion of the real emitted expression. The source
form and path derivations retain their separate heaps and independent costs. -/
theorem reflects [FunctionCalls.FaultTokens faults]
    (rawMeaning : RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ receipt.operand)
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨native, middleStore, evaluated, runs⟩ := (emitted.spine.renamed_completed_iff ξ).mp completed
  rw [← emitted.calls_eq] at runs
  have reflected := reflects_for functions (State := Entry methods ambient.definitions caller)
    (rawTrace := RawOutcome (Program.ofChecked compilerProgram) context evidence source environment before node)
    (pathTrace := fun heap value => Path (Program.ofChecked compilerProgram) context evidence heap node.coercions value)
    (sourceType := node.rawType) (targetType := node.type)
    (fun entry maps worlds admin metadata => entry.extend maps worlds admin metadata)
    chain.final_type entry (fun invoked => invoked) rawMeaning
    (fun next heaps represented runs => ?_) ⟨native, middleStore, evaluated, runs.toFor⟩
  · obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, admin, metadata, next⟩ := reflected
    exact ⟨_, _, _, _, trace.toTrace.source receipt.found, related, heaps, maps, worlds, admin, metadata, next⟩
  · obtain ⟨outcome, after, finalMap, finalWorld, selected, related, heaps, maps, worlds, admin, metadata, next⟩ :=
      CallableCoercionPathMeaning.reflects functions extension definitions registered faithful observations runtimeViews
        uninitialized missing chain next heaps represented runs.toRuns
    refine ⟨_, _, _, _, ?_, related, heaps, maps, worlds, admin, metadata, next⟩
    cases outcome <;> simpa only [PathOutcome, Path, steps] using selected.sound

end Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
/-! A delegated group keeps the actual sanitizer and exact child code. The
changed parent is explicitly excluded from the child's reached references;
unique occurrence IDs alone do not imply that condition. No execution law is
stored in these static receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
open Core Frontend SourceInference
open CallableCoercionExpressionCertificates CallableLambdaViewEdits CallableLambdaBodyReachability

private theorem node_eq {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (first : source.lookupExpression? id = some left) (second : source.lookupExpression? id = some right) : left = right :=
  Option.some.inj (first.symm.trans second)

/-- The real replacement is found at the original occurrence, including all
of its changed type, requirement and coercion fields. -/
theorem raw_lookup {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (ordinary : List RequirementId) :
    (SourceCoreEvidence.withNode source (rawNode node ordinary)).lookupExpression? id = some (rawNode node ordinary) := by
  have sound := lookupExpression?_sound found
  have same : node.id = id := sound.2
  have self : source.lookupExpression? node.id = some node := same.symm ▸ found
  have edited := CallableLambdaViewEdits.raw unique self ordinary
  apply lookupExpression?_complete (edited.metadata.unique unique)
  constructor
  · apply List.mem_map.mpr
    refine ⟨.expression node, sound.1, ?_⟩
    simp [rawNode]
  · exact same

private theorem ordinary_empty {node : ExpressionNode}
    (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []) :
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  change (let coercions := coercionRequirementIds node.coercions
    if node.requirements.length < coercions.length then none else
      let owned := node.requirements.take (node.requirements.length - coercions.length)
      if node.requirements = owned ++ coercions then some owned else none) = some []
  simp [Dynamic.OrdinaryRequirementLayout] at layout
  simp [layout]

/-- Original independent group typing fixes the raw child type and empty
owned prefix. Retained output coercions remain in their original order. -/
theorem group_typing {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type) :
    ExpressionHasType source context inner node.rawType ∧
      TypeAdmissible context node.rawType ∧ Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq rawWF _ requirements =>
    have same := node_eq (lookupExpression?_complete unique contains) found
    subst same
    rw [form] at raw
    cases raw with
    | group child =>
      cases requirements with
      | ordinary _ _ layout =>
        refine ⟨rawEq ▸ child, rawEq ▸ rawWF, layout, ?_⟩
        exact ordinary_empty layout

/-- Only the child typing is transported. The edited root is then rebuilt with
its raw type and an empty output path using the independent typing rules. -/
theorem sanitized_typing {source : TypedSource} {context : SourceSemantics.Context}
    {id inner : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (typed : ExpressionHasType source context id node.type)
    (avoids : Avoids source [.expression inner] [node.id]) :
    ExpressionHasType (SourceCoreEvidence.withNode source (rawNode node [])) context id node.rawType := by
  obtain ⟨child, rawWF, _, _⟩ := group_typing unique found form typed
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound found).2.symm ▸ found
  have edited := CallableLambdaViewEdits.raw unique self []
  have childTyped := CallableLambdaViewStaticTyping.expression edited avoids unique child (.root (by simp))
  apply ExpressionHasType.ofOrdinary (lookupExpression?_sound (raw_lookup unique found []))
    (rawType := node.rawType) (owned := [])
  · simpa only [rawNode, form] using ExpressionFormHasRawType.group childTyped
  · exact rawWF
  · exact rawWF
  · exact fun id member => False.elim (List.not_mem_nil member)
  · exact .nil _
  · rfl

section Inversion
variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}

private theorem products_group
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | literal receipt =>
    obtain ⟨other, selected, literal⟩ := receipt
    have same := node_eq selected found
    subst other
    generalize lowered.type = nativeType at literal
    generalize lowered.expression = code at literal
    cases literal <;> simp_all
  | read receipt =>
    obtain ⟨receipt, _, _⟩ := receipt
    have same := node_eq receipt.metadata.found found
    have other := same ▸ receipt.form
    simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem primitives_group
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | product tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := products_group tree found form
    exact ⟨child, selected, same, ordinary, .product childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem conditionals_group
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | primitive tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := primitives_group tree found form
    exact ⟨child, selected, same, ordinary, .primitive childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem constructors_group
    (tree : CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionConstructors.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := conditionals_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm

private theorem members_group
    (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := constructors_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem recursive_group
    (tree : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := members_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

private theorem general_group
    (tree : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := recursive_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | proxy receipt =>
    cases receipt with
    | proxy header =>
      have same := node_eq header.metadata.found found
      have other := same ▸ header.form
      simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | index receipt _ otherForm _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm

private theorem builtins_group
    (tree : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner) :
    ∃ child, source.lookupExpression? inner = some child ∧ node.type = child.type ∧
      node.requirements = [] ∧ CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope inner lowered := by
  cases tree with
  | fragment tree =>
    obtain ⟨child, selected, same, ordinary, childTree⟩ := general_group tree found form
    exact ⟨child, selected, same, ordinary, .fragment childTree⟩
  | proxy receipt =>
    cases receipt with
    | proxy header =>
      have same := node_eq header.metadata.found found
      have other := same ▸ header.form
      simp [form] at other
  | group metadata otherForm childFound sameType child =>
    have same := node_eq metadata.found found
    subst same
    have sameInner := ExpressionForm.group.inj (otherForm.symm.trans form)
    subst sameInner
    exact ⟨_, childFound, sameType, metadata.requirements, child⟩
  | pair metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | unary metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | binary metadata otherForm _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | conditional metadata otherForm _ _ _ _ _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | constructor receipt otherForm _ _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | member metadata _ otherForm _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm
  | index receipt _ otherForm _ _ _ =>
    have same := node_eq receipt.metadata.found found
    subst same
    simp [form] at otherForm
  | builtin metadata otherForm _ _ _ _ _ =>
    have same := node_eq metadata.found found
    subst same
    simp [form] at otherForm

end Inversion


/-- A concrete child in the original source, with the same code returned by the
actual delegated sanitizer. Its own complete builtin subtree is finite. -/
structure Child (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : Scope) (node : ExpressionNode) (inner : ExpressionId) (operand : Lowered) where
  form : node.form = .group inner
  layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []
  innerNode : ExpressionNode
  found : source.lookupExpression? inner = some innerNode
  rawType : node.rawType = innerNode.type
  tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope inner operand

section Factory
variable {program : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel readFuel : Nat}
  {source : TypedSource} {scope : Scope} {id inner : ExpressionId} {node : ExpressionNode}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} {solved : List SolvedRequirement}

/-- Extract any group placement, including the existing fragment embeddings,
then transport its complete child tree back across the real local edit. -/
theorem of_tree
    (receipt : Delegated program project caller compilation child fuel source scope id reasonAt policy node output)
    (unique : NodeOccurrencesUnique source) (form : node.form = .group inner)
    (avoids : Avoids source [.expression inner] [node.id])
    (tree : CompatibleExpressionBuiltins.Tree readFuel values
      (SourceCoreEvidence.withNode source (rawNode node receipt.ordinary)) context solved reasonAt scope id receipt.operand) :
    Nonempty (Child readFuel values source context solved reasonAt scope node inner receipt.operand) := by
  obtain ⟨innerNode, selected, sameType, empty, childTree⟩ :=
    builtins_group tree (raw_lookup unique receipt.found receipt.ordinary) (show (rawNode node receipt.ordinary).form = .group inner from form)
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound receipt.found).2.symm ▸ receipt.found
  have edited := CallableLambdaViewEdits.raw unique self receipt.ordinary
  have reached : Reaches source [.expression inner] (.expression inner) := .root (by simp)
  have originalFound := (expression_lookup edited avoids reached).trans selected
  have layout := CallableCallRequirementLayouts.ordinary_owned receipt.ordinaryAccepted
  change receipt.ordinary = [] at empty
  rw [empty] at layout
  exact ⟨⟨form, layout, innerNode, originalFound, sameType,
    CallableLambdaViewBuiltinTrees.builtins_original edited avoids childTree reached⟩⟩

/-- The production contextual callback supplies the sanitized tree. Original
source typing reconstructs raw-root typing, so there is no separate assumed
sanitized typing or child execution law. Ordinary/static scope policies remain
explicit, including the absence of local-polymorphic initializers. -/
theorem of_contextual
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId}
    (receipt : Delegated program project caller compilation child fuel source scope id reasonAt policy node output)
    (childEq : child = SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents
      assignments diagnostics compilation (some native) parent skipInitializer)
    (unique : NodeOccurrencesUnique source) (form : node.form = .group inner)
    (typed : ExpressionHasType source context id node.type)
    (avoids : Avoids source [.expression inner] [node.id])
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source inner)
    (ordinary : CompatibleExpressionBuiltins.Ordinary (SourceCoreEvidence.withNode source (rawNode node [])) locals compilation.owner)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (SourceCoreEvidence.withNode source (rawNode node [])) scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values) :
    Nonempty (Child readFuel values source context compilation.solvedRequirements reasonAt scope node inner receipt.operand) := by
  have selected := (group_typing unique receipt.found form typed).2.2.2
  have empty := Option.some.inj (receipt.ordinaryAccepted.symm.trans selected)
  have self : source.lookupExpression? node.id = some node := (lookupExpression?_sound receipt.found).2.symm ▸ receipt.found
  have edited := CallableLambdaViewEdits.raw unique self []
  have childSyntax := CallableLambdaViewSourceTyping.expression_syntax edited avoids unique syntaxTree (.root (by simp))
  have rawFound := raw_lookup unique receipt.found []
  have rawTyped := sanitized_typing unique receipt.found form typed avoids
  have accepted := receipt.childAccepted
  simp only [childEq, empty] at accepted
  have tree := CompatibleExpressionBuiltins.tree_of_contextual ordinary (edited.metadata.unique unique)
    closed residual declarations sourceSignatures (.group rawFound form childSyntax) rawFound rawTyped
    readPolicy lowerPolicy leafPolicy accepted
  apply of_tree receipt unique form avoids
  simpa only [empty] using tree

end Factory

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
/-! Concrete builtin child meaning closes the original group's raw-form laws.
The source node retains its complete output path and ordered requirements.
Reflection uses only native completion and child reflection, never preservation
or a prior source execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries CallableCoercionPathMeaning
open CallableCoercionExpressionCertificates CallableCoercionExpressionMeaning CallableCoercionRawGroupCertificates

/-- Group evaluation exposes the original child's whole outcome. This does
not erase the child's own metadata or change the surrounding source graph. -/
theorem raw_inv {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {inner : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (form : node.form = .group inner)
    (trace : RawOutcome program context evidence source environment before node outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after := by
  cases outcome with
  | value value =>
    change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ at trace
    rw [form] at trace
    cases trace with | group _ evaluated => exact .value evaluated
  | fault reason =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ at trace
    rw [form] at trace
    cases trace with | group _ failed => exact .fault failed

theorem raw_intro {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {node : ExpressionNode} {inner : ExpressionId} {outcome : Dynamic.ExpressionOutcome}
    (form : node.form = .group inner) (layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after) :
    RawOutcome program context evidence source environment before node outcome after := by
  cases trace with
  | value evaluated =>
    change Dynamic.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .group layout evaluated
  | fault failed =>
    change Dynamic.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _
    rw [form]
    exact .group layout failed

section Raw
variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {compilerProgram : CheckedProgram} {evidence : Dynamic.EvidenceEnvironment}
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {scope : Scope} {node : ExpressionNode} {inner : ExpressionId} {operand : Lowered}
  (child : Child readFuel values source context solved reasonAt scope node inner operand)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical caller : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)

include extension faithful observations runtimeViews valid uninitialized missing child environments heaps locals agrees actualTyped in
theorem raw_preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source) :
    RawFormPreserves (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ operand := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, admin, metadata⟩ :=
    CompatibleExpressionBuiltins.preserves functions extension faithful observations runtimeViews
      (Program.ofChecked compilerProgram) evidence valid unique uninitialized missing child.tree child.found
      environments heaps locals agrees actualTyped (raw_inv child.form trace)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, child.rawType.symm ▸ represented,
    finalHeaps, maps, worlds, admin, metadata⟩

include extension faithful observations runtimeViews valid uninitialized missing child environments heaps locals agrees actualTyped in
theorem raw_reflects [FunctionCalls.FaultTokens faults] :
    RawFormReflects (compilerProgram := compilerProgram) (context := context) (evidence := evidence) (registry := registry)
      functions faults source environment before caller mapping world store node ξ operand := by
  intro value finalStore evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, admin, metadata⟩ :=
    CompatibleExpressionBuiltins.reflects functions extension faithful observations runtimeViews
      (Program.ofChecked compilerProgram) evidence valid uninitialized missing child.tree child.found
      environments heaps locals agrees actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, raw_intro child.form child.layout trace,
    child.rawType.symm ▸ represented, finalHeaps, maps, worlds, admin, metadata⟩
end Raw

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {compilerProgram : CheckedProgram}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap}
  {caller : Environment} {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {node : ExpressionNode} {ξ : Renaming} {operand : Lowered}

variable {raw : Workspace.RawWorkspace} {checkFuel : Nat}
  (checkedAccepted : checkProgram raw checkFuel = .ok compilerProgram)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := Program.ofChecked compilerProgram)
    (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  {project : Projector} {compilation : SourceCoreFunctions.Context} {callerFunction : Specialized} {available : Available}
  {scope : Scope} {id : ExpressionId} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy} {output : Lowered}
  {calls : List CallableCoercionSpine.Call}
  (receipt : Delegated compilerProgram project callerFunction compilation child fuel source scope id reasonAt policy node output)
  (emitted : Emitted compilerProgram project compilation callerFunction receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : Chain node.rawType receipt.operand.type methods node.type output.type)
  (ledger : context.solvedRequirements = callerFunction.function.solvedRequirements)
  (entry : Entry methods ambient.definitions caller mapping world before store)


variable {readFuel : Nat} {inner : ExpressionId} {solved : List SolvedRequirement}
  (childTree : Child readFuel values source context solved reasonAt scope node inner receipt.operand)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (rawUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (rawMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {administrative : Core.Context} {canonical : Environment} {actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical caller)
  (actualTyped : RuntimeEnvironmentHasTypes world caller actualContext ambient.definitions)

include checkedAccepted extension definitions registered faithful observations runtimeViews uninitialized missing ledger emitted steps chain entry childTree valid rawUninitialized rawMissing environments heaps locals agrees actualTyped in
theorem preserves [FunctionCalls.FaultTokens faults]
    (unique : NodeOccurrencesUnique source)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.preserves functions checkedAccepted extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain ledger entry unique (by intros; simp [childTree.form])
    (raw_preserves functions extension faithful observations runtimeViews valid rawUninitialized rawMissing childTree
      environments heaps locals agrees actualTyped unique) trace

include extension definitions registered faithful observations runtimeViews uninitialized missing emitted steps chain entry childTree valid rawUninitialized rawMissing environments heaps locals agrees actualTyped in
theorem reflects [FunctionCalls.FaultTokens faults]
    {value : Value} {finalStore : Store}
    (completed : Evaluates caller store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked compilerProgram) context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact CallableCoercionExpressionMeaning.reflects functions extension definitions registered faithful observations runtimeViews
    uninitialized missing receipt.toOutput emitted steps chain entry
    (raw_reflects functions extension faithful observations runtimeViews valid rawUninitialized rawMissing childTree
      environments heaps locals agrees actualTyped) completed

end Solcore.SourceSemantics.CoreLowering.CallableCoercionRawGroupMeaning
end
