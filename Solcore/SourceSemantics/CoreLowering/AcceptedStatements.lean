import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ActualInvocationAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ProgramCompletion
import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationForLoops
import Solcore.SourceSemantics.CoreLowering.TypedImperativeNative
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationMatches
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildrenExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationLoops
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationAssignments

/-!
# Accepted bodies: the statement closure

The mixed-cell statement flows are closed by induction over the compiler's accepted
tree. `CellAwareInvocationAcceptedFlow.correct` is the closure, and
`CellAwareInvocationAcceptedFlow.body_preserves` and
`CellAwareInvocationAcceptedFlow.body_reflects` compose it with the actual footer, so
they relate a body to independent Source execution in both directions.

Main declarations:
- `CellAwareInvocationAcceptedFlow.Covered`, the statements closed so far;
- `CellAwareInvocationAcceptedInputs.Expressions`, the meaning of accepted expressions,
  an explicit premise here;
- `CellAwareInvocationAcceptedInputs.Writes` and
  `CellAwareInvocationAcceptedInputs.Generalized`, the other premises;
- `CellAwareInvocationAcceptedMatches.Admitted` and
  `CellAwareInvocationAcceptedForItems.ItemsCovered`, matches and `for` headers;
- `CellAwareInvocationAcceptedNative.WordFailure`, the failure component of native
  typing.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
/-! Actual accepted return and tail-expression compiler branches consume the
same smaller expression proof. The child certificate is exactly the policy
call retained by the accepted body tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {context : SourceSemantics.Context} {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep} {administrative : Core.Context}
  {scope : SourceCoreLocalCell.Scope} {id : StatementId} {statement : StatementNode} {stored : Core.Ty}
  {expression : ExpressionId} {node : ExpressionNode} {expected : TypeSystem.Ty}
  {lowered : SourceCoreBasic.LoweredExpr}

def children {bodyRelation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled bodyRelation) (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => index.policy.lowerExpression fuel index.compilerSource scope expression
    index.reasonAt = .ok lowered

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

theorem returning {childFuel budget : Nat} {rest : List StatementId}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .returnStmt (some expression))
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.return_head source rest read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

theorem tail {childFuel budget : Nat}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .expression expression false)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.tail_head source read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTerminals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
/-! Fixed-control checker typing supplies the static Source facts consumed at
each accepted compiler statement. The actual compiler read selects the node;
typing never chooses a different statement or expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
open Core Frontend SourceInference

variable {source : TypedSource}

/-- The original statement typing splits at the node read by the compiler. -/
theorem head_form (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {id : StatementId}
    {rest : List StatementId} {facts : BodyFacts} {node : StatementNode}
    (typed : StatementsHaveType source control context (id :: rest) final facts)
    (found : source.lookupStatement? id = some node) :
    ∃ middle restFacts, Dynamic.StatementHasType.FormTyping source control context node.form middle ∧
      StatementsHaveType source control middle rest final restFacts := by
  cases typed with
  | singleton head =>
    obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : original = node :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst same
    exact ⟨_, _, formTyped, .nil _ _⟩
  | cons head tail =>
    obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : original = node :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst same
    exact ⟨_, _, formTyped, tail⟩

/-- Expression typing identifies the unique original node and its stored type. -/
theorem expression_node (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType source context id type) :
    ∃ node, source.lookupExpression? id = some node ∧ node.type = type ∧
      ExpressionHasType source context id node.type := by
  have original := typed
  cases typed with
  | intro contains _ _ _ _ _ => exact ⟨_, lookupExpression?_complete unique contains, rfl, original⟩

/-- A monomorphic binder uses the catalog projection in every actual body
policy, named or contextual. -/
theorem binder_projected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (accepted : index.policy.lowerBinder source scope binder = .ok payload) :
    compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload := by
  cases index with
  | named receipt selected =>
    simp only [ActualBodyInvocation.Index.policy, AcceptedNamedBodyFlow.namedPolicy,
      SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte] at accepted
    exact CompatibleStatementBindings.binder_projected accepted
  | contextual material view =>
    simp only [ActualBodyInvocation.Index.policy, GeneralizedLocalAcceptedBodyCompiler.policy,
      GeneralizedLocalLambdaCompilation.binder, SourceCoreGeneralFunctions.contextualBinder, mono,
      List.isEmpty_nil, ↓reduceIte, GeneralizedLocalLambdaCompilation.representation] at accepted
    rw [material.indexed.represented] at accepted
    exact CompatibleStatementBindings.binder_projected accepted

/-- The actual statement read also locates the node in the compiler's view. -/
theorem compiler_read {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.compilerSource.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ index.compilerSource.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : index.compilerSource.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

/-- Header items extend the lexical context without changing its signatures. -/
theorem items_signatures {control : ControlContext} {signatures : ProgramSignatures} :
    ∀ {items : List ForItemForm} {context final : SourceSemantics.Context},
      ForItemsHaveType source control context items final →
      context.signatures = signatures → final.signatures = signatures
  | [], _, _, typed, same => by
    cases typed
    exact same
  | _ :: _, _, _, typed, same => by
    cases typed with
    | cons head tail =>
      apply items_signatures tail
      cases head with
      | letUninitialized _ _ extension => cases extension; exact same
      | letInitialized _ _ _ extension => cases extension; exact same
      | letInitializedGeneralized _ _ _ _ extension => cases extension; exact same
      | expression => exact same
      | assignValue => exact same
      | assignBitNot => exact same

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
/-! Native typing facts of the actual emitted statement code. Every flow the
compiler emits reports failure as a Word, so the initializer of a declaration
is typed at its own language result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
open Core Frontend SourceInference
open TypedLexicalWhile.Native (remove_front)

/-- Every native typing of `code` has a Word failure component. -/
def WordFailure (context : Core.Context) (code : Expr) (definitions : DataEnvironment) : Prop :=
  ∀ {type : Ty}, HasType context code type definitions → ∃ success, type = LanguageResult.resultType success

section Leaves
variable {context : Core.Context} {definitions : DataEnvironment}

theorem success_word {payload : Expr} :
    WordFailure context (LanguageResult.success payload) definitions := by
  intro type typed
  cases typed with
  | inRight => exact ⟨_, rfl⟩

theorem fallthrough_word (result : Ty) : WordFailure context (LocalLoop.fallthrough result) definitions :=
  success_word

theorem returned_word (value : Expr) : WordFailure context (LocalLoop.returned value) definitions :=
  success_word

theorem breaking_word (result : Ty) : WordFailure context (LocalLoop.breaking result) definitions :=
  success_word

theorem continuing_word (result : Ty) : WordFailure context (LocalLoop.continuing result) definitions :=
  success_word

theorem returnValue_word (result : Ty) (computation : Expr) :
    WordFailure context (LocalLoop.returnValue result computation) definitions := by
  intro type typed
  cases typed with
  | caseE _ _ returned => exact success_word returned

theorem sequence_word (result : Ty) (computation next : Expr) :
    WordFailure context (LocalLoop.sequence result computation next) definitions := by
  intro type typed
  cases typed with
  | caseE _ _ control =>
    cases control with
    | caseE _ _ transfer => exact success_word transfer

end Leaves

/-- A discarded computation keeps the continuation's exact native type. -/
theorem discard_tail {definitions : DataEnvironment} {context : Core.Context} {output result : Ty}
    {computation next : Expr}
    (typed : HasType context (LocalSequence.discard output computation next) result definitions) :
    HasType context next result definitions := by
  cases typed with
  | caseE _ _ body => exact remove_front body

/-- The marked initialized allocation reads its payload from the innermost
binder, so that binder has the request's payload type. -/
theorem allocation_payload {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (CompatibleStatementInitialized.request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (CompatibleStatementInitialized.request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {definitions : DataEnvironment} {context : Core.Context} {bound result : Ty}
    (typed : HasType (bound :: context) annotation.expression result definitions) :
    bound = payload := by
  rw [annotation.exact] at typed
  cases typed with
  | letE _ original =>
    have allocated := remove_front original
    rw [same, allocation.expressionExact] at allocated
    unfold SourceCoreAllocationLayouts.allocation at allocated
    simp only [CompatibleStatementInitialized.request] at allocated
    unfold SourceCoreHeapMarkers.allocateInitialized at allocated
    cases allocated with
    | letE initial rest =>
      cases initial with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        cases rest with
        | letE _ cell =>
          unfold OptionalCell.allocateInitialized at cell
          cases cell with
          | newCell value =>
            cases value with
            | inRight _ read =>
              cases read with
              | var found =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at found
                exact found

/-- At a Word failure component, the initializer of an emitted declaration is
typed at the language result of the declared payload. -/
theorem initialized_initializer {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (CompatibleStatementInitialized.request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (CompatibleStatementInitialized.request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {definitions : DataEnvironment} {context : Core.Context} {type success : Ty} {initializer body : Expr}
    (typed : HasType context (CompatibleStatementInitialized.sequence type initializer annotation.expression body)
      (LanguageResult.resultType success) definitions) :
    HasType context initializer (LanguageResult.resultType payload) definitions := by
  cases typed with
  | caseE initialized failure next =>
    cases failure with
    | inLeft _ reason =>
      cases reason with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        cases next with
        | letE allocated _ =>
          have bound := allocation_payload allocation annotation same allocated
          subst bound
          exact initialized

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNative
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
/-! Inputs of the accepted-body closure that are not statement flow: meaning of
the expressions the compiler actually accepted, the fault interpretation,
reached place diagnostics and identity views used by writes, and the inputs of
generalized declarations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationAcceptedTerminals (children)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

/-- Accepted-expression meaning for every child the compiler lowered, at every
compiler fuel. This is the only expression input of the statement closure. -/
def Expressions (budget : Nat) : Prop :=
  ∀ fuel context, Dynamic.SourceRuntimeValid program context index.source →
    invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
    CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget ∧
    CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index
      registry invocation (children index fuel) faults budget

/-- Write inputs shared by statements and `for` header items: the metadata
registry extension, fault interpretation of the body's own diagnostic words,
reached place diagnostics at the actual compiler sites and identity views.
Operand and unary words are interpreted only at the typed assignment
occurrences of the Source, as reached place diagnostics are: a site without a
table entry yields the zero word for both kinds of fault. -/
structure Writes where
  extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving
  operands : ∀ {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
      {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId},
    AssignmentDiagnosticOrigins.Occurs invocation.source site assignment operator rhs →
    SourceAssignmentHasType invocation.source context assignment operator rhs →
    AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token) operator
      (index.invalidOperand site assignment.target.root operator)
  unary : ∀ {context : SourceSemantics.Context} {site : SourceCoreElaboration.ErrorSite}
      {assignment : AssignmentResolution},
    GenericAssignmentUnaryDiagnostics.UnaryOccurs invocation.source site assignment →
    SourceBitNotAssignmentValid invocation.source context assignment →
    faults (.semantic (.invalidUnaryOperand .bitNot)) (index.invalidUnary site assignment.target.root)
  identities : Dynamic.Value → Word → Prop
  faithful : DataEquality.IdentityFaithful identities
  observations : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities
  functionTypes : CompatiblePayload.FunctionRuntimeViews functions
  placeDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol invocation.source
    index.invalidProjection index.missingDefault receiving (fun reason token => faults (.semantic reason) token)

/-- Inputs of generalized declarations: the captured-scope descriptor
attachment, the residual entry of a contextual invocation (trivial for named
rows), and the body's diagnostic issuer at every generalized initializer. -/
structure Generalized : Prop where
  attachment : attachment = GeneralizedLocalCapturedScopes.Attachment
  entry : index.ResidualEntry
  issuer : ∀ fuel scope initializer, GeneralizedLocalDiagnosticIssuer.Receipt whole.indexed
    (index.initializerInputs fuel scope initializer index.reasonAt)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
/-! The accepted bare-assignment and bit-not receipts of an actual body supply
the flow heads used by the mixed-cell write theorems. A right-hand side
certificate is the compiler's own child lowering; checker typing supplies
writability, and diagnostic words come from the body's own fault tables. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
open Core Frontend SourceInference
open CellAwareInvocationAcceptedTerminals (children)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- The head is stated over any Source equal to the compiler's view, so it
can be used directly at the invocation's own Source. -/
theorem bare_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr}
    (receipt : AcceptedBareAssignmentReceipt.Receipt index.policy fuel index.compilerSource scope site assignment
      operator rhs output next index.reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    {context : SourceSemantics.Context} (typed : SourceAssignmentHasType target context assignment operator rhs)
    (administrative : Core.Context) :
    ∃ head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = index.invalidOperand site assignment.target.root operator := by
  subst target
  have lowered := index.assignment_lowered receipt.accepted
  obtain ⟨_, writable, rightTyped, profile⟩ :=
    ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare typed
  obtain ⟨node, found, _, _⟩ := CellAwareInvocationAcceptedSourceFacts.expression_node unique rightTyped
  exact GenericAssignmentStatements.Head.of_lower_bare_with_token receipt.bare unique writable rightTyped profile
    (fun _ generated => ⟨node, found, generated⟩) lowered

/-- Checker validity of a bare bit-not target gives its writable declaration
and Word representation. -/
theorem bitNot_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {binder : TypedBinder}
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (targetType : binder.scheme.body = assignment.target.type)
    (bare : assignment.target.projections = [])
    (typed : SourceBitNotAssignmentValid source context assignment) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) ∧
    (SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer) := by
  cases typed with
  | intro place _ =>
  cases place with
  | intro writable projections target =>
    refine ⟨?_, .inl (by rw [target]; rfl)⟩
    intro actual actualFound
    cases Except.ok.inj (declaration.symm.trans actualFound)
    rw [bare] at projections
    cases projections
    exact targetType.symm ▸ target.symm ▸ writable

/-- The accepted bare bit-not receipt supplies the unary flow head and its
diagnostic word from this body's own fault table. -/
theorem bitNot_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
    (receipt : AcceptedBareBitNotReceipt.Receipt index.policy fuel index.compilerSource scope site assignment
      output next index.reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    {context : SourceSemantics.Context} (typed : SourceBitNotAssignmentValid target context assignment) :
    ∃ head : CompatibleBitNotStatements.Head context scope assignment,
      code = head.emit next output ∧ head.invalid = index.invalidUnary site assignment.target.root := by
  subst target
  have lowered := index.bitNot_lowered receipt.selected receipt.accepted
  obtain ⟨writable, profile⟩ := bitNot_facts receipt.declaration targetType receipt.bare typed
  exact CompatibleBitNotStatements.Head.of_lower_with_token writable receipt.bare profile lowered

/-- A projected write's head retains the compiler's ordered key and right-hand
actions, its native typing and the prepared place used by reached diagnostics. -/
theorem projected_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr}
    (receipt : AcceptedProjectedAssignmentReceipt.Receipt index.policy fuel index.compilerSource scope site
      assignment operator rhs output next index.reasonAt code)
    (route : AcceptedProjectedAssignmentRoute.Route index.compilerSource receipt.binder.scheme.body
      assignment.target.projections assignment.target.type)
    {context : SourceSemantics.Context} (signatures : context.signatures = compiled.compatible.checked.signatures)
    (typed : SourceAssignmentHasType target context assignment operator rhs)
    (administrative : Core.Context) {result : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result
      compiled.indexed.layouts.definitions) :
    ∃ head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment operator rhs,
      code = head.emit next output ∧ head.invalid = index.invalidOperand site assignment.target.root operator ∧
      head.PreparedAt site fuel (index.invalidProjection site assignment.target.root)
        (index.missingDefault site assignment.target.root) := by
  subst target
  have lowered := index.assignment_lowered receipt.accepted
  obtain ⟨sourceTyped, writable, rightTyped, profile⟩ :=
    ScopedSourceForItemsAdmission.projected_assignment_facts unique receipt.description.binding route typed
  exact CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
    unique signatures sourceTyped writable rightTyped profile
    (fun id _ member generated _ => by
      rcases List.mem_cons.mp member with same | member
      · subst id
        obtain ⟨node, found, _, _⟩ := CellAwareInvocationAcceptedSourceFacts.expression_node unique rightTyped
        exact ⟨node, found, generated⟩
      · obtain ⟨node, found, _⟩ := route.key_typed unique (sourceTyped _ receipt.description.binding) member
        exact ⟨node, found, generated⟩) lowered native

theorem bitNot_word {source : TypedSource} {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    (typed : SourceBitNotAssignmentValid source context assignment) :
    SourceCoreRawMetadata.runtimeType assignment.target.type = .word := by
  cases typed with
  | intro place _ =>
  cases place with
  | intro _ _ target =>
    rw [target]
    rfl

/-- The projected unary head keeps the absent operand literal; only ordered
keys are compiler children, each certified by its own accepted lowering. -/
theorem projected_bitNot_head (index : ActualBodyInvocation.Index compiled bodyRelation) {target : TypedSource}
    (sameSource : index.compilerSource = target) (unique : NodeOccurrencesUnique target)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
    (receipt : AcceptedProjectedBitNotReceipt.Receipt index.policy fuel index.compilerSource scope site
      assignment output next index.reasonAt code)
    (route : AcceptedProjectedAssignmentRoute.Route index.compilerSource receipt.binder.scheme.body
      assignment.target.projections assignment.target.type)
    {context : SourceSemantics.Context} (signatures : context.signatures = compiled.compatible.checked.signatures)
    (typed : SourceBitNotAssignmentValid target context assignment)
    (administrative : Core.Context) {result : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result
      compiled.indexed.layouts.definitions) :
    ∃ head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) target context
        (children index fuel) scope administrative compiled.indexed.layouts.definitions assignment,
      code = head.emit next output ∧ head.invalid = index.invalidUnary site assignment.target.root ∧
      head.PreparedAt site fuel (index.invalidProjection site assignment.target.root)
        (index.missingDefault site assignment.target.root) := by
  subst target
  have lowered := index.bitNot_lowered receipt.callbackSelected receipt.accepted
  obtain ⟨sourceTyped, writable⟩ :=
    ScopedSourceForItemsAdmission.projected_bitNot_facts unique receipt.description.binding route typed
  exact CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
    unique signatures sourceTyped writable receipt.projected (.inl (bitNot_word typed))
    (fun id _ member generated _ => by
      obtain ⟨node, found, _⟩ := route.key_typed unique (sourceTyped _ receipt.description.binding) member
      exact ⟨node, found, generated⟩) lowered native

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedAssignments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
/-! The actual accepted `for` header items close the mixed-cell header flows.
Each item uses the compiler's own child lowering and allocation receipt;
header declarations are authenticated by the original compilation receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open AcceptedNamedBodyFlow (Items)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedSourceFacts (expression_node)

section Coverage
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {result : Ty} {reasonAt : ExpressionId → Word}
  {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
  {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}

/-- Header items closed below. Raw write receipts that were not refined are
outside the closure, and writes require the compiler view to be the original
Source, as for named rows. -/
def ItemsCovered (semantic : TypedSource) {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Prop :=
  match tree with
  | .nil .. => True
  | .absent _ remaining _ => ItemsCovered semantic remaining
  | @Items.initialized _ _ _ _ _ _ _ _ _ _ binder _ _ _ _ _ _ _ _ _ remaining _ =>
      binder.scheme.quantified = [] ∧ ItemsCovered semantic remaining
  | .discard _ _ remaining => ItemsCovered semantic remaining
  | .assigned remaining _ _ | .projectedAssigned remaining _ _ | .bitNotted remaining _ _
    | .projectedBitNotted remaining _ _ => source = semantic ∧ ItemsCovered semantic remaining
  | .assigning .. | .bitNotting .. => False

end Coverage

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

section Validity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

theorem post_preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope items expected type code budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope items expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem post_reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope items expected type code budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope items expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end Validity

section InitialValidity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

theorem initial_preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope items test postItems statements expected type code
        budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
      producer registry invocation faults administrative scope items test postItems statements expected type code
      budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem initial_reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope items test postItems statements expected type code
        budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
      producer registry invocation faults administrative scope items test postItems statements expected type code
      budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end InitialValidity

section Empty
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}

/-- An exhausted update list falls through at the original lexical state. -/
theorem post_empty (budget : Nat) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope [] expected type (LocalLoop.fallthrough type) budget ∧
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope [] expected type (LocalLoop.fallthrough type) budget := by
  have evaluates : ∀ (actual : Environment) (store : Store) (embedding : Renaming),
      Evaluates actual store ((LocalLoop.fallthrough type).rename embedding) (LocalLoop.fallthroughValue type) store :=
    fun actual store _ => by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store
  refine ⟨?_, ?_⟩
  · intro size _ mapping world actualContext environment canonical actual before store embedding
      _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
      initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
    cases trace
    exact ⟨_, store, mapping, world, evaluates actual store embedding, .fallthrough environment (.inl rfl), heaps,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, protocol.refl initial, admitted⟩
  · intro size _ mapping world actualContext environment canonical actual before store embedding value finalStore
      _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
      initial admitted _authority _physical _owner _sameLocation _ready completed
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (evaluates actual store embedding)
    exact ⟨_, context, .done environment, before, mapping, world, .empty, .fallthrough environment (.inl rfl), heaps,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Empty

include bindings transport registered in
/-- Induction over the accepted update items of one actual `for` statement.
The parent statement and the original compilation authenticate declarations. -/
theorem post_correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {parentId : StatementId} {statement : StatementNode}
    {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
    (parentReached : index.Reached (.statement parentId))
    (parentFound : index.compilerSource.lookupStatement? parentId = some statement)
    (parentForm : statement.form = .forLoop allInitial condition allPost bodyStatements)
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {expected : TypeSystem.Ty} :
    ∀ {fuel scope items code}
      (tree : Items index.policy index.compilerSource (.occurrence parentId.occurrence) index.result index.reasonAt
        next finalScope (LocalLoop.fallthrough index.result) fuel scope items code),
      ItemsCovered index.source tree →
      (∀ item ∈ items, item ∈ allInitial ++ allPost) →
      ∀ {control : ControlContext} {context final : SourceSemantics.Context},
        context.signatures = whole.compatible.checked.signatures →
        ForItemsHaveType index.source control context items final →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope items expected index.result code budget ∧
        CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope items expected index.result code budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  intro fuel scope items code tree
  induction tree with
  | nil same accepted =>
    intro _ _ control context final _ _ _
    exact post_empty bridge index producer registry invocation faults administrative budget
  | @absent fuel scope binder payload rest tail code projected remaining allocated tailIH =>
    intro covered members control context final signatures typed native
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    cases headTyped with
    | letUninitialized mono _ extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForPostAcceptedAllocation.absent_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.1,
      CellAwareInvocationForPostAcceptedAllocation.absent_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.2⟩
  | @initialized fuel scope binder expression payload rest tail code projected child generated childType
      remaining allocated tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨mono, covered⟩ := covered
    have monomorphic : binder.scheme.quantified.isEmpty = true := by rw [mono]; rfl
    rw [if_pos monomorphic] at allocated
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    have typedInitializer : ExpressionHasType index.source context expression binder.scheme.body ∧
        BinderExtends index.source.owner context binder middle := by
      cases headTyped with
      | letInitialized initializerTyped _ _ extension => exact ⟨initializerTyped, extension⟩
      | letInitializedGeneralized polymorphic => exact False.elim (polymorphic mono)
    obtain ⟨initializerTyped, extended⟩ := typedInitializer
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    obtain ⟨initializerNode, initializerFound, valueType, initializerTyped⟩ :=
      expression_node sourceUnique initializerTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForPostAcceptedAllocation.initialized_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).1)
        tailBounds.1,
      CellAwareInvocationForPostAcceptedAllocation.initialized_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).2)
        tailBounds.2⟩
  | @discard fuel scope expression rest tail child generated remaining tailIH =>
    intro covered members control context final signatures typed native
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | expression expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostDiscard.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostDiscard.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | assigning => intro covered; cases covered
  | @assigned fuel scope assignment operator expression rest tail code remaining receipt targetType tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.operands (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostAssignment.preserves bridge transport functions
          producer sourceEq unique head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostAssignment.reflects bridge transport functions
          producer sourceEq unique head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @projectedAssigned fuel scope assignment operator expression rest tail code remaining receipt route tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      writes.placeDiagnostics.assignment head (.header found parentForm (members _ (List.mem_cons_self ..)))
        signatures receipt.projected preparedAt sourceTyped (environment := environment) initial
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedAssignment.preserves bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations shapes budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedAssignment.reflects bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations shapes writes.functionTypes budget (expressions fuel context runtime covers ledger).2
          tailBounds.2⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted fuel scope assignment rest tail code remaining receipt targetType tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.unary (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨CellAwareInvocationForPostBitNot.preserves bridge transport functions producer head sourceEq errors
        budget tailBounds.1,
      CellAwareInvocationForPostBitNot.reflects bridge transport functions producer head sourceEq errors
        budget tailBounds.2⟩
  | @projectedBitNotted fuel scope assignment rest tail code remaining receipt route tailIH =>
    intro covered members control context final signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ =>
        exact writes.placeDiagnostics.unary head (.header found parentForm (members _ (List.mem_cons_self ..)))
          signatures preparedAt place initial
    rw [emitted]
    exact ⟨post_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedBitNot.preserves bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations reachedErrors budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      post_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForPostProjectedBitNot.reflects bridge transport
          functions producer sourceEq unique head receipt.projected writes.extension writes.faithful
          writes.observations reachedErrors writes.functionTypes budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩

include bindings transport registered in
/-- Induction over the accepted initializer items of one actual `for` statement.
The exhausted list enters the loop terminal at the final initializer context. -/
theorem initial_correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    {parentId : StatementId} {statement : StatementNode}
    {allInitial allPost : List ForItemForm} {condition : ExpressionId} {bodyStatements : List StatementId}
    (parentReached : index.Reached (.statement parentId))
    (parentFound : index.compilerSource.lookupStatement? parentId = some statement)
    (parentForm : statement.form = .forLoop allInitial condition allPost bodyStatements)
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr} {finalScope : SourceCoreLocalCell.Scope}
    {finish : Expr} {expected : TypeSystem.Ty} {test : ExpressionId} {postItems : List ForItemForm}
    {statements : List StatementId} {control : ControlContext} {loopContext : SourceSemantics.Context}
    (terminal : (∃ nativeType, HasType (SourceCoreLocalCell.coreContext finalScope ++ administrative) finish
        nativeType whole.indexed.layouts.definitions) →
      CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge loopContext model index
        producer registry invocation faults administrative finalScope [] test postItems statements expected
        index.result finish budget ∧
      CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge loopContext model index
        producer registry invocation faults administrative finalScope [] test postItems statements expected
        index.result finish budget) :
    ∀ {fuel scope items code}
      (tree : Items index.policy index.compilerSource (.occurrence parentId.occurrence) index.result index.reasonAt
        next finalScope finish fuel scope items code),
      ItemsCovered index.source tree →
      (∀ item ∈ items, item ∈ allInitial ++ allPost) →
      ∀ {context : SourceSemantics.Context},
        context.signatures = whole.compatible.checked.signatures →
        ForItemsHaveType index.source control context items loopContext →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model index
          producer registry invocation faults administrative scope items test postItems statements expected
          index.result code budget ∧
        CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model index
          producer registry invocation faults administrative scope items test postItems statements expected
          index.result code budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  intro fuel scope items code tree
  induction tree with
  | @nil fuel scope same accepted =>
    intro _ _ context _ typed native
    subst scope
    cases typed
    exact terminal native
  | @absent fuel scope binder payload rest tail code projected remaining allocated tailIH =>
    intro covered members context signatures typed native
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    cases headTyped with
    | letUninitialized mono _ extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForInitialAcceptedAllocation.absent_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.1,
      CellAwareInvocationForInitialAcceptedAllocation.absent_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        payloadProjected allocated sourceEq tailBounds.2⟩
  | @initialized fuel scope binder expression payload rest tail code projected child generated childType
      remaining allocated tailIH =>
    intro covered members context signatures typed native
    obtain ⟨mono, covered⟩ := covered
    have monomorphic : binder.scheme.quantified.isEmpty = true := by rw [mono]; rfl
    rw [if_pos monomorphic] at allocated
    cases typed with
    | @cons _ _ middle _ _ _ headTyped restTyped =>
    have typedInitializer : ExpressionHasType index.source context expression binder.scheme.body ∧
        BinderExtends index.source.owner context binder middle := by
      cases headTyped with
      | letInitialized initializerTyped _ _ extension => exact ⟨initializerTyped, extension⟩
      | letInitializedGeneralized polymorphic => exact False.elim (polymorphic mono)
    obtain ⟨initializerTyped, extended⟩ := typedInitializer
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    obtain ⟨initializerNode, initializerFound, valueType, initializerTyped⟩ :=
      expression_node sourceUnique initializerTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      nextSignatures restTyped ⟨_, tailNative⟩
    have present := members _ (List.mem_cons_self ..)
    exact ⟨CellAwareInvocationForInitialAcceptedAllocation.initialized_preserves bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).1)
        tailBounds.1,
      CellAwareInvocationForInitialAcceptedAllocation.initialized_reflects bridge bindings model index producer
        registered artifact checked parentReached parentFound parentForm present projected extended
        initializerFound valueType initializerTyped (certificates := fun _ => children index fuel) generated
        childType allocated sourceEq (fun context runtime covers ledger => (expressions fuel context runtime covers ledger).2)
        tailBounds.2⟩
  | @discard fuel scope expression rest tail child generated remaining tailIH =>
    intro covered members context signatures typed native
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | expression expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialDiscard.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialDiscard.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result (sourceEq ▸ expressionFound)
          (sourceEq ▸ expressionTyped) generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | assigning => intro covered; cases covered
  | @assigned fuel scope assignment operator expression rest tail code remaining receipt targetType tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.operands (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialAssignment.preserves bridge transport functions
          producer unique head receipt.bare (sourceEq ▸ assignmentTyped) writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialAssignment.reflects bridge transport functions
          producer unique head receipt.bare (sourceEq ▸ assignmentTyped) writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩
  | @projectedAssigned fuel scope assignment operator expression rest tail code remaining receipt route tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      writes.placeDiagnostics.assignment head (.header found parentForm (members _ (List.mem_cons_self ..)))
        signatures receipt.projected preparedAt sourceTyped (environment := environment) initial
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedAssignment.preserves bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations shapes budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedAssignment.reflects bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations shapes writes.functionTypes budget (expressions fuel context runtime covers ledger).2
          tailBounds.2⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted fuel scope assignment rest tail code remaining receipt targetType tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      have found : invocation.source.lookupStatement? parentId = some statement := by
        rw [sourceEq, ← sameSource]
        exact parentFound
      rw [invalid]
      exact writes.unary (.header found parentForm (members _ (List.mem_cons_self ..)))
        (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨CellAwareInvocationForInitialBitNot.preserves bridge transport functions producer head (sourceEq ▸ assignmentTyped) errors
        budget tailBounds.1,
      CellAwareInvocationForInitialBitNot.reflects bridge transport functions producer head (sourceEq ▸ assignmentTyped) errors
        budget tailBounds.2⟩
  | @projectedBitNotted fuel scope assignment rest tail code remaining receipt route tailIH =>
    intro covered members context signatures typed native
    obtain ⟨sameSource, covered⟩ := covered
    cases typed with
    | cons headTyped restTyped =>
    cases headTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH covered (fun item member => members item (List.mem_cons_of_mem _ member))
      signatures restTyped ⟨_, tailNative⟩
    have found : invocation.source.lookupStatement? parentId = some statement := by
      rw [sourceEq, ← sameSource]
      exact parentFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ =>
        exact writes.placeDiagnostics.unary head (.header found parentForm (members _ (List.mem_cons_self ..)))
          signatures preparedAt place initial
    rw [emitted]
    exact ⟨initial_preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedBitNot.preserves bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations reachedErrors budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      initial_reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationForInitialProjectedBitNot.reflects bridge transport
          functions producer unique head receipt.projected (sourceEq ▸ assignmentTyped) writes.extension writes.faithful
          writes.observations reachedErrors writes.functionTypes budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedForItems
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
/-! A match accepted by the actual compiler tree closes its mixed-cell flow.
The tree's match receipt supplies the certificate, the scrutinee lowering and
the finite branch requests; the enclosing tree induction supplies every branch
at its original Source context with the match's own control. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationAcceptedSourceFacts (head_form expression_node)

/-- Match compilation contexts of an actual body: the checked catalog's initial
values, the body's own marked allocator, and data definitions that the indexed
layouts extend. Both the base and the ambient callback contexts qualify. -/
def Admitted {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index whole bodyRelation)
    (compilation : SourceCoreCompatibleDataMatches.Context) : Prop :=
  compilation.values = .initial whole.compatible.checked ∧
    compilation.sourceCells = index.policy.sourceCells ∧
    compilation.definitions.Extends whole.indexed.layouts.definitions

/-- The original compilation receipt's checker run fixes a well-formed
signature catalog for the compiled program. -/
theorem catalog {whole : SourceCoreUnifiedCompilation.Compiled}
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program) :
    SignatureCatalogWellFormed whole.compatible.checked.signatures := by
  rw [CallableIndexedOwnedPublicSignatureCatalog.signatures whole,
    (SourceCoreCompiler.Compiled.artifact_fields sourceCompiled artifact).1]
  exact SignatureCatalogWellFormed.ofCheckProgram checked

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

include bindings registered in
/-- Both directions for an accepted match head followed by its actual suffix.
Branch bounds are required only at the exact compiler requests and their
original Source contexts; the hidden scrutinee and every pattern binder are
non-inputs by the runtime ownership of the body's local identities. -/
theorem correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    (catalog : SignatureCatalogWellFormed whole.compatible.checked.signatures)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {expected : TypeSystem.Ty} {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {stored : Ty}
    {resolution : MatchResolution} {matchedCode tail : Expr}
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (reached : index.Reached (.statement id))
    (read : index.policy.readStatement index.compilerSource id = .ok (node, stored))
    (form : node.form = .matchWith resolution)
    (receipt : AcceptedNamedMatchFlow.Receipt index.policy compilation index.compilerSource scope id resolution
      index.result index.reasonAt escaped fuel matchedCode)
    (admitted : Admitted index compilation) (sameSource : index.compilerSource = index.source)
    (branches : ∀ request ∈ receipt.requests, ∀ {control : ControlContext} {context final : SourceSemantics.Context}
      {facts : BodyFacts}, control.returnType = expected →
      context.signatures = whole.compatible.checked.signatures →
      StatementsHaveType index.source control context request.statements final facts →
      (∃ nativeType, HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code
        nativeType whole.indexed.layouts.definitions) →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative request.scope false request.statements expected index.result
        request.code budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative request.scope false request.statements expected index.result
        request.code budget)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (result : control.returnType = expected)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (typed : StatementsHaveType index.source control context (id :: rest) final facts)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) matchedCode nativeType
      whole.indexed.layouts.definitions)
    (tailBounds : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope mode rest expected index.result tail budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index
        producer registry invocation faults administrative scope mode rest expected index.result tail budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode (id :: rest) expected index.result
      (LocalLoop.sequence index.result matchedCode tail) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode (id :: rest) expected index.result
      (LocalLoop.sequence index.result matchedCode tail) budget := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  have statementFound := index.statement_read_reached reached read
  have statementAt : invocation.source.lookupStatement? id = some node := by
    rw [sourceEq]
    exact statementFound
  obtain ⟨_, _, formTyped, _⟩ := head_form sourceUnique typed statementFound
  rw [form] at formTyped
  have sourceFacts : ∃ type caseFacts, ExpressionHasType index.source context resolution.scrutinee type ∧
      MatchCasesHaveType index.source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType index.source control context statements last bodyFacts) := by
    cases formTyped with
    | matchWithoutDefault absent value casesTyped =>
      exact ⟨_, _, value, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present value casesTyped defaultTyped =>
      exact ⟨_, _, value, casesTyped, fun statements selected => by
        cases Option.some.inj (present.symm.trans selected)
        exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨scrutineeType, caseFacts, value, casesTyped, defaultTyped⟩ := sourceFacts
  obtain ⟨scrutineeNode, scrutineeFound, nodeType, scrutineeTyped⟩ := expression_node sourceUnique value
  subst nodeType
  have found : invocation.source.lookupExpression? resolution.scrutinee = some scrutineeNode := by
    rw [sourceEq]
    exact scrutineeFound
  have typedAt : ExpressionHasType invocation.source context resolution.scrutinee scrutineeNode.type := by
    rw [sourceEq]
    exact scrutineeTyped
  have casesAt : MatchCasesHaveType invocation.source control context scrutineeNode.type resolution.cases
      caseFacts := by
    rw [sourceEq]
    exact casesTyped
  have defaultAt : ∀ statements, resolution.defaultBody = some statements →
      ∃ last bodyFacts, StatementsHaveType invocation.source control context statements last bodyFacts := by
    rw [sourceEq]
    exact defaultTyped
  have compilerFound : index.compilerSource.lookupExpression? resolution.scrutinee = some scrutineeNode := by
    rw [sameSource]
    exact scrutineeFound
  obtain ⟨valuesEq, cellsEq, extension⟩ := admitted
  have allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      whole.indexed.ancestry.layout.frame whole.indexed.base.globals.length
      (whole.indexed.layouts.allocatorAt index.owner index.active (fun error => .sourceAllocation (reprStr error)))) :=
    cellsEq.trans index.sourceCells
  obtain ⟨nativeType, matchedNative⟩ := native
  have typedCertificate := CompatibleMatchNativeChildren.Certificate.typed_bodies_extended
    (fun error => .sourceAllocation (reprStr error)) allocator extension receipt.certificate matchedNative
  obtain ⟨requests, certificate, _, typedRequests⟩ :=
    GenericMatchChildren.Certificate.finite_children typedCertificate
  have contexts : ∀ request ∈ requests, ∀ childContext,
      GenericMatchChildren.ScopedContextFor invocation.source context
        (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases
        resolution.defaultBody request childContext →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge childContext model index
        producer registry invocation faults administrative request.scope false request.statements expected
        index.result request.code budget ∧
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge childContext model index
        producer registry invocation faults administrative request.scope false request.statements expected
        index.result request.code budget := by
    intro request member childContext related
    obtain ⟨occurs, requestNative⟩ := typedRequests request member
    obtain ⟨_, _, childTyped⟩ := ScopedSourceMatchAdmission.request_typing casesAt defaultAt related.forget
    rw [sourceEq] at childTyped
    exact branches request occurs result (related.closed_fields.1.trans signatures) childTyped ⟨_, requestNative⟩
  cases compilation with
  | mk values solved sourceCells ambientDefinitions =>
  dsimp only at valuesEq
  subst valuesEq
  refine ⟨?_, ?_⟩
  · intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admission authority
      physical owner sameLocation ready finalContext outcome after trace
    obtain ⟨hiddenOrdinary, armsOrdinary⟩ :=
      ScopedSourceMatchAdmission.ordinary_bindings physical.ownership statementFound form
    have ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids certificate
      (index.compiler_noninput hiddenOrdinary)
      (fun arm member binder bound => index.compiler_noninput (armsOrdinary arm member binder bound))
    refine CellAwareInvocationMatchSequences.preserves bridge functions index producer sourceEq ?_ unique
      statementAt form (.inl tailBounds.1) within environments heaps locals agrees actualTyped sourceTyped
      runtime covers sameLedger initial admission authority physical owner sameLocation ready trace
    intro innerSize innerWithin
    exact CellAwareInvocationMatchTreeHeads.preserves bridge functions index
      (fun error => .sourceAllocation (reprStr error)) allocator rfl registered writes.extension certificate
      ordinary signatures catalog found typedAt sourceEq compilerFound rfl statementFound form casesAt defaultAt
      budget producer bindings unique
      (by
        intro childSize smaller childScope expression lowered certified
        rcases certified with ⟨rfl, rfl, rfl⟩
        exact (expressions receipt.childFuel context runtime covers sameLedger).1 childSize smaller
          receipt.generated)
      (fun request member childContext related _ => (contexts request member childContext related).1) innerWithin
  · intro size within mapping world actualContext environment canonical actual before store embedding value
      finalStore environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admission
      authority physical owner sameLocation ready completed
    obtain ⟨hiddenOrdinary, armsOrdinary⟩ :=
      ScopedSourceMatchAdmission.ordinary_bindings physical.ownership statementFound form
    have ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids certificate
      (index.compiler_noninput hiddenOrdinary)
      (fun arm member binder bound => index.compiler_noninput (armsOrdinary arm member binder bound))
    refine CellAwareInvocationMatchSequences.reflects bridge functions index producer sourceEq ?_
      statementAt form (.inl tailBounds.2) within environments heaps locals agrees actualTyped sourceTyped
      runtime covers sameLedger initial admission authority physical owner sameLocation ready completed
    intro innerSize innerWithin
    exact CellAwareInvocationMatchTreeHeads.reflects bridge functions index
      (fun error => .sourceAllocation (reprStr error)) allocator rfl registered writes.extension certificate
      ordinary signatures catalog found typedAt sourceEq compilerFound rfl statementFound form casesAt defaultAt
      budget producer bindings
      (by
        intro childSize smaller childScope expression lowered certified
        rcases certified with ⟨rfl, rfl, rfl⟩
        exact (expressions receipt.childFuel context runtime covers sameLedger).2 childSize smaller
          receipt.generated)
      (fun request member childContext related _ => (contexts request member childContext related).2) innerWithin

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMatches
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
/-! The actual accepted compiler tree closes the mixed-cell statement flows.
Every child is the action run by the compiler at its original source, scope and
fuel. Fixed-control checker typing supplies the Source facts; expression
meaning is supplied for exactly the expressions the compiler accepted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open AcceptedNamedBodyFlow (Tree)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedSourceFacts (head_form expression_node)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

section Coverage
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {result : Ty}
  {reasonAt : ExpressionId → Word}

/-- A generalized declaration's initializer is a direct lambda without
requirements or coercions. -/
def LambdaInitializer (semantic : TypedSource) (expression : ExpressionId) : Prop :=
  ∀ node, semantic.lookupExpression? expression = some node →
    (∃ parameters result body, node.form = .lambda parameters result body) ∧
      node.requirements = [] ∧ node.coercions = []

/-- Compiler branches whose statement flow is closed below. Function-mode
fallthrough is admitted only at a Unit result, and a final bare value only at
the declared result type of its original node. A nonfinal bare value in
function mode has no Source rule and is outside this closure. Bare and
projected assignments and bit-not updates are closed when the compiler view is
the original Source, as for named rows. A match receipt is closed under the
same view when its compilation context is `admitted`, and a generalized
declaration when its inputs are `generalized` and its initializer is a direct
lambda. -/
def Covered (semantic : TypedSource) (expected : TypeSystem.Ty)
    (admitted : SourceCoreCompatibleDataMatches.Context → Prop) (generalized : Prop)
    {mode : Bool} {escaped : Word} {fuel scope statements code}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code) : Prop :=
  match tree with
  | .nil => mode = false ∨ expected = .unit
  | .returning .. | .returnUnit .. | .breaking .. | .continuing .. => True
  | @Tree.tailValue _ _ _ _ _ _ _ _ _ _ expression _ _ _ _ _ _ =>
      ∀ node, semantic.lookupExpression? expression = some node → node.type = expected
  | @Tree.initialized _ _ _ _ _ _ _ _ _ _ _ _ binder expression _ _ _ _ _ _ _ _ _ _ remaining _ =>
      (binder.scheme.quantified = [] ∨ generalized ∧ LambdaInitializer semantic expression) ∧
        Covered semantic expected admitted generalized remaining
  | .absent _ _ _ _ remaining _ => Covered semantic expected admitted generalized remaining
  | .assigned _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .bitNotted _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .projectedAssigned _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .projectedBitNotted _ _ _ remaining _ _ =>
      source = semantic ∧ Covered semantic expected admitted generalized remaining
  | .discard _ _ _ _ _ tail => Covered semantic expected admitted generalized tail
  | .valueDiscard _ _ _ _ _ _ tail => mode = false ∧ Covered semantic expected admitted generalized tail
  | .block _ _ inner tail =>
      Covered semantic expected admitted generalized inner ∧ Covered semantic expected admitted generalized tail
  | .conditional _ _ _ _ _ left right tail =>
      Covered semantic expected admitted generalized left ∧
        Covered semantic expected admitted generalized right ∧ Covered semantic expected admitted generalized tail
  | @Tree.matched _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ compilation _ _ _ branches tail =>
      admitted compilation ∧ source = semantic ∧
        (∀ request member, Covered semantic expected admitted generalized (branches request member)) ∧
        Covered semantic expected admitted generalized tail
  | .whileLoop _ _ _ _ _ _ inner tail =>
      Covered semantic expected admitted generalized inner ∧ Covered semantic expected admitted generalized tail
  | .forLoop _ _ _ _ _ _ initial inner after tail =>
      CellAwareInvocationAcceptedForItems.ItemsCovered semantic initial ∧
        Covered semantic expected admitted generalized inner ∧
        CellAwareInvocationAcceptedForItems.ItemsCovered semantic after ∧
        Covered semantic expected admitted generalized tail
  | _ => False

end Coverage

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- At a Word failure component, the bundle initializer of a snapshot
declaration is typed at the language result of the declared payload. -/
private theorem snapshot_initializer {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (CompatibleStatementInitialized.request source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (CompatibleStatementInitialized.request source scope binder payload))
    (same : annotation.original = allocation.expression)
    {copySource : TypedSource} {definitions : DataEnvironment} {context : Core.Context} {type success : Ty}
    {initializer captured body : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      copySource scope (fun index => index) (snapshotInner payload initializer annotation.expression) = .ok captured)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (cellPayload : Ty), scope[index]? = some (id, cellPayload) →
      context[index]? = some (.cell (OptionalCell.cellType cellPayload)))
    (typed : HasType context (snapshotSequence type captured body) (LanguageResult.resultType success) definitions) :
    HasType context initializer (LanguageResult.resultType payload) definitions := by
  unfold snapshotSequence LanguageResult.bind at typed
  cases typed with
  | caseE capturedTyped failure _ =>
    cases failure with
    | inLeft _ reason =>
      cases reason with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        have inner := CaptureCopyTyping.copyScopeIndexed_body_hasType copied slots capturedTyped
        unfold snapshotInner LanguageResult.bind LanguageResult.success at inner
        cases inner with
        | caseE initializerTyped innerFailure allocated =>
          cases innerFailure with
          | inLeft _ innerReason =>
            cases innerReason with
            | var innerFound =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at innerFound
              subst innerFound
              cases allocated with
              | inRight _ allocationTyped =>
                have bound := CellAwareInvocationAcceptedNative.allocation_payload allocation annotation same
                  allocationTyped
                subst bound
                exact initializerTyped

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

section Validity
variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {budget : Nat}

/-- Runtime validity of the fixed Source context is part of every flow port. -/
theorem preserves_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope mode statements expected type code budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode statements expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

theorem reflects_of_valid
    (bound : Dynamic.SourceRuntimeValid program context index.source → invocation.evidence.Covers context →
      context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
        registry invocation faults administrative scope mode statements expected type code budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
      registry invocation faults administrative scope mode statements expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
  exact bound runtime covers sameLedger size within environments heaps locals agrees actualTyped runtime covers sameLedger

end Validity

include bindings transport registered in
/-- Induction over the actual compiler tree. Each covered branch applies its
existing flow theorem to the compiler's read, lowered children and allocation
receipt; nested statement lists inherit reachability, checker typing and native
typing from the enclosing compiled code. -/
theorem correct (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {expected : TypeSystem.Ty} :
    ∀ {mode escaped fuel scope statements code}
      (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope statements code),
      Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
        (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) tree →
      (∀ id ∈ statements, index.Site (.statement id)) →
      ∀ {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts},
        control.returnType = expected →
        context.signatures = whole.compatible.checked.signatures →
        StatementsHaveType index.source control context statements final facts →
        (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget ∧
        CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer
          registry invocation faults administrative scope mode statements expected index.result code budget ∧
        CellAwareInvocationAcceptedNative.WordFailure (SourceCoreLocalCell.coreContext scope ++ administrative) code
          whole.indexed.layouts.definitions := by
  have sourceUnique : NodeOccurrencesUnique index.source := sourceEq ▸ unique
  have catalog := CellAwareInvocationAcceptedMatches.catalog artifact checked
  intro mode escaped fuel scope statements code tree
  induction tree with
  | nil =>
    intro allowed _ control context final facts _ _ _ _
    exact ⟨fun size _ => CellAwareInvocationEmptyFlow.preserves bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size,
      fun size _ => CellAwareInvocationEmptyFlow.reflects bridge context model index producer
        registry invocation faults administrative _ _ expected index.result allowed size,
      CellAwareInvocationAcceptedNative.fallthrough_word _⟩
  | @returning mode escaped fuel scope id rest node stored expression read form statementType child generated childType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | returnValue valueTyped =>
    obtain ⟨expressionNode, expressionFound, valueType, expressionTyped⟩ :=
      expression_node sourceUnique valueTyped
    rw [result] at valueType
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode (id :: rest) :=
      .returning rest (sourceEq ▸ lookupStatement?_sound statementFound) form
    rw [ensure_eq childType, ← valueType]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.preserves bridge producer unique head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).1),
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.reflects bridge producer head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).2),
      CellAwareInvocationAcceptedNative.returnValue_word _ _⟩
  | @returnUnit mode escaped fuel scope id rest node stored read form statementType unitType =>
    intro _ reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | returnUnit unitResult =>
    have resultUnit : index.result = .unit := (ensure_eq statementType).trans (ensure_eq unitType).symm
    rw [← result, unitResult, resultUnit]
    have found := sourceEq ▸ statementFound
    exact ⟨fun size _ => CellAwareInvocationScopedTerminalFlow.unit_preserves bridge producer
        (fun _ _ => CompatiblePayload.ValueRep.unit) found form unique size,
      fun size _ => CellAwareInvocationScopedTerminalFlow.unit_reflects bridge producer
        (fun _ _ => CompatiblePayload.ValueRep.unit) found form size,
      CellAwareInvocationAcceptedNative.returned_word _⟩
  | @initialized mode escaped fuel scope id rest node stored binder initializer payload tail code
      read form statementType projected child generated childType remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨shape, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    have payloadEq : payload = child.type := ensure_eq childType
    subst payloadEq
    obtain ⟨nativeType, native⟩ := native
    by_cases mono : binder.scheme.quantified = []
    · have monomorphic : binder.scheme.quantified.isEmpty = true := by rw [mono]; rfl
      rw [if_pos monomorphic] at allocated
      obtain ⟨allocation, annotation, same, emitted⟩ := index.let_initialized_receipt allocated
      have tailNative := TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ native)
      have typedInitializer : ExpressionHasType index.source context initializer binder.scheme.body ∧
          BinderExtends index.source.owner context binder middle := by
        cases formTyped with
        | letInitialized initializerTyped _ extension => exact ⟨initializerTyped, extension⟩
        | letInitializedGeneralized polymorphic => exact False.elim (polymorphic mono)
      obtain ⟨initializerTyped, extended⟩ := typedInitializer
      have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
        cases extended
        exact signatures
      obtain ⟨initializerNode, initializerFound, valueType, initializerTyped⟩ :=
        expression_node sourceUnique initializerTyped
      have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
        result nextSignatures restTyped ⟨_, tailNative⟩
      exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
          fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.preserves bridge bindings model
            index producer registered registry invocation faults headReached.reached read form mono extended
            childType allocated sourceEq initializerFound valueType initializerTyped generated budget
            (expressions fuel context runtime covers ledger).1 tailBounds.1,
        reflects_of_valid bridge index producer registry invocation faults administrative
          fun runtime covers ledger => CellAwareInvocationOrdinaryAcceptedAllocation.reflects bridge bindings model
            index producer registered registry invocation faults headReached.reached read form mono extended
            childType allocated sourceEq initializerFound valueType initializerTyped generated budget
            (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
        by
          intro _ typed
          exact tailBounds.2.2 (TypedLexicalWhile.Native.initialized_child allocation annotation same (emitted ▸ typed))⟩
    · have generalizedBinder : binder.scheme.quantified.isEmpty = false := by
        cases quantified : binder.scheme.quantified with
        | nil => exact absurd quantified mono
        | cons _ _ => rfl
      simp only [generalizedBinder, Bool.false_eq_true, ↓reduceIte] at allocated
      obtain ⟨allocation, annotation, same, captured, copied, emitted⟩ :=
        index.let_initialized_snapshot_receipt allocated
      have slots : ∀ (slot : Nat) (slotId : Resolved.LocalId) (cellPayload : Ty),
          scope[slot]? = some (slotId, cellPayload) →
          (SourceCoreLocalCell.coreContext scope ++ administrative)[slot]? =
            some (.cell (OptionalCell.cellType cellPayload)) :=
        fun _ _ _ found => CellAwareGeneralizedSnapshotTyping.scope_cell found
      have tailNative := (CellAwareGeneralizedSnapshotTyping.snapshot_children allocation annotation same copied slots
        (emitted ▸ native)).2
      obtain ⟨generalized, lambdaShape⟩ := shape.resolve_left mono
      have typedInitializer : ExpressionHasType index.source (localSchemeInitializerContext context binder)
            initializer binder.scheme.body ∧ BinderExtends index.source.owner context binder middle := by
        cases formTyped with
        | letInitialized _ monomorphic _ => exact False.elim (mono monomorphic)
        | letInitializedGeneralized _ _ _ initializerTyped extension => exact ⟨initializerTyped, extension⟩
      obtain ⟨initializerTyped, extended⟩ := typedInitializer
      have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
        cases extended
        exact signatures
      obtain ⟨initializerNode, initializerFound, valueType, _⟩ := expression_node sourceUnique initializerTyped
      obtain ⟨⟨parameters, lambdaResult, lambdaBody, initializerForm⟩, requirements, coercions⟩ :=
        lambdaShape initializerNode initializerFound
      have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
        result nextSignatures restTyped ⟨_, tailNative⟩
      have word : CellAwareInvocationAcceptedNative.WordFailure (SourceCoreLocalCell.coreContext scope ++ administrative)
          code whole.indexed.layouts.definitions := by
        intro _ typed
        exact tailBounds.2.2 (CellAwareGeneralizedSnapshotTyping.snapshot_children allocation annotation same copied
          slots (emitted ▸ typed)).2
      obtain ⟨success, nativeEq⟩ := word native
      subst nativeEq
      rw [emitted] at native
      have nativeTyped := snapshot_initializer allocation annotation same copied slots native
      obtain ⟨attachmentEq, entry, issuer⟩ := generalized
      subst attachmentEq
      refine ⟨?_, ?_, word⟩
      · intro size within mapping world actualContext environment canonical actual before store embedding
          environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
          initial admitted authority physical owner sameLocation ready finalContext outcome after trace
        obtain ⟨_, declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership statementFound form
        exact CellAwareInvocationGeneralizedAcceptedAllocation.preserves bridge bindings model index producer
          registered registry invocation faults (artifact := artifact) (checked := checked) (entry := entry)
          (site := headReached) (read := read) (form := form) (projected := projected) (generated := generated)
          (issuer := issuer fuel scope initializer) (declaration := declaration) (polymorphic := mono)
          (extended := extended) (ordinary := ordinary) (nativeTyped := nativeTyped) (childType := childType)
          (allocated := allocated) (sourceEq := sourceEq) budget tailBounds.1 size within environments heaps
          locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner
          sameLocation ready trace
      · intro size within mapping world actualContext environment canonical actual before store embedding value
          finalStore environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
          initial admitted authority physical owner sameLocation ready completed
        obtain ⟨_, declaration, ordinary⟩ := SourceLetDeclarationFacts.of_lookup physical.ownership statementFound form
        exact CellAwareInvocationGeneralizedAcceptedAllocation.reflects bridge bindings model index producer
          registered registry invocation faults (artifact := artifact) (checked := checked) (entry := entry)
          (site := headReached) (read := read) (form := form) (projected := projected) (generated := generated)
          (issuer := issuer fuel scope initializer) (declaration := declaration) (polymorphic := mono)
          (extended := extended) (ordinary := ordinary) (nativeTyped := nativeTyped) (childType := childType)
          (allocated := allocated) (sourceEq := sourceEq) (initializerFound := initializerFound)
          (initializerForm := initializerForm) (valueType := valueType) (requirements := requirements)
          (coercions := coercions) budget tailBounds.2.1 size within environments heaps locals agrees actualTyped
          runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
  | @absent mode escaped fuel scope id rest node stored binder payload tail code
      read form statementType projected remaining allocated tailIH =>
    intro covered reached control context final facts result signatures typed native
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | letUninitialized mono extended =>
    have nextSignatures : middle.signatures = whole.compatible.checked.signatures := by
      cases extended
      exact signatures
    have payloadProjected := CellAwareInvocationAcceptedSourceFacts.binder_projected index mono projected
    obtain ⟨allocation, annotation, same, emitted⟩ := index.let_uninitialized_receipt allocated
    obtain ⟨_, native⟩ := native
    have tailNative := TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ native)
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result nextSignatures restTyped ⟨_, tailNative⟩
    exact ⟨CellAwareInvocationAbsentAcceptedAllocation.preserves bridge bindings model index producer registered
        registry invocation faults headReached.reached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.1,
      CellAwareInvocationAbsentAcceptedAllocation.reflects bridge bindings model index producer registered
        registry invocation faults headReached.reached read form mono extended allocated sourceEq payloadProjected
        budget tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedLexicalWhile.Native.absent_child allocation annotation same (emitted ▸ typed))⟩
  | assigning => intro covered; cases covered
  | @assigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignValue assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bare_head index
      (sameSource.trans sourceEq.symm) unique receipt targetType (sourceEq ▸ assignmentTyped) administrative
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have token : AssignmentOperandDiagnostics.OperandsLaw (fun reason token => faults (.semantic reason) token)
        operator head.invalid := by
      have found : invocation.source.lookupStatement? id = some node := sourceEq ▸ statementFound
      rw [invalid]
      exact writes.operands (.statement found form) (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationBareAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique (sourceEq ▸ statementFound) form head receipt.bare writes.extension token budget
          (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @projectedAssigned mode escaped fuel scope id rest node stored assignment operator expression tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignValue assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have found := sourceEq ▸ statementFound
    have shapes := fun (sourceTyped : SourceAssignmentHasType invocation.source context assignment operator expression)
        {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
        (initial : protocol.State initialIndex) =>
      writes.placeDiagnostics.assignment head (.statement found form) signatures receipt.projected preparedAt sourceTyped
        (environment := environment) initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations shapes budget
          (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedAssignmentFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations shapes
          writes.functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | bitNotting => intro covered; cases covered
  | @bitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt targetType tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨head, emitted, invalid⟩ := CellAwareInvocationAcceptedAssignments.bitNot_head index
      (sameSource.trans sourceEq.symm) receipt targetType (sourceEq ▸ assignmentTyped)
    obtain ⟨_, native⟩ := native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have errors : head.Errors (fun reason token => faults (.semantic reason) token) := by
      show faults (.semantic (.invalidUnaryOperand .bitNot)) head.invalid
      have found : invocation.source.lookupStatement? id = some node := sourceEq ▸ statementFound
      rw [invalid]
      exact writes.unary (.statement found form) (sourceEq ▸ assignmentTyped)
    rw [emitted]
    exact ⟨CellAwareInvocationBareBitNotFlow.preserves bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.1,
      CellAwareInvocationBareBitNotFlow.reflects bridge transport functions producer head sourceEq unique
        (sourceEq ▸ statementFound) form errors budget tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @projectedBitNotted mode escaped fuel scope id rest node stored assignment tail code
      read form statementType remaining receipt route tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨sameSource, tailCovered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | assignBitNot assignmentTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨head, emitted, invalid, preparedAt⟩ := CellAwareInvocationAcceptedAssignments.projected_bitNot_head index
      (sameSource.trans sourceEq.symm) unique receipt route signatures (sourceEq ▸ assignmentTyped) administrative native
    have tailNative := TypedImperative.Native.execute_continuation (emitted ▸ native)
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have found := sourceEq ▸ statementFound
    have reachedErrors : SourceBitNotAssignmentValid invocation.source context assignment →
        ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
          (initial : protocol.State initialIndex),
          CompatibleProjectedBitNotStatements.Head.ReachedErrors (values := .initial whole.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions whole.indexed) functions protocol head environment
            initial (fun reason token => faults (.semantic reason) token) (registry := receiving) := by
      intro sourceTyped environment initialIndex initial
      cases sourceTyped with
      | intro place _ => exact writes.placeDiagnostics.unary head (.statement found form) signatures preparedAt place initial
    rw [emitted]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.preserves bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations reachedErrors
          budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationProjectedBitNotFlow.reflects bridge transport functions
          producer sourceEq unique found form head receipt.projected writes.extension writes.faithful writes.observations reachedErrors
          writes.functionTypes budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (TypedImperative.Native.execute_continuation typed)⟩
  | @discard mode escaped fuel scope id rest node stored expression tail read form child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionDiscard expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.preserves bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inl rfl) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.reflects bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inl rfl) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (CellAwareInvocationAcceptedNative.discard_tail typed)⟩
  | @tailValue escaped fuel scope id node stored expression read form child generated statementType childType =>
    intro covered reached control context final facts result signatures typed _
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, _restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionValue expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    have valueType : expressionNode.type = expected := covered expressionNode expressionFound
    have head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression true [id] :=
      .tail (sourceEq ▸ lookupStatement?_sound statementFound) form
    rw [ensure_eq childType, ← valueType]
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.preserves bridge producer unique head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).1),
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationScopedTerminalFlow.reflects bridge producer head
          (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped) generated budget
          ((expressions fuel context runtime covers ledger).2),
      CellAwareInvocationAcceptedNative.returnValue_word _ _⟩
  | @valueDiscard mode escaped fuel scope id rest node stored expression tail read form notTail child generated statementType remaining tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨modeFalse, covered⟩ := covered
    have statementFound := index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | expressionValue expressionTyped =>
    obtain ⟨expressionNode, expressionFound, _, expressionTyped⟩ := expression_node sourceUnique expressionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨_, tailNative⟩ := TypedLexicalWhile.Native.discard_child native
    have tailBounds := tailIH covered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.preserves bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inr modeFalse) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationDiscardFlow.reflects bridge context model index producer
          registry invocation faults administrative scope mode expected index.result sourceEq unique
          (sourceEq ▸ statementFound) form (.inr modeFalse) (sourceEq ▸ expressionFound) (sourceEq ▸ expressionTyped)
          generated budget (expressions fuel context runtime covers ledger).2 tailBounds.2.1,
      by
          intro _ typed
          exact tailBounds.2.2 (CellAwareInvocationAcceptedNative.discard_tail typed)⟩
  | @block mode escaped fuel scope id rest node stored statements innerCode tail read form inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    cases formTyped with
    | block innerTyped =>
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, innerNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have innerReached : ∀ other ∈ statements, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached result signatures innerTyped ⟨_, innerNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    exact ⟨CellAwareInvocationBlockFlow.preserves bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.1 tailBounds.1,
      CellAwareInvocationBlockFlow.reflects bridge context model index producer registry invocation faults
        administrative scope mode expected index.result sourceEq unique (sourceEq ▸ statementFound) form budget
        innerBounds.2.1 tailBounds.2.1,
      CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | @conditional mode escaped fuel scope id rest node stored condition thenBody elseBody thenCode elseCode tail
      read form child generated conditionType left right remaining leftIH rightIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨leftCovered, rightCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, branchNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    obtain ⟨⟨_, thenNative⟩, ⟨_, elseNative⟩⟩ := TypedLexicalWhile.Native.conditional_children branchNative
    have thenReached : ∀ other ∈ thenBody, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have elseReached : ∀ other ∈ elseBody.getD [], index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have tailReached : ∀ other ∈ rest, index.Site (.statement other) := fun other member =>
      reached other (List.mem_cons_of_mem _ member)
    rw [form] at formTyped
    have branches : ∃ conditionTyped : ExpressionHasType index.source context condition .bool,
        (∃ thenFinal thenFacts, StatementsHaveType index.source control context thenBody thenFinal thenFacts) ∧
        (∃ elseFinal elseFacts, StatementsHaveType index.source control context (elseBody.getD []) elseFinal elseFacts) ∧
        middle = context := by
      cases formTyped with
      | ifWithoutElse conditionTyped thenTyped => exact ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, .nil _ _⟩, rfl⟩
      | ifWithElse conditionTyped thenTyped elseTyped => exact ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, elseTyped⟩, rfl⟩
    obtain ⟨conditionTyped, ⟨_, _, thenTyped⟩, ⟨_, _, elseTyped⟩, sameMiddle⟩ := branches
    subst middle
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    have leftBounds := leftIH leftCovered thenReached result signatures thenTyped ⟨_, thenNative⟩
    have rightBounds := rightIH rightCovered elseReached result signatures elseTyped ⟨_, elseNative⟩
    have tailBounds := tailIH tailCovered tailReached result signatures restTyped ⟨_, tailNative⟩
    exact ⟨preserves_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationConditionalFlow.preserves bridge context model index producer
          registry invocation faults administrative scope expected index.result
          (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
          (sourceEq ▸ conditionFound) nodeType (sourceEq ▸ conditionTyped) generated sourceEq unique
          (sourceEq ▸ statementFound) form budget (expressions fuel context runtime covers ledger).1
          leftBounds.1 rightBounds.1 tailBounds.1,
      reflects_of_valid bridge index producer registry invocation faults administrative
        fun runtime covers ledger => CellAwareInvocationConditionalFlow.reflects bridge context model index producer
          registry invocation faults administrative scope expected index.result
          (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
          (sourceEq ▸ conditionFound) nodeType (sourceEq ▸ conditionTyped) generated sourceEq unique
          (sourceEq ▸ statementFound) form budget (expressions fuel context runtime covers ledger).2
          leftBounds.2.1 rightBounds.2.1 tailBounds.2.1,
      CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | matching => intro covered; cases covered
  | @matched mode escaped fuel scope id rest node stored resolution matchedCode tail compilation
      read form receipt branches remaining branchIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨admitted, sameSource, branchesCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    rw [form] at formTyped
    have sameMiddle : middle = context := by cases formTyped <;> rfl
    subst middle
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, matchedNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have branchReached : ∀ request (member : request ∈ receipt.requests),
        ∀ other ∈ request.statements, index.Site (.statement other) := by
      intro request member other otherMember
      apply headReached.statement_source_child statementFound
      rw [form]
      simp only [StatementForm.references, MatchResolution.references]
      rcases receipt.original request member with ⟨arm, armMember, same⟩ | same
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨arm, armMember, List.mem_map.mpr ⟨other, same ▸ otherMember, rfl⟩⟩))
      · rw [same, Option.getD_some]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨other, otherMember, rfl⟩)
    have matchBounds := CellAwareInvocationAcceptedMatches.correct bridge bindings index producer registered
      registry invocation faults administrative budget expressions writes catalog sourceEq unique headReached.reached
      read form receipt admitted sameSource
      (by
        intro request member _ _ _ _ childResult childSignatures childTyped childNative
        have branchBounds := branchIH request member (branchesCovered request member) (branchReached request member)
          childResult childSignatures childTyped childNative
        exact ⟨branchBounds.1, branchBounds.2.1⟩)
      result signatures typed ⟨_, matchedNative⟩ ⟨tailBounds.1, tailBounds.2.1⟩
    exact ⟨matchBounds.1, matchBounds.2, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
  | @whileLoop mode escaped fuel scope id rest node stored condition body loopCode tail read form statementType
      child generated conditionType inner remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨innerCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    rw [form] at formTyped
    cases formTyped with
    | whileLoop conditionTyped bodyTyped =>
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, loopNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    obtain ⟨⟨_, bodyNative⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopNative
    have innerReached : ∀ other ∈ body, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have innerBounds := innerIH innerCovered innerReached (control := control.enterLoop) result signatures bodyTyped
      ⟨_, bodyNative⟩
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    refine ⟨?_, ?_, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
    · intro size within mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready finalContext outcome after trace
      exact CellAwareInvocationLoopSequences.preserves bridge model producer transport
        (fun represented => CompatibleExpressionPrimitives.bool_fields represented) sourceEq
        (expressions fuel context runtime covers sameLedger).1 (sourceEq ▸ conditionFound) nodeType
        (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.1 unique (sourceEq ▸ statementFound) form
        tailBounds.1 within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace
    · intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
      exact CellAwareInvocationLoopSequences.reflects bridge model producer transport
        (fun represented => CompatibleExpressionPrimitives.bool_fields represented) sourceEq
        (expressions fuel context runtime covers sameLedger).2 (sourceEq ▸ conditionFound) nodeType
        (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.2.1 (sourceEq ▸ statementFound) form
        tailBounds.2.1 within environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
  | @breaking mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.breaking_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.breaking_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size,
      CellAwareInvocationAcceptedNative.breaking_word _⟩
  | @continuing mode escaped fuel scope id rest node stored read form statementType =>
    intro _ reached control context final facts _ _ _ _
    have found := sourceEq ▸ index.statement_read_reached (reached id (List.mem_cons_self ..)).reached read
    exact ⟨fun size _ => CellAwareInvocationTransferFlow.continuing_preserves bridge context model index producer
        registry invocation faults administrative scope mode expected index.result unique found form size,
      fun size _ => CellAwareInvocationTransferFlow.continuing_reflects bridge context model index producer
        registry invocation faults administrative scope mode expected index.result found form size,
      CellAwareInvocationAcceptedNative.continuing_word _⟩
  | @forLoop mode escaped fuel scope id rest node stored initializer condition post body loopScope postScope
      loopCode postCode initialCode tail read form statementType child generated conditionType initial inner after
      remaining innerIH tailIH =>
    intro covered reached control context final facts result signatures typed native
    obtain ⟨initialCovered, innerCovered, afterCovered, tailCovered⟩ := covered
    have headReached := reached id (List.mem_cons_self ..)
    have statementFound := index.statement_read_reached headReached.reached read
    have compilerFound := CellAwareInvocationAcceptedSourceFacts.compiler_read index read
    obtain ⟨middle, restFacts, formTyped, restTyped⟩ := head_form sourceUnique typed statementFound
    cases child with
    | mk childType childCode =>
    have boolType := ensure_eq conditionType
    dsimp only at boolType
    subst boolType
    rw [form] at formTyped
    cases formTyped with
    | @forLoop _ _ _ _ loopContext _ _ _ initialTyped conditionTyped bodyTyped postTyped =>
    have loopSignatures := CellAwareInvocationAcceptedSourceFacts.items_signatures initialTyped signatures
    obtain ⟨conditionNode, conditionFound, nodeType, conditionTyped⟩ := expression_node sourceUnique conditionTyped
    obtain ⟨_, native⟩ := native
    obtain ⟨⟨_, initialNative⟩, ⟨_, tailNative⟩⟩ := TypedLexicalWhile.Native.sequence_children native
    have innerReached : ∀ other ∈ body, index.Site (.statement other) := fun other member =>
      headReached.statement_source_child statementFound (by rw [form]; simp [StatementForm.references, member])
    have tailBounds := tailIH tailCovered (fun other member => reached other (List.mem_cons_of_mem _ member))
      result signatures restTyped ⟨_, tailNative⟩
    have terminal : (∃ nativeType, HasType (SourceCoreLocalCell.coreContext loopScope ++ administrative)
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) nativeType
          whole.indexed.layouts.definitions) →
        CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge loopContext model index
          producer registry invocation faults administrative loopScope [] condition post body expected index.result
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) budget ∧
        CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge loopContext model index
          producer registry invocation faults administrative loopScope [] condition post body expected index.result
          (LocalLoop.iterate index.result childCode loopCode postCode escaped) budget := by
      intro loopNative
      obtain ⟨_, loopNative⟩ := loopNative
      obtain ⟨⟨_, bodyNative⟩, ⟨_, postNative⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children loopNative
      have innerBounds := innerIH innerCovered innerReached (control := control.enterLoop) result loopSignatures
        bodyTyped ⟨_, bodyNative⟩
      have postBounds := CellAwareInvocationAcceptedForItems.post_correct (expected := expected) bridge bindings
        transport index producer registered registry invocation faults administrative budget expressions writes sourceEq
        unique artifact checked
        headReached.reached compilerFound form after afterCovered (fun item member => List.mem_append_right _ member)
        loopSignatures postTyped ⟨_, postNative⟩
      exact ⟨CellAwareInvocationAcceptedForItems.initial_preserves_of_valid bridge index producer registry invocation
          faults administrative fun runtime covers ledger => CellAwareInvocationForInitialTerminal.preserves bridge
            model producer transport (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
            (expressions fuel _ runtime covers ledger).1 (sourceEq ▸ conditionFound) nodeType
            (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.1 postBounds.1 ⟨_, _, _, bodyTyped⟩
            ⟨_, _, postTyped⟩,
        CellAwareInvocationAcceptedForItems.initial_reflects_of_valid bridge index producer registry invocation
          faults administrative fun runtime covers ledger => CellAwareInvocationForInitialTerminal.reflects bridge
            model producer transport (fun represented => CompatibleExpressionPrimitives.bool_fields represented)
            (expressions fuel _ runtime covers ledger).2 (sourceEq ▸ conditionFound) nodeType
            (sourceEq ▸ conditionTyped) generated loopTyped innerBounds.2.1 postBounds.2 ⟨_, _, _, bodyTyped⟩
            ⟨_, _, postTyped⟩⟩
    have initialBounds := CellAwareInvocationAcceptedForItems.initial_correct bridge bindings transport index producer
      registered registry invocation faults administrative budget expressions writes sourceEq unique artifact checked
      headReached.reached compilerFound form terminal initial initialCovered (fun item member => List.mem_append_left _ member)
      signatures initialTyped ⟨_, initialNative⟩
    refine ⟨?_, ?_, CellAwareInvocationAcceptedNative.sequence_word _ _ _⟩
    · intro size within mapping world actualContext environment canonical actual before store embedding
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready finalContext outcome after trace
      exact CellAwareInvocationForSequences.preserves bridge model producer sourceEq initialBounds.1 unique
        (sourceEq ▸ statementFound) form tailBounds.1 within environments heaps locals agrees actualTyped runtime covers
        sameLedger sourceTyped initial admitted authority physical owner sameLocation ready trace
    · intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed
      exact CellAwareInvocationForSequences.reflects bridge model producer sourceEq initialBounds.2
        (sourceEq ▸ statementFound) form tailBounds.2.1 within environments heaps locals agrees actualTyped runtime covers
        sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
  | forBoundary => intro covered; cases covered
  | boundary => intro covered; cases covered

include bindings transport registered in
/-- The complete accepted body of an actual named or contextual invocation:
its compiler tree, footer and native result. Source executions of the original
statements are related in both directions at the actual reached heap. -/
theorem body_preserves (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      index.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (index.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions writes artifact checked sourceEq unique body.tree covered (fun _ member => index.site_root member)
    result signatures sourceTyped flowNative).1
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.preserves bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

include bindings transport registered in
/-- Native completion of the same complete accepted body reconstructs an
original Source execution, its body result and the reached heap. -/
theorem body_reflects (budget : Nat)
    (expressions : CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (index.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        index.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  have flowNative : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative)
      body.flow nativeType whole.indexed.layouts.definitions := by
    obtain ⟨_, native⟩ := native
    rw [body.emitted] at native
    exact TypedLexicalWhile.Native.finished_flow native
  have bound := (correct bridge bindings transport index producer registered registry invocation faults
    administrative budget expressions writes artifact checked sourceEq unique body.tree covered (fun _ member => index.site_root member)
    result signatures sourceTyped flowNative).2.1
  intro size within
  rw [body.emitted]
  exact CellAwareInvocationBodyFinish.reflects bridge producer bound sourceEq sourceTyped depth projection
    index.fellThrough index.escaped within

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow
end
