import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeTree
import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNativeBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates

/-! The native body collector follows the actual named compiler and its
marked lexical allocations. Source typing supplies context extension; the
accepted initializer supplies the complete ordered candidate bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)
open GeneralizedLocalInitializerCompilation (namedInputs)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩


private theorem while_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) result definitions) :
    ∃ childType, HasType context condition childType definitions := by
  cases typed with
  | letE allocation installed =>
    cases installed with
    | letE written invoked =>
      cases written with
      | storeCell reference closure =>
        cases closure with
        | inRight unitWF raw =>
          cases raw with
          | lambda parameterWF resultWF loop =>
            obtain ⟨_, shifted⟩ := computation_child loop
            exact ⟨_, TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem for_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    ∃ childType, HasType context condition childType definitions := by
  cases typed with
  | letE allocation installed =>
    cases installed with
    | letE written invoked =>
      cases written with
      | storeCell reference closure =>
        cases closure with
        | inRight unitWF raw =>
          cases raw with
          | lambda parameterWF resultWF loop =>
            obtain ⟨_, shifted⟩ := computation_child loop
            exact ⟨_, TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front shifted)⟩

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

/-- Only finite static expression and candidate profiles are inputs. All
compiler actions and native child typing are recovered from the accepted body. -/
theorem collected
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (unique : NodeOccurrencesUnique (source named))
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    (assignmentPolicy : ∀ fuel scope site assignment operator rhs output next reasonAt,
      SourceCoreLoops.assignValue policy fuel (source named) scope site assignment operator rhs output next reasonAt =
      SourceCoreCompatibleDataPlaces.lower (.initial checked) checked.signatures policy.lowerExpression
        fuel (source named) scope site assignment operator (some rhs) output next reasonAt
        (diagnostics.placeReason named.signature.key site assignment.target.root none)
        (GenericAssignmentDiagnostics.token compiled.own.assignments site assignment.target.root operator)
        (fun type => diagnostics.placeReason named.signature.key site assignment.target.root (some type)))
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (expressionPolicy : policy.lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
        ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
        diagnostics (context prepared named) prepared.base.callableContext none none)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder (source named) scope binder = SourceCoreCompatibleDataExpressions.lowerBinder checked (source named) scope binder)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (profiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [],
        Nonempty (GeneralizedLocalInitializerPackets.BindingProfile
          (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
            (context prepared named) scope initializer reasonAt) site.binding candidate))
    (bodyProfiles : ∀ {scope binder initializer}
      (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
        (source named) binder initializer) childFuel,
      ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
        (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
        candidate.source initializer))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : CellAwareImperativeSourceBodyAdmission.Syntax prepared.base.locals named.signature.key []
      (source named) approved expected sourceContext mode statements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (sourceSignatures : sourceContext.signatures = checked.signatures)
    {fuel : Nat} {type : Ty} {code : Expr} {escaped : Word} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope statements
      type reasonAt mode escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    CellAwareImperativeTree.Tree prepared named compiled certificates administrative reasonAt
      sourceContext scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil allowed =>
    have same : (Except.ok (LocalLoop.fallthrough type) : Except SourceCoreBasic.Error Expr) = Except.ok code := by simpa only [SourceCoreLoops.lowerFlowStatementsWithPolicy] using accepted
    cases same
    exact .nil allowed
  | @returnUnit sourceContext mode id node rest found form unit =>
    cases unit
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, first, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨checkedType, second, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := (ensure_same first).trans (ensure_same second).symm
      subst type
      simp only [first, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      exact .returnUnit rest found form
  | @returning sourceContext mode id node expression expressionNode rest found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .returning rest found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @tail sourceContext id node expression expressionNode found form expressionFound valueType typed value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .tail found form expressionFound valueType typed
        (children sourceContext declarations value expressionFound typed generated childTyped)
  | @generalizedInitialized sourceContext nextContext mode id node binder initializer initializerNode parameters result body rest found form declaration polymorphic extended ordinary initializerFound initializerForm valueType requirements coercions site remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have actualGenerated := expressionPolicy ▸ generated
      obtain ⟨childFuel, fuelEq, binding, located, ⟨initial⟩⟩ :=
        GeneralizedLocalInitializerCompilation.of_named_contextual compiled record
          initializerFound initializerForm site.selected actualGenerated
      have sameBinding : binding = site.binding := by
        rw [site.selectedBinder] at located
        exact Except.ok.inj (located.symm.trans site.located)
      subst binding
      subst fuel
      obtain ⟨initial⟩ := GeneralizedLocalInitializerPackets.of_receipt prepared initial
        (profiles site childFuel) (bodyProfiles site childFuel) rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have tail := ih
        (CellAwareNativeBodyCollectors.scope_generalized lowered.type declarations declaration polymorphic extended)
        (by cases extended; exact sourceSignatures) generatedTail (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact .generalizedInitialized found form declaration polymorphic extended ordinary
        initializerFound initializerForm valueType requirements coercions site initial
        (initial.typed childTyped) allocation annotation same tail
  | @initialized sourceContext nextContext mode id node binder initializer initializerNode rest found form member mono extended ordinary initializerFound valueType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, _projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, sameType, accepted⟩ := bind_ok accepted
      cases checkedType
      have same := ensure_same sameType
      subst payload
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have tail := ih (CompatibleMatchArmScopes.scope_bind lowered.type declarations member extended)
        (by cases extended; exact sourceSignatures) generatedTail (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact .initialized found form member mono extended ordinary initializerFound valueType typed
        (children sourceContext declarations value initializerFound typed generated childTyped)
        allocation annotation same tail

  | @uninitialized sourceContext nextContext mode id node binder rest found form member mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨tailCode, generatedTail, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      have tail := ih (CompatibleMatchArmScopes.scope_bind payload declarations member extended)
        (by cases extended; exact sourceSignatures) generatedTail (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      exact .uninitialized found form member mono extended ordinary
        (CompatibleStatementBindings.binder_projected (binderPolicy scope binder mono ▸ projected))
        allocation annotation same tail

  | @discard sourceContext mode id node expression expressionNode semicolon rest found form notTail continuing expressionFound typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        obtain ⟨_, childTyped⟩ := computation_child nativeTyped
        exact .discard found form notTail continuing expressionFound typed
          (children sourceContext declarations value expressionFound typed generated childTyped)
          (ih declarations sourceSignatures generatedBody tailTyped)
  | @block sourceContext mode id node statements rest found form inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form (innerIH declarations sourceSignatures generatedInner headTyped) (restIH declarations sourceSignatures generatedBody tailTyped)
  | @ifThen sourceContext mode id node condition conditionNode thenBody elseBody rest found form conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope [] type reasonAt false escaped =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨_, childTyped⟩ := computation_child branchTyped
        exact .ifThen found form conditionFound conditionType typed
          (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
          (thenIH declarations sourceSignatures generatedThen thenTyped) (elseIH declarations sourceSignatures generatedElse elseTyped) (restIH declarations sourceSignatures generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨_, childTyped⟩ := computation_child branchTyped
        exact .ifThen found form conditionFound conditionType typed
          (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
          (thenIH declarations sourceSignatures generatedThen thenTyped) (elseIH declarations sourceSignatures generatedElse elseTyped) (restIH declarations sourceSignatures generatedBody tailTyped)

  | @whileLoop sourceContext mode id node condition conditionNode statements rest found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, childTyped⟩ := while_condition loopTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact .whileLoop found form conditionFound conditionType typed
        (children sourceContext declarations conditionSyntax conditionFound typed generatedCondition childTyped)
        (loopIH declarations sourceSignatures generatedLoop loopBodyTyped)
        loopTyped
        (restIH declarations sourceSignatures generatedBody tailTyped)

  | @forLoop sourceContext loopContext postContext mode id node initialItems condition conditionNode postItems statements rest
      found form initialSyntax conditionFound conditionType typed conditionSyntax loopSyntax postSyntax loopSourceTyped postSourceTyped remaining loopIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      let nextReceipt : SourceCoreLocalCell.Scope → Expr → Prop := fun loopScope terminal =>
        ∃ conditionCode loopCode postCode postScope,
          terminal = LocalLoop.iterate type conditionCode loopCode postCode escaped ∧
          certificates loopContext loopScope condition ⟨.bool, conditionCode⟩ ∧
          CellAwareImperativeTree.Tree prepared named compiled certificates administrative reasonAt
            loopContext loopScope false statements expected type loopCode ∧
          CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type
            postContext postScope (LocalLoop.fallthrough type) loopContext loopScope postItems postCode ∧
          HasType (SourceCoreLocalCell.coreContext loopScope ++ administrative)
            (LocalLoop.iterate type conditionCode loopCode postCode escaped)
            (LanguageResult.resultType (LocalLoop.controlType type)) prepared.layouts.definitions
      have origin := AssignmentDiagnosticOrigins.ForOriginFor.start (tracked := true) found form
      obtain ⟨loopScope, terminal, completed, initialTree⟩ := CellAwareForHeaderCollectors.collected compiled
        unique assignmentsPrepared assignmentPolicy binderPolicy allocationPolicy children
        (continuation := nextReceipt)
        (fun loopScope terminal loopDeclarations accepted _nativeType nativeTyped => by
          obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
          obtain ⟨checkedType, checkedCondition, accepted⟩ := bind_ok accepted
          cases checkedType
          have sameType := ensure_same checkedCondition
          rcases conditionCode with ⟨native, code⟩
          dsimp only at sameType
          subst native
          obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
          obtain ⟨postCode, generatedPost, accepted⟩ := bind_ok accepted
          cases accepted
          obtain ⟨_, conditionNative⟩ := for_condition nativeTyped
          obtain ⟨⟨_, loopNative⟩, ⟨_, postNative⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
          obtain ⟨postScope, postTerminal, postSame, postTree⟩ := CellAwareForHeaderCollectors.collected compiled
            unique assignmentsPrepared assignmentPolicy binderPolicy allocationPolicy children
            (continuation := fun _ terminal => terminal = LocalLoop.fallthrough type)
            (fun _ _ _ accepted _ _ => Except.ok.inj accepted.symm)
            postSyntax loopDeclarations (initialSyntax.signatures.trans sourceSignatures) origin.post_origin generatedPost postNative
          subst postTerminal
          exact ⟨code, loopCode, postCode, postScope, rfl,
            children loopContext loopDeclarations conditionSyntax conditionFound typed generatedCondition conditionNative,
            loopIH loopDeclarations (initialSyntax.signatures.trans sourceSignatures) generatedLoop loopNative, postTree, loopTyped⟩)
        initialSyntax declarations sourceSignatures origin.header generatedInitial initialTyped
      obtain ⟨conditionCode, loopCode, postCode, postScope, rfl, conditionCertificate, loopTree, postTree, loopTyped⟩ := completed
      exact .forLoop found form initialTree conditionFound conditionType typed conditionCertificate
        loopTree postTree loopSourceTyped postSourceTyped loopTyped (restIH declarations sourceSignatures generatedBody tailTyped)

  | @assign sourceContext mode id node assignment operator rhs rhsNode binder rest found form declaration targetType profile bare rhsFound rhsType assignmentTyped value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨_projections, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare assignmentTyped
      obtain ⟨actualBinder, preparedPlace, index, lowered, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
      obtain ⟨_, rhsNative⟩ := (CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_children
        (codeEq ▸ nativeTyped)).1
      have child : certificates sourceContext scope rhs lowered :=
        children sourceContext declarations value rhsFound (rhsType.symm ▸ rightTyped) generated rhsNative
      obtain ⟨head, emitted, token⟩ := GenericAssignmentStatements.Head.of_lower_bare_with_token
        (administrative := administrative) (definitions := prepared.layouts.definitions)
        bare unique writable rightTyped runtimeProfile (fun actual acceptedRight => by
          have same : actual = lowered := Except.ok.inj (acceptedRight.symm.trans generated)
          subst actual
          exact ⟨rhsNode, rhsFound, child⟩) accepted
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer := by
        rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl word)
      have operands := GenericAssignmentDiagnostics.prepared_operands tablePrepared
        (lookupStatement?_sound found).1 (.statement form) rawProfile
      rw [(lookupStatement?_sound found).2, ← token] at operands
      rw [emitted]
      exact .assign found form head bare rightTyped operands (ih declarations sourceSignatures generatedBody tailTyped)

  | @assignProjected sourceContext mode id node assignment operator rhs rhsNode binder rest found form declaration route profile projected keys rhsFound rhsType assignmentTyped value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨sourceTyped, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.projected_assignment_facts unique declaration route assignmentTyped
      obtain ⟨head, emitted, token, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped runtimeProfile
          (certificate := certificates sourceContext)
          (fun child lowered member generated raw => by
            obtain ⟨_, native⟩ := raw
            rcases List.mem_cons.mp member with same | member
            · subst child
              exact ⟨rhsNode, rhsFound, children sourceContext declarations value rhsFound
                (rhsType.symm ▸ rightTyped) generated native⟩
            · obtain ⟨node, found, childTyped⟩ := route.key_typed unique (sourceTyped binder declaration) member
              exact ⟨node, found, children sourceContext declarations (keys _ member) found childTyped generated native⟩)
          accepted nativeTyped
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have rawProfile : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer := by
        rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl word)
      have operands := GenericAssignmentDiagnostics.prepared_operands tablePrepared
        (lookupStatement?_sound found).1 (.statement form) rawProfile
      rw [(lookupStatement?_sound found).2, ← token] at operands
      rw [emitted]
      exact .assignProjected found form head projected rightTyped
        (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
          (.statement found form) sourceSignatures preparedAt operands registry)
        (ih declarations sourceSignatures generatedBody tailTyped)

  | breaking rest found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      cases accepted
      exact .breaking rest found form
  | continuing rest found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checkedType, _, accepted⟩ := bind_ok accepted
      cases checkedType
      cases accepted
      exact .continuing rest found form

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
