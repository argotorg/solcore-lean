import Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyTree
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates

/-! The native body collector follows the actual named compiler and its
marked lexical allocations. Source typing supplies context extension; the
accepted initializer supplies the complete ordered candidate bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
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

theorem scope_generalized {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context nextContext : SourceSemantics.Context} {binder : TypedBinder} (payload : Ty)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (declaration : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) = [binder])
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends source.owner context binder nextContext) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) nextContext := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    unfold SourceCoreDataPlaces.rootBinder at authentic
    by_cases owner : binder.id.owner ≠ source.owner
    · simp [owner, throw, bind, Except.bind] at authentic
    · cases quantified : binder.scheme.quantified with
      | nil => exact False.elim (polymorphic quantified)
      | cons first rest => simp [owner, declaration, quantified, throw, bind, Except.bind] at authentic
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

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
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (expressionPolicy : policy.lowerExpression =
      SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
        ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
        prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
        diagnostics (context prepared named) prepared.base.callableContext none none)
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
    (syntaxTree : CellAwareSourceBodyAdmission.Syntax prepared.base.locals named.signature.key []
      (source named) approved expected sourceContext mode statements)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    {fuel : Nat} {type : Ty} {code : Expr} {escaped : Word} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel (source named) scope statements
      type reasonAt mode escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    CellAwareNativeBodyTree.Tree prepared named compiled certificates administrative reasonAt
      sourceContext scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
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
        (scope_generalized lowered.type declarations declaration polymorphic extended)
        generatedTail (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact .generalizedInitialized found form declaration polymorphic extended ordinary
        initializerFound initializerForm valueType requirements coercions site initial
        (initial.typed childTyped) allocation annotation same tail

end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors
