import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport

/-! Static steps for original-source recursive compiler-action transport.
  Actual reached lookups preserve complete nodes. Metadata preserves declared
  binders, and the production indirect-call hook ignores its Source argument.
  Full compiler-action equality follows its actual fuel recursion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)

section Syntax
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
include edited avoids

/-- Recursive syntax crosses only actual reached, unedited occurrences. -/
theorem syntax_view {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) : Syntax view id := by
  revert reached
  induction tree with
  | leaf finite =>
      intro reached
      exact .leaf (CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport.finite_syntax
        edited avoids finite reached)
  | @group id node inner found form child ih =>
      intro reached
      have innerReached : Reaches source roots (.expression inner) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .group ((expression_lookup edited avoids reached).symm.trans found) form (ih innerReached)
  | @tuple id node ids found form children ih =>
      intro reached
      exact .tuple ((expression_lookup edited avoids reached).symm.trans found) form
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @constructor id node instantiation ids found form ranges children ih =>
      intro reached
      exact .constructor ((expression_lookup edited avoids reached).symm.trans found) form ranges
        (fun child member => ih child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @call id node callee ids metadata found form calleeTree children calleeIH childrenIH =>
      intro reached
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [form, ExpressionForm.references])
      exact .call ((expression_lookup edited avoids reached).symm.trans found) form
        (calleeIH calleeReached)
        (fun child member => childrenIH child member
          (.expression reached found (by simp [form, ExpressionForm.references, member])))
  | @unary id node operator operand found form child ih =>
      intro reached
      exact .unary ((expression_lookup edited avoids reached).symm.trans found) form
        (ih (.expression reached found (by simp [form, ExpressionForm.references])))
  | @binary id node left operator right found form first second firstIH secondIH =>
      intro reached
      exact .binary ((expression_lookup edited avoids reached).symm.trans found) form
        (firstIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (secondIH (.expression reached found (by simp [form, ExpressionForm.references])))
  | @conditional id node condition yes no found form test thenBranch elseBranch testIH thenIH elseIH =>
      intro reached
      exact .conditional ((expression_lookup edited avoids reached).symm.trans found) form
        (testIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (thenIH (.expression reached found (by simp [form, ExpressionForm.references])))
        (elseIH (.expression reached found (by simp [form, ExpressionForm.references])))

/-- Reverse syntax uses the original body's authentic reachability path. -/
theorem syntax_original {id : ExpressionId} (tree : Syntax view id)
    (reached : Reaches source roots (.expression id)) : Syntax source id := by
  have reverse : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact syntax_view reverse (avoids.view edited.metadata) tree (reached.metadata edited.metadata)
end Syntax

/-- Compatible read policy retains requirements, coercions and projected type
  because its actual full node lookup and owner stay equal. -/
theorem compatible_read_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId}
    (lookup : source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataExpressions.readExpression checked source id =
      SourceCoreCompatibleDataExpressions.readExpression checked view id := by
  simp only [SourceCoreCompatibleDataExpressions.readExpression, metadata.owner, lookup]

/-- The declared binder and exact lazy mapping encoder survive the same view;
  this follows from rootBinder transport rather than a raw type cast. -/
theorem compatible_lower_read_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word}
    (lookup : source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id reason =
      SourceCoreCompatibleDataExpressions.lowerRead fuel values view scope id reason := by
  simp only [SourceCoreCompatibleDataExpressions.lowerRead,
    compatible_read_eq metadata lookup, metadata.owner, rootBinder metadata]

private theorem mapM_eq_of_members {α β ε : Type} {items : List α}
    {left right : α → Except ε β} (same : ∀ item, item ∈ items → left item = right item) :
    items.mapM left = items.mapM right := by
  revert same
  induction items with
  | nil => intro _same; rfl
  | cons item rest ih =>
      intro same
      simp only [List.mapM_cons]
      rw [same item (by simp), ih (fun next member => same next (by simp [member]))]

/-- The validator reads the literal callee plus the ordered arguments. Full
  lookup equality preserves every type, raw type and coercion check. -/
theorem indirect_validator_eq {source view : TypedSource}
    {node : ExpressionNode} {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution}
    (calleeLookup : source.lookupExpression? callee = view.lookupExpression? callee)
    (argumentLookups : ∀ child, child ∈ ids →
      source.lookupExpression? child = view.lookupExpression? child) :
    SourceCompilationPlan.validateIndirectCallMetadata source node callee ids metadata =
      SourceCompilationPlan.validateIndirectCallMetadata view node callee ids metadata := by
  have calleeExact : SourceCompilationPlan.exactExpression source callee =
      SourceCompilationPlan.exactExpression view callee := by
    simp only [SourceCompilationPlan.exactExpression, calleeLookup]
  have argumentTypes : ids.mapM (fun child => do
      let actual ← SourceCompilationPlan.exactExpression source child
      pure actual.type) = ids.mapM (fun child => do
      let actual ← SourceCompilationPlan.exactExpression view child
      pure actual.type) := by
    apply mapM_eq_of_members
    intro child member
    simp only [SourceCompilationPlan.exactExpression, argumentLookups child member]
  simp only [SourceCompilationPlan.validateIndirectCallMetadata, calleeExact, argumentTypes]

/-- Both production policy branches ignore the Source argument of callCallable.
  The actual node, compilation context, table and diagnostic owner are fixed. -/
theorem production_call_eq (native : Option SourceCoreGeneralFunctions.CallableContext)
    (active : TypeSystem.Substitution) (compilation : SourceCoreFunctions.Context)
    (source view : TypedSource) (node : ExpressionNode) (result : Ty)
    (callee arguments : Expr) :
    (SourceCoreGeneralFunctions.callablePolicy native active).callCallable
      compilation source node result callee arguments =
    (SourceCoreGeneralFunctions.callablePolicy native active).callCallable
      compilation view node result callee arguments := by
  cases native <;> rfl


private inductive FormInFragment : ExpressionForm → Prop where
  | atomic {form} (leaf : CompatibleExpressionLiterals.Atomic form) : FormInFragment form
  | read {name binder} : FormInFragment (.reference name (.local binder))
  | group {inner} : FormInFragment (.group inner)
  | tuple {ids} : FormInFragment (.tuple ids)
  | constructor {instantiation ids} : FormInFragment (.constructor instantiation ids)
  | call {callee ids metadata} : FormInFragment (.call callee ids (.indirect metadata))
  | unary {operator operand} : FormInFragment (.unary operator operand)
  | binary {left operator right} : FormInFragment (.binary left operator right)
  | conditional {test yes no} : FormInFragment (.conditional test yes no)

private theorem syntax_found {source : TypedSource} {id : ExpressionId}
    (tree : Syntax source id) : ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | leaf finite => cases finite <;> exact ⟨_, ‹source.lookupExpression? id = some _›⟩
  | group found _ _ => exact ⟨_, found⟩
  | tuple found _ _ => exact ⟨_, found⟩
  | constructor found _ _ _ => exact ⟨_, found⟩
  | call found _ _ _ => exact ⟨_, found⟩
  | unary found _ _ => exact ⟨_, found⟩
  | binary found _ _ _ => exact ⟨_, found⟩
  | conditional found _ _ _ _ => exact ⟨_, found⟩

private theorem syntax_form {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (found : source.lookupExpression? id = some node) :
    FormInFragment node.form := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          exact .atomic atomic
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.read
      | group selected form _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.group
      | pair selected form _ _ =>
          cases Option.some.inj (selected.symm.trans found)
          exact form.symm ▸ FormInFragment.tuple
  | group selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.group
  | tuple selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.tuple
  | constructor selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.constructor
  | call selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.call
  | unary selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.unary
  | binary selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.binary
  | conditional selected form _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.conditional

/-- Direct references obtain their syntax from the actual finite parent tree.
The projection preserves the literal argument vector, including duplicates. -/
private theorem syntax_child {source : TypedSource} {id child : ExpressionId}
    {node : ExpressionNode} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (edge : (.expression child : NodeId) ∈ node.form.references) : Syntax source child := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;> simp [formEq, ExpressionForm.references] at edge
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          simp [form, ExpressionForm.references] at edge
      | @group _ _ inner selected form innerTree =>
          cases Option.some.inj (selected.symm.trans found)
          have same : child = inner := by simpa [form, ExpressionForm.references] using edge
          exact same.symm ▸ Syntax.leaf innerTree
      | @pair _ _ left right selected form first second =>
          cases Option.some.inj (selected.symm.trans found)
          have member : child = left ∨ child = right := by
            simpa [form, ExpressionForm.references] using edge
          rcases member with same | same
          · exact same.symm ▸ Syntax.leaf first
          · exact same.symm ▸ Syntax.leaf second
  | @group _ _ inner selected form innerTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = inner := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ innerTree
  | tuple selected form children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | constructor selected form _ranges children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | @call _ _ callee ids _ selected form calleeTree children =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = callee ∨ child ∈ ids := by
        simpa [form, ExpressionForm.references] using edge
      rcases member with same | member
      · exact same.symm ▸ calleeTree
      · exact children child member
  | @unary _ _ operator operand selected form childTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = operand := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ childTree
  | @binary _ _ left operator right selected form first second =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = left ∨ child = right := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same
      · exact same.symm ▸ first
      · exact same.symm ▸ second
  | @conditional _ _ test yes no selected form testTree yesTree noTree =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = test ∨ child = yes ∨ child = no := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same | same
      · exact same.symm ▸ testTree
      · exact same.symm ▸ yesTree
      · exact same.symm ▸ noTree

private theorem basic_atomic_eq {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (lookup : source.lookupExpression? id = view.lookupExpression? id)
    (atomic : CompatibleExpressionLiterals.Atomic node.form)
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (reason : Word) :
    SourceCoreBasic.lowerExpression fuel source scope id reason =
      SourceCoreBasic.lowerExpression fuel view scope id reason := by
  have sameRead : SourceCoreBasic.readExpression source id = SourceCoreBasic.readExpression view id := by
    simp only [SourceCoreBasic.readExpression, metadata.owner, lookup]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      conv => lhs; rw [SourceCoreBasic.lowerExpression]
      conv => rhs; rw [SourceCoreBasic.lowerExpression]
      cases reading : SourceCoreBasic.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          simp only [viewReading, bind, Except.bind]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have readFound := (BasicExpressions.readExpression_certificate reading).1
          cases Option.some.inj (readFound.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;>
            simp only [viewReading, formEq, bind, Except.bind, pure, Except.pure]

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn
    policy compilation readFuel values source scope reasonAt
      (fun id => Reaches source roots (.expression id)))
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyOn
    policy compilation readFuel values view scope reasonAt
      (fun id => Reaches view roots (.expression id)))
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
include edited avoids sourceProfile viewProfile

private theorem policy_read_eq {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  rw [sourceProfile.read id reached tree,
    viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)]
  exact compatible_read_eq edited.metadata (expression_lookup edited avoids reached)

include callables in
private theorem compiler_step_eq (fuel : Nat) {id : ExpressionId} {node : ExpressionNode}
    (tree : Syntax source id) (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node)
    (children : ∀ child, (.expression child : NodeId) ∈ node.form.references →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation view scope id reasonAt := by
  have lookup := expression_lookup edited avoids reached
  have viewFound := lookup.symm.trans found
  have sameRead := policy_read_eq edited avoids sourceProfile viewProfile tree reached
  have sourceBypass := sourceProfile.special id reached tree
    (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
  have viewBypass := viewProfile.special id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)
    (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
  by_cases owner : id.occurrence.owner = source.owner
  · have viewOwner := owner.trans edited.metadata.owner
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    have sourceOwned : ¬id.occurrence.owner ≠ source.owner := fun different => different owner
    have viewOwned : ¬id.occurrence.owner ≠ view.owner := fun different => different viewOwner
    simp only [if_neg sourceOwned, if_neg viewOwned,
      found, viewFound, bind, Except.bind, pure, Except.pure]
    cases hook : policy.lowerSpecial? <;> simp only [hook] at sourceBypass viewBypass ⊢
    all_goals try rw [sourceBypass, viewBypass]
    all_goals
      try dsimp only [bind, Except.bind, pure, Except.pure]
      cases reading : policy.readExpression source id with
      | error error =>
          have viewReading := sameRead.symm.trans reading
          cases form : node.form <;> try rfl
          all_goals simp only [viewReading]
      | ok output =>
          rcases output with ⟨actualNode, type⟩
          have compatibleReading := (sourceProfile.read id reached tree).symm.trans reading
          have actualMetadata := CompatibleExpressionReads.metadata_of_read compatibleReading
          cases Option.some.inj (actualMetadata.found.symm.trans found)
          have viewReading := sameRead.symm.trans reading
          have viewCompatibleReading :=
            (viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)).symm.trans viewReading
          have clipped : min (fuel + 1) fuel = fuel := Nat.min_eq_right (Nat.le_succ fuel)
          have readLower := compatible_lower_read_eq edited.metadata (fuel := readFuel)
            (values := values) (scope := scope) (reason := reasonAt id) lookup
          have hookSame : ∀ result callee arguments,
              policy.callables.callCallable compilation source node result callee arguments =
                policy.callables.callCallable compilation view node result callee arguments := by
            intro result callee arguments
            rw [callables]
            exact production_call_eq native active compilation source view node result callee arguments
          have tupleChildren {ids : List ExpressionId} (form : node.form = .tuple ids) :
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation source scope child reasonAt) =
              ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                compilation view scope child reasonAt) := by
            apply mapM_eq_of_members
            intro child member
            exact children child (by simp [form, ExpressionForm.references, member])
          have tupleLeaf {ids : List ExpressionId} (form : node.form = .tuple ids) :
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) source scope id reasonAt =
              policy.leafLowerer
                  (fun budget childSource childScope childId childReasonAt =>
                    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                      compilation childSource childScope childId childReasonAt)
                  (fuel + 1) view scope id reasonAt := by
            rw [sourceProfile.leaf]
            simp only [SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
              viewCompatibleReading, bind, Except.bind, pure, Except.pure, form, clipped,
              tupleChildren form]
          have fragment := syntax_form tree found
          generalize formEq : node.form = actualForm at fragment
          cases fragment with
          | atomic atomic =>
              have atomicBasic := basic_atomic_eq edited.metadata found lookup (formEq.symm ▸ atomic)
                (fuel + 1) scope (reasonAt id)
              generalize atomicForm : actualForm = leafForm at atomic
              cases atomic with
              | unit =>
                  simp only [formEq, atomicForm, viewReading]
                  exact tupleLeaf (formEq.trans atomicForm)
              | bool name value =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | word literal =>
                  simp only [formEq, atomicForm, viewReading, sourceProfile.leaf,
                    SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading, bind, Except.bind, atomicBasic]
              | integer literal resolution => rfl
          | read =>
              simp only [formEq, viewReading, sourceProfile.lower, readLower]
          | @group inner =>
              have child := children inner (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @tuple ids =>
              cases ids with
              | nil =>
                  simp only [formEq, viewReading, tupleLeaf formEq]
              | cons first rest =>
                  cases rest with
                  | nil =>
                      simp only [formEq, viewReading, tupleLeaf formEq]
                  | cons second tail =>
                      cases tail with
                      | nil =>
                          have firstSame := children first (by simp [formEq, ExpressionForm.references])
                          have secondSame := children second (by simp [formEq, ExpressionForm.references])
                          simp only [formEq, viewReading, firstSame, secondSame]
                      | cons third tail =>
                          simp only [formEq, viewReading, tupleLeaf formEq]
          | @constructor instantiation ids =>
              have argumentsSame : (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation source scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) =
                (ids.zip instantiation.payloadTypes).mapM (fun (argument, expected) => do
                  let expected ← SourceCoreCompatibleDataExpressions.projectType values.checked
                    (.occurrence id.occurrence) expected
                  let argument ← SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
                    compilation view scope argument reasonAt
                  SourceCoreBasic.ensureType (.occurrence id.occurrence) expected argument.type
                  pure argument) := by
                apply mapM_eq_of_members
                intro pair member
                have child := children pair.1 (by
                  simp only [formEq, ExpressionForm.references, List.mem_map, NodeId.expression.injEq]
                  exact ⟨pair.1, (List.of_mem_zip member).1, rfl⟩)
                cases pair
                dsimp only at child ⊢
                rw [child]
              simp only [bind, Except.bind] at argumentsSame
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
                viewCompatibleReading, bind, Except.bind]
              simp only [SourceCoreCompatibleDataExpressions.lowerWithReasons, compatibleReading,
                viewCompatibleReading, bind, Except.bind, formEq, Nat.min_self, argumentsSame]
          | @unary operator operand =>
              have child := children operand (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @binary left operator right =>
              have first := children left (by simp [formEq, ExpressionForm.references])
              have second := children right (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, first, second]
          | @conditional condition yes no =>
              have test := children condition (by simp [formEq, ExpressionForm.references])
              have thenBranch := children yes (by simp [formEq, ExpressionForm.references])
              have elseBranch := children no (by simp [formEq, ExpressionForm.references])
              simp only [formEq, viewReading, test, thenBranch, elseBranch]
          | @call callee ids metadata =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have argumentReached : ∀ child, child ∈ ids → Reaches source roots (.expression child) :=
                fun child member => .expression reached found
                  (by simp [formEq, ExpressionForm.references, member])
              have validatorSame := indirect_validator_eq (node := node) (metadata := metadata)
                (expression_lookup edited avoids calleeReached)
                (fun child member => expression_lookup edited avoids (argumentReached child member))
              have calleeRead := policy_read_eq edited avoids sourceProfile viewProfile
                (syntax_child tree found (by simp [formEq, ExpressionForm.references])) calleeReached
              have calleeSame := children callee (by simp [formEq, ExpressionForm.references])
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [formEq, ExpressionForm.references, member])
              simp only [formEq, viewReading, validatorSame, calleeRead, calleeSame, argumentsSame, hookSame]
  · have viewOwner : id.occurrence.owner ≠ view.owner :=
      fun same => owner (same.trans edited.metadata.owner.symm)
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    simp only [if_pos owner, if_pos viewOwner]
    change Except.error (.ownerMismatch source.owner id.occurrence.owner) =
      (Except.error (.ownerMismatch view.owner id.occurrence.owner) :
        Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr)
    rw [edited.metadata.owner]

include callables in
/-- The actual production compiler returns the same complete action on every
reached node of the supported recursive grammar. Compiler fuel is identical;
child equalities follow its real predecessor recursion, including ordered
vectors. No evaluator, raw-type cast, or arbitrary source-insensitive policy is
assumed. -/
theorem compiler_eq_on (fuel : Nat) {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt := by
  induction fuel generalizing id with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy]
  | succ fuel ih =>
      obtain ⟨node, found⟩ := syntax_found tree
      apply compiler_step_eq edited avoids sourceProfile viewProfile callables fuel tree reached found
      intro child edge
      exact ih (syntax_child tree found edge) (.expression reached found edge)

include callables in
/-- An accepted Code.view action transfers to the original Source through the
same factory action, after its actual recursive syntax has been transported.
Raw typing and declaration authority remain original-source issuer inputs. -/
theorem accepted_original_on (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Syntax view id) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered := by
  exact (compiler_eq_on edited avoids sourceProfile viewProfile callables fuel
    (syntax_original edited avoids tree reached) reached).trans accepted
end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
    policy compilation readFuel values source scope reasonAt)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor
    policy compilation readFuel values view scope reasonAt)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
include edited avoids sourceProfile viewProfile callables

/-- Existing global policy callers restrict their facts to the actual body. -/
theorem compiler_eq (fuel : Nat) {id : ExpressionId} (tree : Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt :=
  compiler_eq_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables fuel tree reached

/-- Compatibility wrapper for complete global profiles. -/
theorem accepted_original (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Syntax view id) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered :=
  accepted_original_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables fuel tree reached accepted
end Compiler

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
