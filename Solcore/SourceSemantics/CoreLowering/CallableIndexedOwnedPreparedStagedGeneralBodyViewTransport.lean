import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles

/-! Actual compiler actions for recursive ordinary and direct calls cross the
retained unchanged body view. Runtime children keep their ordered syntax;
synthetic callees retain real metadata lookups and are not evaluated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralBodyViewSyntax
open CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport

variable {directSites : DeclarationInstantiation → Prop}

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

private inductive FormInFragment : ExpressionForm → Prop where
  | atomic {form} (leaf : CompatibleExpressionLiterals.Atomic form) : FormInFragment form
  | proxy {inner} : FormInFragment (.proxy inner)
  | read {name binder} : FormInFragment (.reference name (.local binder))
  | group {inner} : FormInFragment (.group inner)
  | tuple {ids} : FormInFragment (.tuple ids)
  | constructor {instantiation ids} : FormInFragment (.constructor instantiation ids)
  | direct {callee ids instantiation} : FormInFragment (.call callee ids (.declaration instantiation))
  | builtin {callee ids function} : FormInFragment (.call callee ids (.builtinFunction function))
  | call {callee ids metadata} : FormInFragment (.call callee ids (.indirect metadata))
  | unary {operator operand} : FormInFragment (.unary operator operand)
  | binary {left operator right} : FormInFragment (.binary left operator right)
  | index {base key} : FormInFragment (.index base key)
  | conditional {test yes no} : FormInFragment (.conditional test yes no)

private theorem syntax_form {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax source id directSites) (found : source.lookupExpression? id = some node) :
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
  | proxy selected form =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.proxy
  | group selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.group
  | tuple selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.tuple
  | constructor selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.constructor
  | direct selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.direct
  | builtin selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.builtin
  | call selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.call
  | unary selected form _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.unary
  | binary selected form _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.binary
  | index selected form _ _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.index
  | conditional selected form _ _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      exact form.symm ▸ FormInFragment.conditional

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

/-- Reader and leaf fields shared by ordinary and evidence-aware policies.
The special action is compared at the actual compiler step separately. -/
structure ReadPolicyOn (policy : SourceCoreFunctions.Policy)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (allowed : ExpressionId → Prop) (directSites : DeclarationInstantiation → Prop) : Prop where
  read : ∀ id, allowed id → GeneralSyntax source id directSites → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : ReadPolicyOn
    policy readFuel values source
      (fun id => Reaches source roots (.expression id)) directSites)
  (viewProfile : ReadPolicyOn
    policy readFuel values view
      (fun id => Reaches view roots (.expression id)) directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile

private theorem policy_read_eq {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    policy.readExpression source id = policy.readExpression view id := by
  rw [sourceProfile.read id reached tree,
    viewProfile.read id (reached.metadata edited.metadata) (syntax_view edited avoids tree reached)]
  exact compatible_read_eq edited.metadata (expression_lookup edited avoids reached)

include callables readView in
theorem compiler_step_eq_of_hook (fuel : Nat) {id : ExpressionId} {node : ExpressionNode}
    (tree : GeneralSyntax source id directSites) (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node)
    (children : ∀ child, RuntimeChild node.form child →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt =
        SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt)
    (specialEq :
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower compilation
            (fun budget childSource childScope childId childReasonAt =>
              SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                compilation childSource childScope childId childReasonAt)
            (fuel + 1) source scope id reasonAt) =
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower compilation
            (fun budget childSource childScope childId childReasonAt =>
              SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
                compilation childSource childScope childId childReasonAt)
            (fuel + 1) view scope id reasonAt)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation view scope id reasonAt := by
  have lookup := expression_lookup edited avoids reached
  have viewFound := lookup.symm.trans found
  have sameRead := policy_read_eq edited avoids sourceProfile viewProfile tree reached
  by_cases owner : id.occurrence.owner = source.owner
  · have viewOwner := owner.trans edited.metadata.owner
    conv => lhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    conv => rhs; rw [SourceCoreFunctions.lowerExpressionWithPolicy]
    have sourceOwned : ¬id.occurrence.owner ≠ source.owner := fun different => different owner
    have viewOwned : ¬id.occurrence.owner ≠ view.owner := fun different => different viewOwner
    simp only [if_neg sourceOwned, if_neg viewOwned,
      found, viewFound, bind, Except.bind, pure, Except.pure]
    cases hook : policy.lowerSpecial? <;> simp only [hook] at specialEq ⊢
    all_goals try
      rename_i lower
      rw [specialEq]
      cases action : lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) view scope id reasonAt
      all_goals try rfl
      all_goals rename_i output
      all_goals cases output
      all_goals try rfl
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
            exact children child (by simp [RuntimeChild, form, ExpressionForm.references, member])
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
          | proxy =>
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading, viewCompatibleReading,
                SourceCoreCompatibleDataExpressions.lowerWithReasons, bind, Except.bind, pure, Except.pure]
          | read =>
              simp only [formEq, viewReading, sourceProfile.lower, readLower]
          | @group inner =>
              have child := children inner (by simp [RuntimeChild, formEq, ExpressionForm.references])
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
                          have firstSame := children first (by simp [RuntimeChild, formEq, ExpressionForm.references])
                          have secondSame := children second (by simp [RuntimeChild, formEq, ExpressionForm.references])
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
                  simp only [RuntimeChild, formEq, ExpressionForm.references, List.mem_map, NodeId.expression.injEq]
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
              have child := children operand (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, child]
          | @binary left operator right =>
              have first := children left (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have second := children right (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, first, second]
          | @index base key =>
              have first := children base (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have second := children key (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have baseReached : Reaches source roots (.expression base) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have baseLookup := expression_lookup edited avoids baseReached
              have baseReading : SourceCoreCompatibleDataExpressions.readExpression values.checked source base =
                  SourceCoreCompatibleDataExpressions.readExpression values.checked view base := by
                simp only [SourceCoreCompatibleDataExpressions.readExpression, baseLookup, edited.metadata.owner]
              simp only [formEq, viewReading, sourceProfile.leaf,
                SourceCoreCompatibleDataExpressions.leafLowerer, compatibleReading,
                viewCompatibleReading, bind, Except.bind]
              simp only [SourceCoreCompatibleDataExpressions.lowerWithReasons, compatibleReading,
                viewCompatibleReading, bind, Except.bind, formEq, Nat.min_self, baseReading, first, second]
          | @conditional condition yes no =>
              have test := children condition (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have thenBranch := children yes (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have elseBranch := children no (by simp [RuntimeChild, formEq, ExpressionForm.references])
              simp only [formEq, viewReading, test, thenBranch, elseBranch]
          | @direct callee ids instantiation =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have calleeLookup := expression_lookup edited avoids calleeReached
              have calleeRead := readView callee calleeReached
              have validatorSame : SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation =
                  SourceCompilationPlan.validateDirectDeclarationCallee view id callee instantiation := by
                simp only [SourceCompilationPlan.validateDirectDeclarationCallee, calleeLookup]
              have selectedSame : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
                  SourceCoreFunctions.selectedSignature policy compilation view node instantiation false := by
                simp only [SourceCoreFunctions.selectedSignature, edited.metadata.owner]
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, member])
              simp only [formEq, viewReading, edited.metadata.owner, calleeRead, validatorSame,
                selectedSame, argumentsSame]
          | @builtin callee ids function =>
              have calleeReached : Reaches source roots (.expression callee) :=
                .expression reached found (by simp [formEq, ExpressionForm.references])
              have argumentReached : ∀ child, child ∈ ids → Reaches source roots (.expression child) :=
                fun child member => .expression reached found
                  (by simp [formEq, ExpressionForm.references, member])
              have validatorSame := SourceCoreElaboration.validateBuiltinFunctionCall_congr
                edited.metadata.owner node callee ids function
                (CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.lookup_node edited.metadata
                  (expression_lookup edited avoids calleeReached))
                (fun child member => CallableIndexedOwnedPreparedStagedGeneralBodyViewReadPolicy.lookup_node edited.metadata
                  (expression_lookup edited avoids (argumentReached child member)))
              have calleeRead := readView callee calleeReached
              have referenceSame : ∀ calleeNode,
                  SourceCoreFunctions.builtinReference policy.callables compilation source calleeNode function.spelling function =
                    SourceCoreFunctions.builtinReference policy.callables compilation view calleeNode function.spelling function := by
                intro calleeNode
                rw [callables]
                cases native <;> rfl
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, member])
              simp only [formEq, viewReading, validatorSame, calleeRead, referenceSame, argumentsSame, hookSame]
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
                (syntax_child tree found (by simp [RuntimeChild, formEq, ExpressionForm.references])) calleeReached
              have calleeSame := children callee (by simp [RuntimeChild, formEq, ExpressionForm.references])
              have argumentsSame : ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
                ids.mapM (fun child =>
                  SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope child reasonAt) := by
                apply mapM_eq_of_members
                intro child member
                exact children child (by simp [RuntimeChild, formEq, ExpressionForm.references, member])
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

end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn
    policy compilation readFuel values source scope reasonAt
      (fun id => Reaches source roots (.expression id)) directSites)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyOn
    policy compilation readFuel values view scope reasonAt
      (fun id => Reaches view roots (.expression id)) directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile

include callables readView in
/-- The actual production compiler returns the same complete action on every
reached node of the supported recursive grammar. Compiler fuel is identical;
child equalities follow its real predecessor recursion, including ordered
vectors. No evaluator, raw-type cast, or arbitrary source-insensitive policy is
assumed. -/
theorem compiler_eq_on (fuel : Nat) {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt := by
  induction fuel generalizing id with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy]
  | succ fuel ih =>
      obtain ⟨node, found⟩ := syntax_found tree
      apply compiler_step_eq_of_hook edited avoids
        ⟨sourceProfile.read, sourceProfile.lower, sourceProfile.leaf⟩
        ⟨viewProfile.read, viewProfile.lower, viewProfile.leaf⟩
        callables readView fuel tree reached found
      · intro child edge
        exact ih (syntax_child tree found edge) (.expression reached found (runtime_child_references edge))
      · exact (sourceProfile.special id reached tree _ _).trans
          (viewProfile.special id (reached.metadata edited.metadata)
            (syntax_view edited avoids tree reached) _ _).symm

include callables readView in
/-- An accepted Code.view action transfers to the original Source through the
same factory action, after its actual recursive syntax has been transported.
Raw typing and declaration authority remain original-source issuer inputs. -/
theorem accepted_original_on (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax view id directSites) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered := by
  exact (compiler_eq_on edited avoids sourceProfile viewProfile callables readView fuel
    (syntax_original edited avoids tree reached) reached).trans accepted
end Compiler

section Compiler
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {scope : SourceCoreLocalCell.Scope}
  {reasonAt : ExpressionId → Word}
  (sourceProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
    policy compilation readFuel values source scope reasonAt directSites)
  (viewProfile : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralPolicyFor
    policy compilation readFuel values view scope reasonAt directSites)
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active)
  (readView : ∀ id, Reaches source roots (.expression id) →
    policy.readExpression source id = policy.readExpression view id)
include edited avoids sourceProfile viewProfile callables readView

/-- Existing global policy callers restrict their facts to the actual body. -/
theorem compiler_eq (fuel : Nat) {id : ExpressionId} (tree : GeneralSyntax source id directSites)
    (reached : Reaches source roots (.expression id)) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt =
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation view scope id reasonAt :=
  compiler_eq_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables readView fuel tree reached

/-- Compatibility wrapper for complete global profiles. -/
theorem accepted_original (fuel : Nat) {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax view id directSites) (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation view scope id reasonAt = .ok lowered) :
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
      compilation source scope id reasonAt = .ok lowered :=
  accepted_original_on edited avoids (sourceProfile.on _) (viewProfile.on _) callables readView fuel tree reached accepted
end Compiler

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralBodyViewTransport
