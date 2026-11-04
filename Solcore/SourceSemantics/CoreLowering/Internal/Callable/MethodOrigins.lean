import Solcore.Frontend.SourceCoreCallableViews
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.PreparedMethods
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.MethodIdentity
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.Frontend.CorrelatedTypedSourceInstances
import Solcore.Frontend.SourceSpecializationAcceptance
import Solcore.Frontend.SourceStageAnalysisCongruence
import Solcore.SourceSemantics.SourceAnnotationSummaryUniqueness
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AppliedViews
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.Ancestry
import Solcore.SourceSemantics.SourceBodyResultAnnotation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.AncestryPaired
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.Frontend.SourceCoreCallablePairedAncestry
import Solcore.Frontend.SourceCoreCallablePairedAllocationFrames

/-!
# Method origins and resolution

Method resolver evidence and tables, origin tables and coherence, specialization identity, the seeds of paired ancestry, and paired emission.

The first two imports are in this order on purpose. The `DecidableEq` of trait evidence and the `LawfulBEq` of `ProgramPredicate` each have equal-priority instances in several modules, and Lean tries the last one imported first, so this order fixes which ones `validate`, `validateSelection` and `instDecidableCompatible` use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
/-! A retained method dictionary is accepted only when the actual method
materializer and the method caller's resolver produce the same complete list.
The validator preserves order, repeated goals and every nested evidence tree.
It is a static check and contains no Source or native execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
open Frontend SourceInference
open CallableNamedMetadata (environment evidence evidence_represents)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

/-- Actual accepted compiler materialization, together with the exact resolver
result required when that selected method becomes a caller. -/
structure Materialized (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) where
  dictionary : Dictionary
  materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
    .ok dictionary
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program
    selection.method.specialized.key selection.method.specialized.assumptions = .ok dictionary

/-- The check compares complete raw dictionaries, not merely their goals or
runtime projections. Rejection means this static producer is unavailable. -/
def validate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Option (Materialized program caller node selection) :=
  match materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection with
  | .error _ => none
  | .ok dictionary =>
      match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program
          selection.method.specialized.key selection.method.specialized.assumptions with
      | .error _ => none
      | .ok actual =>
          if same : actual = dictionary then
            some ⟨dictionary, materialized, same ▸ resolved⟩
          else none

variable {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
  {node : ExpressionNode} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}

/-- Matching the compiler's own accepted action transfers the receipt to its
exact retained dictionary. No equality supplied by a public caller is used. -/
def Materialized.for_actual (receipt : Materialized program caller node selection)
    {dictionary : Dictionary}
    (accepted : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
      .ok dictionary) :
    ResolvedCaller program selection.method.specialized (environment dictionary) := by
  have same : receipt.dictionary = dictionary := Except.ok.inj (receipt.materialized.symm.trans accepted)
  exact ⟨dictionary, same ▸ receipt.resolved, rfl⟩

/-- A successful per-position resolver spine reconstructs the genuine whole
resolver action at any specialization key. -/
theorem resolve_of_resolved {goals : List ProgramPredicate} {dictionary : Dictionary}
    (resolved : CallableCoercionEvidenceOrigins.Resolved program goals dictionary)
    (key : SourceCompilationPlan.Key) :
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key goals = .ok dictionary := by
  induction resolved with
  | nil => rfl
  | @cons goal raw goals rest head tail ih =>
      obtain ⟨semantic, represented, valid⟩ := TraitResolutionSoundness.resolve_success_evidenceValid head
      have same := represented.functional (evidence_represents raw)
      rw [same] at valid
      have goalEq : SourceCompilationPlan.runtimeEvidenceGoal raw = goal := by
        simpa only [CallableEvidenceEnvironment.evidence_goal] using valid.evidence_goal_eq
      cases raw with
      | byImpl actual implementation premises =>
          simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment, head]
          change actual = goal at goalEq
          simp [goalEq, ih]
          rfl

/-- Structural static proofs of every retained tree can construct the same
receipt without invoking the executable validator. -/
def of_resolved {dictionary : Dictionary}
    (materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
      .ok dictionary)
    (resolved : CallableCoercionEvidenceOrigins.Resolved program selection.method.specialized.assumptions dictionary) :
    Materialized program caller node selection :=
  ⟨dictionary, materialized, resolve_of_resolved resolved selection.method.specialized.key⟩

end Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
/-! A finite static validation traverses actual retained caller rows and their
original expression nodes. Every successful operator selection retains its
full materialized/resolved dictionary and actual caller header coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
open Core Frontend SourceInference
open CallableCoercionExpressionCertificates (rawNode)
open CallableMethodResolverEvidence (Materialized)

structure SelectedReady (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) where
  materialized : Materialized program caller node selection
  covered : CallableCoercionEvidenceOrigins.CallerCovered caller selection.method

def validateSelection (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Option (SelectedReady program caller node selection) := do
  let materialized ← CallableMethodResolverEvidence.validate program caller node selection
  if covered : selection.method.traitPredicates.all
      (fun goal => decide (goal ∈ caller.assumptions)) = true then
    return ⟨materialized, fun goal member =>
      of_decide_eq_true (List.all_eq_true.mp covered goal member)⟩
  else none

def select (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (requirements : List RequirementId)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) :
    Except SourceTypedRuntime.RuntimeError SourceCompilationPlan.CheckedRuntimeOperatorMethod :=
  match node.form with
  | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | _ => .error (.unsupportedRequirements requirements)

def NodeReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Prop :=
  ∀ requirements available selection,
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements →
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available →
    select program caller node requirements available = .ok selection →
    Nonempty (SelectedReady program caller (rawNode node requirements) selection)

/-- Errors in a selector cannot issue an operator receipt. A successful
selector must pass the additional complete-dictionary and coverage checks. -/
def validateNode (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Option (PLift (NodeReady program caller node)) :=
  match owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => some ⟨by
      intro requirements available selection ordinary _resolved _selected
      rw [owned] at ordinary
      cases ordinary⟩
  | some requirements =>
      match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
      | .error _ => some ⟨by
          intro requirements available selection _ordinary actualResolved _selected
          rw [resolved] at actualResolved
          cases actualResolved⟩
      | .ok available =>
          match selected : select program caller node requirements available with
          | .error _ => some ⟨by
              intro actualRequirements actualAvailable selection ordinary actualResolved actualSelected
              have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
              have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
              subst actualRequirements actualAvailable
              rw [selected] at actualSelected
              cases actualSelected⟩
          | .ok selection =>
              match validateSelection program caller (rawNode node requirements) selection with
              | none => none
              | some retained => some ⟨by
                  intro actualRequirements actualAvailable actualSelection ordinary actualResolved actualSelected
                  have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
                  have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
                  subst actualRequirements actualAvailable
                  have sameSelection := Except.ok.inj (selected.symm.trans actualSelected)
                  subst actualSelection
                  exact ⟨retained⟩⟩

def expressions (caller : SourceSpecialization.SpecializedFunction) : List ExpressionNode :=
  caller.function.typedBody.nodes.filterMap fun
    | .expression node => some node
    | _ => none

private def validateNodes (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction) :
    (nodes : List ExpressionNode) → Option (PLift (∀ node ∈ nodes, NodeReady program caller node))
  | [] => some ⟨by intro node member; cases member⟩
  | node :: nodes => do
      let ⟨head⟩ ← validateNode program caller node
      let ⟨tail⟩ ← validateNodes program caller nodes
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def Ready (program : CheckedProgram) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ caller ∈ rows, ∀ node ∈ expressions caller, NodeReady program caller node

/-- The finite producer is executable from the real retained source table.
Only a validated table can supply subsequent selected operator receipts. -/
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

/-- Actual lowering supplies the same owned requirement list, caller resolver
and selector equations checked by the finite table. -/
theorem Ready.operator {program : CheckedProgram}
    {rows : List SourceSpecialization.SpecializedFunction} (ready : Ready program rows)
    {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ rows)
    {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {output : SourceCoreBasic.LoweredExpr}
    (actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    Nonempty (SelectedReady program caller (rawNode node actual.requirements) actual.selection) := by
  have expressionMember : node ∈ expressions caller :=
    List.mem_filterMap.mpr ⟨.expression node, nodeMember, rfl⟩
  exact ready caller member node expressionMember actual.requirements actual.available actual.selection
    actual.ordinary actual.resolved actual.selectedMethod

end Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodSelectedRoots
/-! Executable recovery of the exact primary and ordered method roots from an
actual checked operator selection. This reuses the original requirement action
and retains all method premises without projecting their trees. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodSelectedRoots
open Frontend SourceInference
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

private def solvedRow (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId) :
    Except SourceTypedRuntime.RuntimeError SolvedRequirement :=
  match caller.function.solvedRequirements.filter (fun solved => decide (solved.id = requirement)) with
  | [] => .error (.missingSolvedRequirement caller.key occurrence requirement)
  | [solved] => .ok solved
  | solved => .error (.duplicateSolvedRequirements caller.key occurrence requirement solved.length)

def rawRoots (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : Dictionary)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Except SourceTypedRuntime.RuntimeError Dictionary := do
  let solved ← solvedRow caller node.id selection.primaryRequirement
  let primary ← SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available
    selection.primaryRequirement solved.predicate
  pure (primary :: selection.method.methodPremises)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem primary_row {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {id : RequirementId} {goal : ProgramPredicate}
    {raw : TypedTraitResolution.Evidence}
    (accepted : SourceCompilationPlan.exactRuntimeRequirementEvidence program caller node available id goal = .ok raw) :
    ∃ solved, solvedRow caller node.id id = .ok solved ∧
      solved.predicate = goal := by
  simp only [SourceCompilationPlan.exactRuntimeRequirementEvidence, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  obtain ⟨solved, found, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
  · rename_i same
    exact ⟨solved, found, by simpa using same⟩

/-- The recovered raw roots equal the complete roots retained by the authentic
selector certificate, including ordered and repeated method premises. -/
theorem of_certificate {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : Dictionary} {primary : RequirementId}
    {methodIds : List RequirementId} {arity : Nat} {name : String}
    {method : ExecutableImplMethods.CheckedMethod}
    (roots : CallableCoercionMethodCertificates.Roots program caller node available primary methodIds arity name method) :
    rawRoots program caller node available ⟨primary, method⟩ = .ok (roots.primary :: roots.methodEvidence) := by
  obtain ⟨solved, found, same⟩ := primary_row roots.primarySelected
  simp only [rawRoots, found, bind, Except.bind, same, roots.primarySelected,
    roots.methods, pure, Except.pure]

theorem of_source_receipt {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Core.Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output}
    (selected : CallablePreparedMethodSelection.SourceReceipt actual) :
    rawRoots program caller (CallableCoercionExpressionCertificates.rawNode node actual.requirements)
      actual.available actual.selection =
        .ok (selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence) :=
  of_certificate selected.certificate.roots

end Solcore.SourceSemantics.CoreLowering.CallableMethodSelectedRoots
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodOriginCoherence
/-! A finite validator compares the complete trees reachable from the actual
caller dictionary and selected roots. It imposes no global implementation
uniqueness condition on the checked program. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodOriginCoherence
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallableNamedMetadata (evidence environment)
abbrev Raw := TypedTraitResolution.Evidence
abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

def subtrees : Raw → List Raw
  | tree@(.byImpl _ _ premises) => tree :: premises.flatMap subtrees

theorem subtree_mem {raw : Raw} {tree : TraitEvidence}
    (subtree : EvidenceSubtree (evidence raw) tree) :
    ∃ found ∈ subtrees raw, evidence found = tree := by
  generalize eq : evidence raw = root at subtree
  induction subtree generalizing raw with
  | self root =>
    exact ⟨raw, by cases raw; simp [subtrees], eq⟩
  | @premise goal implementation premises premise selected member _ induction =>
    cases raw with
    | byImpl rawGoal rawImplementation rawPremises =>
      simp only [evidence, TraitEvidence.implementation.injEq] at eq
      obtain ⟨_, _, same⟩ := eq
      obtain ⟨child, childMember, childEq⟩ := List.mem_map.mp (same.symm ▸ member)
      obtain ⟨found, foundMember, foundEq⟩ := induction childEq
      refine ⟨found, ?_, foundEq⟩
      simpa only [subtrees] using List.mem_cons_of_mem (.byImpl rawGoal rawImplementation rawPremises)
        (List.mem_flatMap.mpr ⟨child, childMember, foundMember⟩)

private theorem lookup_member {caller : EvidenceEnvironment}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (found : caller.LooksUp goal tree) : (goal, tree) ∈ caller := by
  induction found with
  | head => simp
  | tail _ _ induction => exact List.mem_cons_of_mem _ induction

def candidates (caller roots : Dictionary) : Dictionary := caller ++ roots.flatMap subtrees

theorem origin_member {caller roots : Dictionary}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (origin : EvidenceEntryOriginates (environment caller) (roots.map evidence) goal tree) :
    ∃ raw ∈ candidates caller roots,
      SourceTypedRuntime.runtimeEvidenceGoal raw = goal ∧ evidence raw = tree := by
  cases origin with
  | caller found =>
    obtain ⟨raw, member, same⟩ := List.mem_map.mp (lookup_member found)
    exact ⟨raw, List.mem_append_left _ member, (Prod.mk.inj same).1, (Prod.mk.inj same).2⟩
  | root member subtree same =>
    obtain ⟨rawRoot, rawRootMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨raw, rawMember, rawEq⟩ := subtree_mem subtree
    refine ⟨raw, List.mem_append_right _
      (List.mem_flatMap.mpr ⟨rawRoot, rawRootMember, rawMember⟩), ?_, rawEq⟩
    have goalEq := (congrArg TraitEvidence.goal rawEq).trans same
    cases raw
    simpa only [evidence, TraitEvidence.goal, SourceTypedRuntime.runtimeEvidenceGoal,
      SourceCompilationPlan.runtimeEvidenceGoal] using goalEq

def Compatible (goals : List ProgramPredicate) (entries : Dictionary) : Prop :=
  ∀ first ∈ entries, ∀ second ∈ entries,
    SourceTypedRuntime.runtimeEvidenceGoal first ∈ goals →
    SourceTypedRuntime.runtimeEvidenceGoal first = SourceTypedRuntime.runtimeEvidenceGoal second →
    first = second

instance (goals : List ProgramPredicate) (entries : Dictionary) : Decidable (Compatible goals entries) :=
  inferInstanceAs (Decidable (∀ first ∈ entries, ∀ second ∈ entries,
    SourceTypedRuntime.runtimeEvidenceGoal first ∈ goals →
    SourceTypedRuntime.runtimeEvidenceGoal first = SourceTypedRuntime.runtimeEvidenceGoal second → first = second))

theorem coherent {caller roots : Dictionary} {goals : List ProgramPredicate}
    (checked : Compatible goals (candidates caller roots)) :
    RecursiveMethodOriginIdentity.Coherent (environment caller) (roots.map evidence) goals := by
  intro goal member left right first second
  obtain ⟨rawLeft, leftMember, leftGoal, leftEq⟩ := origin_member first
  obtain ⟨rawRight, rightMember, rightGoal, rightEq⟩ := origin_member second
  have same := checked rawLeft leftMember rawRight rightMember (leftGoal.symm ▸ member)
    (leftGoal.trans rightGoal.symm)
  exact leftEq.symm.trans ((congrArg evidence same).trans rightEq)

/-- Successful validation is a certificate about complete actual trees.
Order and repeated assumptions remain in the independent assembly relation. -/
def validate (caller roots : Dictionary) (goals : List ProgramPredicate) :
    Option (PLift (RecursiveMethodOriginIdentity.Coherent
      (environment caller) (roots.map evidence) goals)) :=
  if checked : Compatible goals (candidates caller roots) then
    some ⟨coherent checked⟩
  else none

end Solcore.SourceSemantics.CoreLowering.CallableMethodOriginCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodOriginTable
/-! A finite static validation traverses actual retained caller rows and their
original expression nodes. Every successful operator selection retains its
full materialized/resolved dictionary, actual caller header coverage and
coherence of only the actual caller and selected root trees. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodOriginTable
open Core Frontend SourceInference
open CallableCoercionExpressionCertificates (rawNode)
open CallableMethodResolverEvidence (Materialized)

abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

structure SelectedReady (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (available : Dictionary) (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod)
    extends CallableMethodResolverTable.SelectedReady program caller node selection where
  roots : Dictionary
  selectedRoots : CallableMethodSelectedRoots.rawRoots program caller node available selection = .ok roots
  coherent : RecursiveMethodOriginIdentity.Coherent (CallableNamedMetadata.environment available)
    (roots.map CallableNamedMetadata.evidence) selection.method.specialized.assumptions

def validateSelection (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (available : Dictionary) (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Option (SelectedReady program caller node available selection) := do
  let ordinary ← CallableMethodResolverTable.validateSelection program caller node selection
  match selectedRoots : CallableMethodSelectedRoots.rawRoots program caller node available selection with
  | .error _ => none
  | .ok roots => do
    let ⟨coherent⟩ ← CallableMethodOriginCoherence.validate available roots selection.method.specialized.assumptions
    return ⟨ordinary, roots, selectedRoots, coherent⟩

def select (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (requirements : List RequirementId)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) :
    Except SourceTypedRuntime.RuntimeError SourceCompilationPlan.CheckedRuntimeOperatorMethod :=
  match node.form with
  | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | _ => .error (.unsupportedRequirements requirements)

def NodeReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Prop :=
  ∀ requirements available selection,
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements →
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available →
    select program caller node requirements available = .ok selection →
    Nonempty (SelectedReady program caller (rawNode node requirements) available selection)

/-- Errors in a selector cannot issue an operator receipt. A successful
selector must pass the additional complete-dictionary, coverage and actual-root coherence checks. -/
def validateNode (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Option (PLift (NodeReady program caller node)) :=
  match owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => some ⟨by
      intro requirements available selection ordinary _resolved _selected
      rw [owned] at ordinary
      cases ordinary⟩
  | some requirements =>
      match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
      | .error _ => some ⟨by
          intro requirements available selection _ordinary actualResolved _selected
          rw [resolved] at actualResolved
          cases actualResolved⟩
      | .ok available =>
          match selected : select program caller node requirements available with
          | .error _ => some ⟨by
              intro actualRequirements actualAvailable selection ordinary actualResolved actualSelected
              have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
              have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
              subst actualRequirements actualAvailable
              rw [selected] at actualSelected
              cases actualSelected⟩
          | .ok selection =>
              match validateSelection program caller (rawNode node requirements) available selection with
              | none => none
              | some retained => some ⟨by
                  intro actualRequirements actualAvailable actualSelection ordinary actualResolved actualSelected
                  have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
                  have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
                  subst actualRequirements actualAvailable
                  have sameSelection := Except.ok.inj (selected.symm.trans actualSelected)
                  subst actualSelection
                  exact ⟨retained⟩⟩

def expressions (caller : SourceSpecialization.SpecializedFunction) : List ExpressionNode :=
  caller.function.typedBody.nodes.filterMap fun
    | .expression node => some node
    | _ => none

private def validateNodes (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction) :
    (nodes : List ExpressionNode) → Option (PLift (∀ node ∈ nodes, NodeReady program caller node))
  | [] => some ⟨by intro node member; cases member⟩
  | node :: nodes => do
      let ⟨head⟩ ← validateNode program caller node
      let ⟨tail⟩ ← validateNodes program caller nodes
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def Ready (program : CheckedProgram) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ caller ∈ rows, ∀ node ∈ expressions caller, NodeReady program caller node

/-- The finite producer is executable from the real retained source table.
Only a validated table can supply subsequent selected operator receipts. -/
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

/-- Actual lowering supplies the same owned requirement list, caller resolver
and selector equations checked by the finite table. -/
theorem Ready.operator {program : CheckedProgram}
    {rows : List SourceSpecialization.SpecializedFunction} (ready : Ready program rows)
    {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ rows)
    {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {output : SourceCoreBasic.LoweredExpr}
    (actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    Nonempty (SelectedReady program caller (rawNode node actual.requirements) actual.available actual.selection) := by
  have expressionMember : node ∈ expressions caller :=
    List.mem_filterMap.mpr ⟨.expression node, nodeMember, rfl⟩
  exact ready caller member node expressionMember actual.requirements actual.available actual.selection
    actual.ordinary actual.resolved actual.selectedMethod

/-- The finite certificate transfers to the exact independently retained roots
of any authentic receipt for this same operator selection. -/
theorem SelectedReady.at_source_receipt {program : CheckedProgram}
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {output : SourceCoreBasic.LoweredExpr}
    {actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output}
    (ready : SelectedReady program caller (rawNode node actual.requirements) actual.available actual.selection)
    (selected : CallablePreparedMethodSelection.SourceReceipt actual) :
    RecursiveMethodOriginIdentity.Coherent (CallableNamedMetadata.environment actual.available)
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map
        CallableNamedMetadata.evidence) actual.selection.method.specialized.assumptions := by
  have same := Except.ok.inj (ready.selectedRoots.symm.trans (CallableMethodSelectedRoots.of_source_receipt selected))
  exact same ▸ ready.coherent

end Solcore.SourceSemantics.CoreLowering.CallableMethodOriginTable
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
/-! Authentic compiler selection produces the same ordered roots used by
independent Source dictionary assembly at the reached lexical context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
open Core Frontend SourceInference Solcore.SourceSemantics.Dynamic
open CallablePreparedMethodSelection
open CallableNamedMetadata (evidence environment)

theorem roots_produced
    {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
    {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}
    (selected : SourceReceipt receipt)
    {context : Context}
    (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    RecursiveMethodOriginIdentity.RootsProduced context (environment receipt.available)
      receipt.requirements
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence) := by
  have head := CallableCoercionSourceSelection.requirement_produces signatures ledger assumptions
    receipt.resolved selected.certificate.roots.primarySelected selected.certificate.roots.primaryValid
  have tail := CallableCoercionSourceSelection.requirements_produce signatures ledger assumptions
    receipt.resolved selected.certificate.roots.methodsSelected selected.certificate.roots.methodsValid
  have result : RecursiveMethodOriginIdentity.RootsProduced context (environment receipt.available)
      (receipt.selection.primaryRequirement :: selected.methodIds)
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence) := by
    simpa only [environment, List.map_map, List.map_cons, Function.comp_def] using
      RecursiveMethodOriginIdentity.RootsProduced.intro head tail
  exact (congrArg (fun ids => RecursiveMethodOriginIdentity.RootsProduced context
    (environment receipt.available) ids
    ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map evidence))
    selected.requirements).mpr result

end Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationIdentity
/-!
Authentic ordinary-function origins and their shared contextual source identify
one original checked function. Declaration uniqueness is supplied by the
existing independent program validity, rather than inferred from a native type.

Implementation methods have a distinct stable method identity outside their
shared implementation-owned TypedSource. They are not covered by this result.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationIdentity

open Frontend SourceInference TypeSystem

/-- Source-owner preservation and the genuine ordinary catalog identify the
entire original checker record even when the two full specialization keys differ. -/
theorem generic_eq_of_sources {program : CheckedProgram}
    {leftSignature rightSignature : ProgramFunctionSignature}
    {leftGeneric rightGeneric : CheckedFunction}
    {leftSupplied rightSupplied : ParameterSubstitution}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftMember : leftGeneric ∈ program.functions)
    (rightMember : rightGeneric ∈ program.functions)
    (leftAccepted : SourceSpecialization.specializeFunction
      leftSignature leftGeneric leftSupplied = .ok left)
    (rightAccepted : SourceSpecialization.specializeFunction
      rightSignature rightGeneric rightSupplied = .ok right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using wellFormed.function_ids
  have leftOwner : (left.function.typedBody.applySubstitution leftLocal).owner =
      leftGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1]
    change leftGeneric.typedBody.owner = leftGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1
  have rightOwner : (right.function.typedBody.applySubstitution rightLocal).owner =
      rightGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
    change rightGeneric.typedBody.owner = rightGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    (leftOwner.symm.trans ((congrArg TypedSource.owner sameSource).trans rightOwner))

/-- The actual ordinary producer witnesses supply membership and both accepted
specializer equations internally. No common-template equation is an input. -/
theorem common_generic_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    ∃ leftSignature rightSignature generic leftSupplied rightSupplied,
      leftSignature ∈ program.signatures.functions ∧
      rightSignature ∈ program.signatures.functions ∧ generic ∈ program.functions ∧
      SourceSpecialization.specializeFunction leftSignature generic leftSupplied = .ok left ∧
      SourceSpecialization.specializeFunction rightSignature generic rightSupplied = .ok right := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, leftSignatureMember,
    leftMember, _, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, rightSignatureMember,
    rightMember, _, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_sources wellFormed leftMember rightMember
    leftAccepted rightAccepted sameSource
  subst rightGeneric
  exact ⟨leftSignature, rightSignature, leftGeneric, leftRequest.parameterSubstitution,
    rightRequest.parameterSubstitution, leftSignatureMember, rightSignatureMember,
    leftMember, leftAccepted, rightAccepted⟩

end Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationIdentity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
/-!
Two authentic ordinary specializations of the same contextual source recover
one original checked function. Its independent program typing constructs both
rigid body certificates, including their result annotations. The recovered
source and those annotations determine the enclosing result, original return
marker and stage analysis. Equal full keys are unnecessary.

Catalog-aware ordinary origins and complete raw range formation remain genuine
static inputs. Detached methods and extraction of these origins from every final
prepared row remain separate provenance boundaries.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
open Frontend SourceInference TypeSystem

private theorem original_annotation
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {facts : BodyFacts}
    {signatures : ProgramSignatures}
    (typed : BodyDefinitionHasType signatures signature.scheme.parameters
      signature.scheme.predicates signature.parameterNames signature.parameterTypes
      signature.parameterComptime signature.returnTypes signature.returnComptime
      (BodyDefinition.ofChecked generic) facts) :
    facts.type = generic.inferredBodyType := by
  cases typed with
  | intro _ _ _ _ _ resultEq _ _ _ _ _ _ _ _ _ annotation =>
      exact annotation.trans resultEq.symm

/-- The independent original body judgment and actual canonical specialization
construct both rigid typing and the annotation used to identify its result. -/
theorem annotated_body_of_program {program : CheckedProgram}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    ∃ context facts,
      BodyHasType specialized.function.typedBody context specialized.function.inferredBodyType facts ∧
      facts.type = specialized.function.inferredBodyType ∧
      NodeOccurrencesUnique specialized.function.typedBody := by
  have valid := wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedSignatureMember typedOwner typed =>
      have signatureEq : typedSignature = signature :=
        StructuralSubstitution.eq_of_mem_of_mapped_nodup
          wellFormed.signatures.function_ids typedSignatureMember signatureMember
          (typedOwner.symm.trans
            (RecursiveNamedSpecializationBodyFacts.identities accepted).1.symm)
      subst typedSignature
      have exactRange := RecursiveNamedSpecializationValidity.exact accepted
        (wellFormed.signatures.function_parameters signature signatureMember).1
      have rangeAfter :=
        StructuralSubstitution.ParameterSubstitution.RangeWellFormed.atApplyContextOfBase
          (context := declarationContext program.signatures generic.declaration
            signature.scheme.parameters signature.scheme.predicates generic.solvedRequirements) range
      obtain ⟨context, _inputs, bodyTyped⟩ :=
        StructuralSubstitution.BodyDefinitionHasType.instantiate
          (signatures := program.signatures)
          (assumptions := signature.scheme.predicates)
          (definition := BodyDefinition.ofChecked generic)
          specialized.parameterSubstitution wellFormed.signatures exactRange rangeAfter typed
      have annotation := original_annotation (signature := signature) (generic := generic) typed
      have bodyEq := RecursiveNamedSpecializationBodyFacts.body accepted
      have resultEq := RecursiveNamedSpecializationBodyFacts.result accepted
      refine ⟨context, StructuralSubstitution.applyBodyFacts specialized.parameterSubstitution facts,
        ?_, ?_, ?_⟩
      · rw [bodyEq, resultEq]
        exact bodyTyped
      · change specialized.parameterSubstitution.apply facts.type =
          specialized.function.inferredBodyType
        exact (congrArg specialized.parameterSubstitution.apply annotation).trans resultEq.symm
      · rw [bodyEq]
        exact (StructuralSubstitution.OccurrenceGraphClosed.applyParameters
          specialized.parameterSubstitution
          (StructuralSubstitution.BodyDefinitionHasType.graphClosed typed)).wellFormed.nodeOccurrencesUnique

/-- An actual ordinary origin supplies the selected catalog and original body
provenance; no body typing for a specialization is supplied by the caller. -/
theorem annotated_body_of_origin {program : CheckedProgram}
    {specialized : SourceSpecialization.SpecializedFunction}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (origin : RecursiveNamedPublicSpecializationMeaning.Origin program specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    ∃ context facts,
      BodyHasType specialized.function.typedBody context specialized.function.inferredBodyType facts ∧
      facts.type = specialized.function.inferredBodyType ∧
      NodeOccurrencesUnique specialized.function.typedBody := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := origin
  exact annotated_body_of_program wellFormed signatureMember genericMember accepted range

/-- Original identity, accepted rigid ranges and the complete typed-source
recovery derive the two inputs absent from a source-only analyzer congruence. -/
theorem source_and_result_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.parameterSubstitution)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.function.declaration = right.function.declaration ∧
      left.function.typedBody = right.function.typedBody ∧
      left.function.inferredBodyType = right.function.inferredBodyType ∧
      left.function.returnComptime = right.function.returnComptime := by
  obtain ⟨leftSignature, rightSignature, generic, leftSupplied, rightSupplied,
    _leftMember, _rightMember, _genericMember, leftAccepted, rightAccepted⟩ :=
    CallableOrdinarySpecializationIdentity.common_generic_of_origins
      wellFormed leftOrigin rightOrigin sameSource
  have leftFields := (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1
  have rightFields := (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1
  have rigidSame : left.function.typedBody = right.function.typedBody := by
    rw [leftFields, rightFields]
    exact CorrelatedTypedSourceInstances.apply_source_eq_of_equal_local_instances
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          leftAccepted parameter replacement found)
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          rightAccepted parameter replacement found)
      generic.typedBody leftLocal rightLocal
      (by simpa only [leftFields, rightFields, SourceSpecialization.applyCheckedFunction] using sameSource)
  obtain ⟨leftContext, leftFacts, leftTyped, leftAnnotation, unique⟩ :=
    annotated_body_of_origin wellFormed leftOrigin leftRange
  obtain ⟨rightContext, rightFacts, rightTyped, rightAnnotation, _rightUnique⟩ :=
    annotated_body_of_origin wellFormed rightOrigin rightRange
  have factsSame : leftFacts.type = rightFacts.type :=
    SourceAnnotationSummaryUniqueness.body_facts_type_eq unique leftTyped
      (by simpa only [rigidSame] using rightTyped)
  have resultSame := leftAnnotation.symm.trans (factsSame.trans rightAnnotation)
  refine ⟨?_, rigidSame, resultSame, ?_⟩
  · rw [leftFields, rightFields]
    rfl
  · rw [leftFields, rightFields]
    rfl

/-- The genuine two successful analyzers retain the same complete analysis.
The effective return Boolean is derived from original typing and provenance. -/
theorem analysis_eq_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.parameterSubstitution)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.stageAnalysis = right.stageAnalysis := by
  obtain ⟨sameDeclaration, rigidSame, resultSame, returnSame⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin leftRange rightRange sameSource
  obtain ⟨_, _, _, _, _, _, leftAccepted⟩ := leftOrigin
  obtain ⟨_, _, _, _, _, _, rightAccepted⟩ := rightOrigin
  exact SourceStageAnalysisCongruence.analysis_eq_of_success sameDeclaration rigidSame
    (by rw [resultSame, returnSame])
    (RecursiveNamedSpecializationStageFacts.analyzed leftAccepted)
    (RecursiveNamedSpecializationStageFacts.analyzed rightAccepted)

/-- Same-plan ordinary sidecars therefore agree in every literal guard-frame
field, even when their authenticated full specialization keys differ. -/
theorem ledger_frame_eq_of_origins {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.caller.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.caller.parameterSubstitution)
    (sameSource : left.caller.function.typedBody.applySubstitution leftLocal =
      right.caller.function.typedBody.applySubstitution rightLocal) :
    CallableLedger.frame left = CallableLedger.frame right := by
  obtain ⟨_sameDeclaration, _rigidSame, resultSame, returnSame⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin leftRange rightRange sameSource
  have analysisSame := analysis_eq_of_origins wellFormed leftOrigin rightOrigin
    leftRange rightRange sameSource
  have stagesSame : CallStageGuard.frame left.caller = CallStageGuard.frame right.caller := by
    simp only [CallStageGuard.frame, resultSame, returnSame, analysisSame]
  simp only [CallableLedger.frame, stagesSame, samePlan]

end Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationErasedStageCoherence
/-!
Requirement rewriting in an applied view preserves the source with requirement
lists erased. For two genuine ordinary specializations, this weaker equality
still identifies their original checked function. Its requirement profiles
survive both rigid and local substitution, recovering full equality of the two
canonical contextual sources and their original stage frames.

The rewritten applied source itself is not equated with a canonical source.
Actual ancestry receipts must supply the erased equality. Ordinary catalog
origins and full raw substitution formation remain explicit static inputs.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationErasedStageCoherence
open Frontend SourceInference TypeSystem CallableAncestryMetadata

private theorem rigid_profile (substitution : ParameterSubstitution) (source : TypedSource) :
    requirementProfile (SourceSpecialization.applyTypedSource substitution source) =
      requirementProfile source := by
  simp only [requirementProfile, SourceSpecialization.applyTypedSource, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

private theorem generic_eq_of_erased {program : CheckedProgram}
    {leftSignature rightSignature : ProgramFunctionSignature}
    {leftGeneric rightGeneric : CheckedFunction}
    {leftSupplied rightSupplied : ParameterSubstitution}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftMember : leftGeneric ∈ program.functions)
    (rightMember : rightGeneric ∈ program.functions)
    (leftAccepted : SourceSpecialization.specializeFunction
      leftSignature leftGeneric leftSupplied = .ok left)
    (rightAccepted : SourceSpecialization.specializeFunction
      rightSignature rightGeneric rightSupplied = .ok right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using wellFormed.function_ids
  have owners := congrArg TypedSource.owner erased
  change left.function.typedBody.owner = right.function.typedBody.owner at owners
  rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1] at owners
  change leftGeneric.typedBody.owner = rightGeneric.typedBody.owner at owners
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    ((RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1.symm.trans
      (owners.trans (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1))

/-- The original ordinary function supplies both requirement profiles. Neither
profile equality nor equality of the original templates is assumed. -/
theorem contextual_source_eq_of_erased {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, _leftSignatureMember,
    leftMember, _leftResolved, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, _rightSignatureMember,
    rightMember, _rightResolved, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_erased wellFormed leftMember rightMember
    leftAccepted rightAccepted erased
  subst rightGeneric
  apply FiniteProfiles.source_unique erased
  rw [CallableAncestryProfiles.profile_substitute, CallableAncestryProfiles.profile_substitute,
    (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
  change requirementProfile (SourceSpecialization.applyTypedSource
      left.parameterSubstitution leftGeneric.typedBody) =
    requirementProfile (SourceSpecialization.applyTypedSource
      right.parameterSubstitution leftGeneric.typedBody)
  rw [rigid_profile, rigid_profile]

/-- An erased-source correspondence suffices for ordinary canonical sidecars.
The existing typing and specialization proofs derive all stage-frame fields. -/
theorem ledger_frame_eq_of_erased {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (leftRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) left.caller.parameterSubstitution)
    (rightRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) right.caller.parameterSubstitution)
    (erased : eraseRequirements (left.caller.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.caller.function.typedBody.applySubstitution rightLocal)) :
    CallableLedger.frame left = CallableLedger.frame right :=
  CallableOrdinarySpecializationStageCoherence.ledger_frame_eq_of_origins
    wellFormed samePlan leftOrigin rightOrigin leftRange rightRange
    (contextual_source_eq_of_erased wellFormed leftOrigin rightOrigin erased)

end Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationErasedStageCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableOrdinaryAnnotationCoherence
/-!
Ordinary stage coherence follows from the original body's stored result
annotation. Raw replacement types need no separate formation premise: equal
rigid sources already contain every annotation used by that result.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableOrdinaryAnnotationCoherence
open Frontend SourceInference TypeSystem CallableAncestryMetadata

private theorem original_body {program : CheckedProgram} {generic : CheckedFunction}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (member : generic ∈ program.functions) :
    ∃ context facts, BodyHasType generic.typedBody context generic.inferredBodyType facts ∧
      facts.type = generic.inferredBodyType := by
  have valid := wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, member, rfl⟩)
  cases valid with
  | intro _ _ typed =>
      cases typed with
      | @intro lexicalContext _ _ _ _ _ resultType _ _ _ _ _ _ _ _ bodyTyped annotation =>
          refine ⟨lexicalContext, _, ?_, annotation.trans resultType.symm⟩
          rw [← resultType] at bodyTyped
          exact bodyTyped

/-- Actual ordinary origins and their equal contextual sources identify the
rigid source, annotated result and original return flag. -/
theorem source_and_result_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.function.declaration = right.function.declaration ∧
      left.function.typedBody = right.function.typedBody ∧
      left.function.inferredBodyType = right.function.inferredBodyType ∧
      left.function.returnComptime = right.function.returnComptime := by
  obtain ⟨leftSignature, rightSignature, generic, leftSupplied, rightSupplied,
    _leftMember, _rightMember, genericMember, leftAccepted, rightAccepted⟩ :=
    CallableOrdinarySpecializationIdentity.common_generic_of_origins
      wellFormed leftOrigin rightOrigin sameSource
  have leftFields := (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1
  have rightFields := (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1
  have rigidSame : left.function.typedBody = right.function.typedBody := by
    rw [leftFields, rightFields]
    exact CorrelatedTypedSourceInstances.apply_source_eq_of_equal_local_instances
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          leftAccepted parameter replacement found)
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          rightAccepted parameter replacement found)
      generic.typedBody leftLocal rightLocal
      (by simpa only [leftFields, rightFields, SourceSpecialization.applyCheckedFunction] using sameSource)
  obtain ⟨context, facts, typed, annotation⟩ := original_body wellFormed genericMember
  have sameAnnotation := SourceBodyResultAnnotation.parameter_instances_result_eq typed
    left.parameterSubstitution right.parameterSubstitution
    (by simpa only [RecursiveNamedSpecializationBodyFacts.body leftAccepted,
      RecursiveNamedSpecializationBodyFacts.body rightAccepted] using rigidSame)
  have resultSame : left.function.inferredBodyType = right.function.inferredBodyType := by
    rw [RecursiveNamedSpecializationBodyFacts.result leftAccepted,
      RecursiveNamedSpecializationBodyFacts.result rightAccepted]
    simpa only [annotation] using sameAnnotation
  refine ⟨?_, rigidSame, resultSame, ?_⟩
  · rw [leftFields, rightFields]; rfl
  · rw [leftFields, rightFields]; rfl

/-- Both successful analyzers therefore return the same complete analysis. -/
theorem analysis_eq_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.stageAnalysis = right.stageAnalysis := by
  obtain ⟨declarationEq, sourceEq, resultEq, returnEq⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin sameSource
  obtain ⟨_, _, _, _, _, _, leftAccepted⟩ := leftOrigin
  obtain ⟨_, _, _, _, _, _, rightAccepted⟩ := rightOrigin
  exact SourceStageAnalysisCongruence.analysis_eq_of_success declarationEq sourceEq
    (by rw [resultEq, returnEq])
    (RecursiveNamedSpecializationStageFacts.analyzed leftAccepted)
    (RecursiveNamedSpecializationStageFacts.analyzed rightAccepted)

/-- The full ledger frames agree, including when the sources are supplied
only through the actual requirement-erasure boundary. -/
theorem ledger_frame_eq_of_erased {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (sameSource : eraseRequirements (left.caller.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.caller.function.typedBody.applySubstitution rightLocal)) :
    CallableLedger.frame left = CallableLedger.frame right := by
  have exactSource :=
    CallableOrdinarySpecializationErasedStageCoherence.contextual_source_eq_of_erased
      wellFormed leftOrigin rightOrigin sameSource
  obtain ⟨_, _, resultEq, returnEq⟩ :=
    source_and_result_of_origins wellFormed leftOrigin rightOrigin exactSource
  have analysisEq := analysis_eq_of_origins wellFormed leftOrigin rightOrigin exactSource
  have stagesEq : CallStageGuard.frame left.caller = CallStageGuard.frame right.caller := by
    simp only [CallStageGuard.frame, resultEq, returnEq, analysisEq]
  simp only [CallableLedger.frame, stagesEq, samePlan]

end Solcore.SourceSemantics.CoreLowering.CallableOrdinaryAnnotationCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
/-!
Authentic paired ancestry retains the canonical source after erasing expression
requirement IDs. The actual named roots supply original specialization lookup;
the applied recipe keeps its rewritten source and cumulative semantic local
substitution. Native codebook contexts remain separate.

Both recursive selection constructors yield this correspondence. No full
substitution-only SourceReceipt, rewrite invariance, execution law or original
program typing is assumed or inferred.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open CallableAncestryMetadata

/-- The actual owned named seeds determine the original specialization for
any authenticated paired state, at arbitrary finite ancestry depth. -/
theorem authenticated_canonical
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ original,
      SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      eraseRequirements state.metadata.source =
        eraseRequirements (original.function.typedBody.applySubstitution state.metadata.active) := by
  have seeded := CallableAncestryPairedWorklist.named_roots_seeded inputs
  obtain ⟨root, member, valid⟩ :=
    CallableAncestryPairedValidation.authenticated_valid seeded
      (CallableAncestryPairedWorklist.named_roots_cover inputs) authenticated
  obtain ⟨original, selected, source, _sourceActive, _nativeActive⟩ := seeded root member
  refine ⟨original, ?_, ?_⟩
  · rw [valid.owner]
    exact selected
  · simpa only [source] using valid.canonical

/-- Exact descriptor origins and the lexical application owner identify the
same prepared sidecar. The source still contains all actual requirement rewrites. -/
theorem recipe_canonical
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {callerFrame lexicalFrame : SourceCoreCallablePairedFrames.Frame}
    {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
    {view target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical view target)
    {sidecar : Sidecar}
    (prepared : prepareSidecar base.plan sidecar.caller.key = .ok sidecar)
    (sameOwner : recipe.read.template.owner = sidecar.caller.key) :
    eraseRequirements (recipe.read.after lexical).metadata.source =
      eraseRequirements (sidecar.source.applySubstitution
        (recipe.read.substitution.compose lexical.metadata.active)) := by
  obtain ⟨original, selected, canonical⟩ := authenticated_canonical recipe.authenticated
  have viewOwner : recipe.read.template.owner = recipe.read.entry.view.owner :=
    (SourceCoreStageCodebook.Origin.lambda.inj
      (recipe.read.templateOrigin.symm.trans recipe.read.viewOrigin)).1
  have owner : (recipe.read.after lexical).metadata.owner = sidecar.caller.key := by
    change lexical.metadata.owner = sidecar.caller.key
    exact recipe.applied.owner.trans (viewOwner.symm.trans sameOwner)
  rw [owner] at selected
  have same : original = sidecar.caller :=
    Except.ok.inj (selected.symm.trans (LambdaSourceAlignment.sidecar_lookup prepared))
  subst original
  simpa only [Sidecar.source, SourceCoreCallableAncestryReadRecipes.Read.after] using canonical

/-- Every actual recursive selection retains its full scope and exact semantic
substitution while exposing a canonical source correspondence after erasure. -/
theorem selected_canonical
    {program : CheckedProgram} {plan : Plan} {table : SourceCoreStageCodebook.Table}
    {function : Dynamic.Closure} {selected : Staging.Recursive.Scope}
    (related : RecursiveStageRegistry.Selected program plan table function selected) :
    ∃ sidecar active,
      prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      selected = RecursiveStageRegistry.scope sidecar active function ∧
      eraseRequirements function.source =
        eraseRequirements (sidecar.source.applySubstitution active) := by
  cases related with
  | lambda prepared _ source _ _ =>
      exact ⟨_, _, prepared, rfl, congrArg eraseRequirements (source.source prepared)⟩
  | applied recipe _ samePlan _ prepared sameOwner _ source _ _ =>
      refine ⟨_, _, prepared, rfl, ?_⟩
      rw [source]
      exact recipe_canonical recipe (by simpa only [samePlan] using prepared) sameOwner

end Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
/-! The Source graph retained by a live closure and its authentic metadata
history have the same node shapes. Requirement rewriting is kept separate;
this does not identify the native candidate's complete compilation source. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
open Frontend SourceInference
open CallableAncestryMetadata LambdaMetadataViews

private theorem erased_nodes (nodes : List Node) :
    DataPatternValues.ListRel NodeView nodes (nodes.map eraseNodeRequirements) := by
  induction nodes with
  | nil => exact .nil
  | cons node nodes ih =>
    apply DataPatternValues.ListRel.cons _ ih
    cases node with
    | expression => exact .expression rfl rfl
    | statement => exact .statement _

theorem erased_view (source : TypedSource) :
    MetadataView source (eraseRequirements source) :=
  ⟨rfl, rfl, rfl, erased_nodes source.nodes⟩

theorem of_erased_eq {source metadata : TypedSource}
    (same : eraseRequirements source = eraseRequirements metadata) :
    MetadataView source metadata := by
  have left := erased_view source
  rw [same] at left
  exact left.trans (erased_view metadata).symm

/-- This correspondence follows from the actual finite paired history. It
does not require full Source equality at an applied read. -/
theorem of_pair
    {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleFunctions.Prepared checked}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    MetadataView source state.metadata.source :=
  of_erased_eq (CallableAppliedDynamicSourceMaterialization.erase_source paired).symm

end Solcore.SourceSemantics.CoreLowering.CallableIndependentSourceViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableLambdaRootReachability
/-! A path from a lambda's initializer and body roots either remains at the
initializer or enters its actual body. The executable lookup fixes that edge. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
open Frontend SourceInference TypeSystem CallableBodyMetadataViews

/-- Canonical reference paths from the initializer use its actual lambda
form. Every subsequent step belongs to the same body's root closure. -/
theorem Reaches.lambda_roots_cases {source : TypedSource}
    {initializer : ExpressionId} {lambda : ExpressionNode}
    {parameters : List TypedBinder} {result : Ty} {body : List StatementId}
    (found : source.lookupExpression? initializer = some lambda)
    (form : lambda.form = .lambda parameters result body)
    {node : NodeId} (path : Reaches source (lambdaRoots initializer body) node) :
    node = .expression initializer ∨ Reaches source (body.map NodeId.statement) node := by
  induction path with
  | root member =>
    rcases List.mem_cons.mp member with same | member
    · exact .inl same
    · exact .inr (.root member)
  | @expression id expression child parent selected edge ih =>
    rcases ih with same | reached
    · have sameId : id = initializer := NodeId.expression.inj same
      subst id
      have sameNode : expression = lambda := Option.some.inj (selected.symm.trans found)
      apply Or.inr
      apply Reaches.root
      simpa only [sameNode, form, ExpressionForm.references] using edge
    · exact .inr (.expression reached selected edge)
  | statement _ selected edge ih =>
    rcases ih with same | reached
    · cases same
    · exact .inr (.statement reached selected edge)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAppliedCodeScopeProvenance
/-! An actual applied read retains the full owner key of its lexical Code.
The read's descriptor and template refer to the same view owner, and its
sealed application receipt checks that owner against the lexical history.
Exact sidecar preparation then identifies the original caller and guard frame.
This does not identify a method from arbitrary selected-source equality or
assert that every Selected witness belongs to a supplied Code's ancestry. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedCodeScopeProvenance
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableIndexedHistory
open SourceCoreCallableAncestryReadRecipes

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  (history : History code)
  {caller : SourceCoreCallableAncestryReadRecipes.State} {view target : Word}
  (read : Read compiled.indexed.ancestry.graph.inputs caller view target)
  (applied : Applied read history.metadata)

include history applied

/-- The actual read and application checks recover the lexical Code's full
specialization key, including all declaration arguments. -/
theorem template_owner : read.template.owner = code.compilation.owner := by
  have sameOrigin : SourceCoreStageCodebook.Origin.lambda
      read.template.owner read.template.id read.template.active =
      .lambda read.entry.view.owner read.entry.view.principal.initializer
        read.entry.view.cumulative :=
    read.templateOrigin.symm.trans read.viewOrigin
  have sameOwner := (SourceCoreStageCodebook.Origin.lambda.inj sameOrigin).1
  exact sameOwner.trans (applied.owner.symm.trans history.owner)

/-- Two real preparations at the recovered key return the same complete
sidecar. No comparison of source tables or method body owners is needed. -/
theorem sidecar_eq {canonical selected : SourceCoreStageContracts.Sidecar}
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected) : selected = canonical := by
  rw [template_owner code history read applied] at selectedIssued
  exact Except.ok.inj (selectedIssued.symm.trans canonicalIssued)

/-- The resulting applied scope uses the original Code's complete guard
frame, independently of its accumulated semantic source substitution. -/
theorem guard_frame {canonical selected : SourceCoreStageContracts.Sidecar}
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected)
    (after : Dynamic.Closure) (active : TypeSystem.Substitution) :
    (RecursiveStageRegistry.scope selected active after).guards =
      CallableLedger.frame canonical := by
  rw [sidecar_eq code history read applied canonicalIssued selectedIssued]
  rfl

/-- Genuine principal support fixes the selected sidecar's entire retained
method specialization. Sibling methods are never identified by body owner. -/
theorem principal_caller
    (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
    {selected : SourceCoreStageContracts.Sidecar}
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      read.template.owner = .ok selected) :
    selected.caller = support.method.specialized := by
  have found := LambdaSourceAlignment.sidecar_lookup selectedIssued
  rw [template_owner code history read applied, support.compilation] at found
  change SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
    support.principal.named.signature.key = .ok selected.caller at found
  have same : selected.caller = support.principal.named.specialized :=
    Except.ok.inj (found.symm.trans support.principal.record)
  exact same.trans support.principal.cached.same

end Solcore.SourceSemantics.CoreLowering.CallableAppliedCodeScopeProvenance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
/-! Named seeding succeeds from actual codebook-origin receipts. This closes
the worklist's remaining seed premise without assuming successful runtime
execution or recovering source provenance from native function types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
open Frontend SourceInference TypeSystem CallableAncestryPairedLookup
open CallableAncestryPairedExpansion CallableAncestryPairedWorklist
abbrev State := SourceCoreCallableAncestryReadRecipes.State

private theorem named_exact {plan : SourceSpecializationWorklist.Plan} {owner : SourceSpecialization.SpecializationKey}
    {contract : SourceCoreStageContracts.Contract}
    (accepted : SourceCoreStageContracts.Contract.named plan owner = .ok contract) :
    ∃ caller, SourceCompilationPlan.exactSpecialization plan owner = .ok caller := by
  unfold SourceCoreStageContracts.Contract.named at accepted
  obtain ⟨sidecar, prepared, _⟩ := bind_ok accepted
  unfold SourceCoreStageContracts.prepareSidecar at prepared
  cases selected : SourceCompilationPlan.exactSpecialization plan owner with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at prepared
  | ok caller => exact ⟨caller, rfl⟩

private theorem origin_named {plan : SourceSpecializationWorklist.Plan} {owner : SourceSpecialization.SpecializationKey}
    {count : Nat} {contract : Option SourceCoreStageContracts.Contract}
    (receipt : CallEntryCertificates.OriginContract plan (.named owner) count contract) :
    ∃ original, SourceCoreStageContracts.Contract.named plan owner = .ok original := by
  cases receipt with
  | named prepared => exact ⟨_, prepared⟩

theorem named_total {checked : Checked} {base : Base checked} {inputs : Inputs base}
    (authentic : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries)
    {entry : SourceCoreStageCodebook.Entry} (member : entry ∈ inputs.callable.table.entries)
    {owner : SourceSpecialization.SpecializationKey} (origin : entry.origin = .named owner) :
    ∃ state, SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id = some state := by
  have receipt := authentic entry member
  unfold CallEntryCertificates.Authenticated at receipt
  rw [origin] at receipt
  obtain ⟨original, prepared⟩ := origin_named receipt
  obtain ⟨caller, selected⟩ := named_exact prepared
  refine ⟨⟨⟨owner, [], caller.function.typedBody⟩, []⟩, ?_⟩
  simp only [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?,
      CallableAncestryPairedValidation.stage_entry_self inputs.callable.table member, origin, selected,
      Except.toOption, bind, Option.bind, pure, Option.map_some]

private theorem forIn_total {α β ε : Type} (items : List α) (step : α → β → Except ε (ForInStep β))
    (invariant : β → Prop) (initial : β) (valid : invariant initial)
    (next : ∀ item ∈ items, ∀ state, invariant state →
      ∃ result, step item state = .ok (.yield result) ∧ invariant result) :
    ∃ final, forIn items initial step = .ok final ∧ invariant final := by
  induction items generalizing initial with
  | nil => exact ⟨initial, rfl, valid⟩
  | cons head tail ih =>
    obtain ⟨after, executed, maintained⟩ := next head (by simp) initial valid
    obtain ⟨final, finished, preserved⟩ := ih after maintained (fun item member => next item (by simp [member]))
    refine ⟨final, ?_, preserved⟩
    simpa only [List.forIn_cons, executed, bind, Except.bind] using finished

theorem seed_total {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (authentic : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries) :
    ∃ initial, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial := by
  let step : SourceCoreStageCodebook.Entry → Table → Except SourceCoreCallableAncestryPairedPreparation.Error (ForInStep Table) :=
    fun entry table => do
      match entry.origin with
      | .named _ =>
        let state ← match SourceCoreCallableAncestryPairedPreparation.named? inputs entry.id with
          | none => throw (.invalidNamed entry.id) | some state => pure state
        let (destination, states) ← SourceCoreCallableAncestryPairedPreparation.intern table.states state
        pure (.yield {table with states, named := table.named ++ [⟨entry.id, destination⟩]})
      | _ => pure (.yield table)
  obtain ⟨initial, completed, _⟩ := forIn_total inputs.callable.table.entries step
    (fun table => StatesValid inputs table.states) ⟨[], [], [], []⟩ ⟨by simp, by simp⟩ (by
      intro entry member table previous
      dsimp only [step]
      cases origin : entry.origin with
      | named owner =>
        obtain ⟨state, selected⟩ := named_total authentic member origin
        obtain ⟨destination, states, interned, maintained, _, _⟩ := intern_total previous ⟨.named entry.id, .named selected⟩
        refine ⟨{table with states, named := table.named ++ [⟨entry.id, destination⟩]}, ?_, maintained⟩
        simp only [selected, interned, pure, Except.pure, bind, Except.bind]
      | lambda owner id active => exact ⟨table, rfl, previous⟩
      | builtin builtin => exact ⟨table, rfl, previous⟩)
  refine ⟨initial, ?_⟩
  change (forIn inputs.callable.table.entries ⟨[], [], [], []⟩ step >>= fun result => Except.ok result) = .ok initial
  simp only [completed, bind, Except.bind]

/-- A codebook prepared for the actual executable plan supplies every named
seed. All later worklist phases are total with the computed finite bound. -/
theorem completion_of_codebook {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {projectType : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (prepared : SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan projectType limits firstId = .ok inputs.callable.table) :
    ∃ initial final, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial ∧
      SourceCoreCallableAncestryPairedPreparation.saturate inputs
        (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      SourceCoreCallableAncestryPairedPreparation.valid inputs final = true ∧
      ∃ recipes, final.views.attach.mapM (fun edge =>
        SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs final edge.val edge.property) = .ok recipes := by
  obtain ⟨initial, seeded⟩ := seed_total inputs (CallEntryCertificates.prepareWithProjection_authenticates prepared)
  obtain ⟨final, completed, validated, recipes⟩ := CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  exact ⟨initial, final, seeded, completed, validated, recipes⟩


private theorem mapError_ok {α ε δ : Type} {result : Except ε α} {value : α} {f : ε → δ}
    (accepted : result.mapError f = .ok value) : result = .ok value := by
  cases result with
  | error => cases accepted
  | ok selected => cases accepted; rfl

/-- Recover actual codebook provenance from the compatible compiler factory.
The native table's shape alone is not used as a source-ownership receipt. -/
theorem factory_authenticated {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (inputs : Inputs base) : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨actualPlan, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    have absent := inputs.callableSelected
    cases absent
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, tablePrepared, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      have same : ({table, diagnostics := callableDiagnostics} : SourceCoreGeneralFunctions.CallableContext) = inputs.callable :=
        Option.some.inj inputs.callableSelected
      have authenticated := CallEntryCertificates.prepareWithProjection_authenticates (mapError_ok tablePrepared)
      simpa only [← same] using authenticated
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      have absent := inputs.callableSelected
      cases absent


/-- Once the compatible compiler and input metadata preparation succeed, the
paired cache factory cannot fail at named seeding, queue saturation, closure
validation, or per-edge recipe preparation. Input-metadata preparation and
native runtime-frame coverage remain separate obligations. -/
theorem preparation_total {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared, SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared := by
  obtain ⟨initial, seeded⟩ := seed_total inputs (factory_authenticated compiled inputs)
  obtain ⟨final, completed, validated, recipes, recipesPrepared⟩ :=
    CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  unfold SourceCoreCallableAncestryPairedPreparation.prepare
  simp only [inputsPrepared, Except.mapError, bind, Except.bind]
  split
  · next error impossible => simp [seeded] at impossible
  · next actualInitial selected =>
    have same := Except.ok.inj (selected.symm.trans seeded)
    subst actualInitial
    split
    · next error impossible => simp [completed] at impossible
    · next actualFinal selected =>
      have same := Except.ok.inj (selected.symm.trans completed)
      subst actualFinal
      split
      · split
        · next error impossible => simp [recipesPrepared] at impossible
        · exact ⟨_, rfl⟩
      · next impossible => exact False.elim (impossible validated)

end Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol
/-! Finite laws for the emitted paired-frame protocol with carried metadata
history. A loaded value is not authenticated merely by its native type or ID.
Stable frames carry independent metadata authentication; the transient read tag
retains its actual read factory receipt and read-time caller. Body execution
remains an explicit compositional premise in its real administrative context.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol
open Core Frontend CallableAncestryPairedLookup
open SourceCoreCallablePairedFrames
open DataEquality (Selects)
abbrev MetadataState := SourceCoreCallableAncestryReadRecipes.State
abbrev PairedFrame := SourceCoreCallablePairedFrames.Frame

/-- Transient tags are protocol states, not principal execution-source states.
Only stable frames are passed to the principal metadata lookup theorem. -/
inductive Current {checked : Checked} {base : Base checked} (inputs : Inputs base) : PairedFrame → Prop where
  | stable {frame : PairedFrame} {state : Option MetadataState}
      (history : Authenticates inputs frame state) : Current inputs frame
  | reading {caller : PairedFrame} {state : MetadataState} {id target : Word}
      (history : Authenticates inputs caller (some state))
      (read : SourceCoreCallableAncestryReadRecipes.Read inputs state id target)
      (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs state id target = .ok read) :
      Current inputs (.view id target caller)

structure CellState {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (layout : Layout) (location : Location) (frame : PairedFrame) (store : Store) : Prop where
  read : store.read? location = some (encode layout frame)
  history : Current inputs frame

/-- A lambda's exact descriptor transition is separate from its native type.
Applied views authenticate the read caller and lexical principal separately. -/
inductive Entry {checked : Checked} {base : Base checked} (inputs : Inputs base) (origin : Word)
    (lexical : PairedFrame) : PairedFrame → MetadataState → Prop where
  | ordinary {current : PairedFrame} {state : MetadataState}
      (history : Authenticates inputs lexical (some state))
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state origin = true)
      (unmatched : ∀ id caller, current ≠ .view id origin caller) : Entry inputs origin lexical current state
  | applied {caller : PairedFrame} {callerState lexicalState : MetadataState} {id : Word}
      (callerHistory : Authenticates inputs caller (some callerState))
      (lexicalHistory : Authenticates inputs lexical (some lexicalState))
      (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id origin)
      (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id origin = .ok read)
      (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexicalState)
      (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexicalState = .ok applied) :
      Entry inputs origin lexical (.view id origin caller) (read.after lexicalState)

theorem Entry.authenticates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {origin : Word} {lexical current : PairedFrame} {state : MetadataState}
    (entry : Entry inputs origin lexical current state) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) := by
  cases entry with
  | ordinary history allowed unmatched =>
    have same : selectedFrame origin lexical current = .lambda origin lexical := by
      cases current <;> simp only [selectedFrame]
      next id target caller =>
        by_cases sameTarget : target = origin
        · subst target; exact False.elim (unmatched id caller rfl)
        · simp only [sameTarget, ↓reduceIte]
    rw [same]
    exact .lambda history allowed
  | applied callerHistory lexicalHistory read readPrepared applied appliedPrepared =>
    simp only [selectedFrame, ↓reduceIte]
    apply Authenticates.appliedView callerHistory lexicalHistory
    simp only [SourceCoreCallableAncestryPairedPreparation.view?, readPrepared, appliedPrepared,
      Except.toOption, bind, Option.bind, pure]

private theorem lambda_selected {layout : Layout} {environment : Environment} {lexical : Expr}
    {frame : PairedFrame} (selected : Selects environment lexical (encode layout frame))
    (origin : Word) (store : Store) :
    Evaluates environment store (lambda layout origin lexical) (encode layout (.lambda origin frame)) store :=
  .construct (.pair .word (selected.evaluates store))

/-- The actual hook reads the current frame from the administrative cell.
That read may be a native expression; it must preserve the store. -/
theorem lambdaFrame_read {layout : Layout} {environment : Environment} {store : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} (origin : Word)
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentRead : Evaluates environment store current (encode layout currentFrame) store) :
    Evaluates environment store (lambdaFrame layout origin lexical current)
      (encode layout (selectedFrame origin lexicalFrame currentFrame)) store := by
  cases currentFrame with
  | empty =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken .unit) origin store)
  | named id =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.word id)) origin store)
  | lambda id parent =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected (lexicalSelected.weaken (.pair (.word id) (encode layout parent))) origin store)
  | view id target caller =>
    apply Evaluates.matchData currentRead rfl rfl
    by_cases equal : target = origin
    · simp only [selectedFrame, if_pos equal]
      apply Evaluates.ifTrue (.binary (.first (.second (.var rfl))) .word ?_)
      · exact .construct (.pair (.first (.var rfl)) (.pair .word
          (.pair (.second (.second (.var rfl))) ((lexicalSelected.weaken _).evaluates store))))
      · simp [BinaryOp.apply, equal]
    · simp only [selectedFrame, if_neg equal]
      apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) .word ?_)
      · simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
          (lexicalSelected.weaken (.pair (.word id) (.pair (.word target) (encode layout caller)))) origin store
      · simp [BinaryOp.apply, equal]
  | appliedView id target caller saved =>
    exact .matchData currentRead rfl rfl (by
      simpa [lambda, Expr.weakenAt, selectedFrame] using lambda_selected
        (lexicalSelected.weaken (.pair (.word id) (.pair (.word target)
          (.pair (encode layout caller) (encode layout saved))))) origin store)

theorem lambdaFrame_read_reflects {layout : Layout} {environment : Environment} {before after : Store}
    {lexical current : Expr} {lexicalFrame currentFrame : PairedFrame} {origin : Word} {result : Value}
    (lexicalSelected : Selects environment lexical (encode layout lexicalFrame))
    (currentRead : Evaluates environment before current (encode layout currentFrame) before)
    (evaluated : Evaluates environment before (lambdaFrame layout origin lexical current) result after) :
    result = encode layout (selectedFrame origin lexicalFrame currentFrame) ∧ after = before :=
  evaluation_deterministic evaluated (lambdaFrame_read origin lexicalSelected currentRead)

/-- The saved source ancestry is exactly the value loaded at lambda creation,
including the actual native environment order used by snapshotLambda. -/
def LambdaSnapshot {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (layout : Layout) (origin : Word) (referenceIndex : Nat) (parameter result : Ty) (body : Expr)
    (environment : Environment) (value : Value) : Prop :=
  ∃ (frame : PairedFrame) (state : MetadataState), Authenticates inputs frame (some state) ∧
    value = .closure parameter (LanguageResult.resultType result)
    (withFrame (.var (referenceIndex + 2))
      (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
    (encode layout frame :: environment)

theorem snapshotLambda_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {parameter result : Ty} {body : Expr}
    {environment : Environment} {store : Store} {frame : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (read : store.read? location = some (encode layout frame))
    (history : Authenticates inputs frame (some state)) :
    ∃ value, Evaluates environment store
      (SourceCoreCallablePairedAncestry.snapshotLambda layout origin referenceIndex parameter result body) value store ∧
      LambdaSnapshot inputs layout origin referenceIndex parameter result body environment value :=
  ⟨_, SourceCoreCallablePairedAncestry.snapshotLambda_evaluates origin reference read, ⟨frame, state, history, rfl⟩⟩

/-- Allocation snapshots retain the actual stable creation frame at the new
administrative index. The source allocation runs in its real inserted slot. -/
theorem snapshotBefore_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {reference allocation : Expr} {location : Location} {frame : PairedFrame} {state : Option MetadataState}
    {environment : Environment} {before after : Store} {result : Value}
    (selected : Selects environment reference (.cellRef layout.type location))
    (read : before.read? location = some (encode layout frame))
    (history : Authenticates inputs frame state)
    (evaluated : Evaluates (.cellRef layout.type before.length :: environment) (before ++ [encode layout frame])
      (allocation.weakenAt 0) result after) :
    Evaluates environment before (SourceCoreCallablePairedAllocationFrames.snapshotBefore layout reference allocation) result after ∧
    (before ++ [encode layout frame]).read? before.length = some (encode layout frame) ∧ Authenticates inputs frame state := by
  exact ⟨.letE (.newCell (.loadCell (selected.evaluates before) read)) evaluated, by simp [Store.read?], history⟩


private theorem installed_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {location : Location} {before : Store} {old frame : PairedFrame}
    (read : before.read? location = some (encode layout old)) (history : Current inputs frame) :
    CellState inputs layout location frame (before.set location (encode layout frame)) := by
  have written : before.write? location (encode layout frame) = some (before.set location (encode layout frame)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, history⟩

/-- The exact lambda-body selector after withFrame saves the caller. This
lemma evaluates the emitted load, including its real additional binder. -/
theorem lambda_next_evaluates {layout : Layout} {environment : Environment} {before : Store}
    {referenceIndex location : Nat} {lexical current : PairedFrame} (origin : Word)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (lexicalSelected : environment[1]? = some (encode layout lexical))
    (read : before.read? location = some (encode layout current)) :
    Evaluates (encode layout current :: environment) before
      ((lambdaFrame layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0)
      (encode layout (selectedFrame origin lexical current)) before := by
  have shifted : (lambdaFrame layout origin (.var 1) (.loadCell (.var referenceIndex))).weakenAt 0 =
      lambdaFrame layout origin (.var 2) (.loadCell (.var (referenceIndex + 1))) := by
    simp [lambdaFrame, lambda, Expr.weakenAt]
  rw [shifted]
  exact lambdaFrame_read origin (.var lexicalSelected) (.loadCell (.var (by simpa using reference)) read)

/-- Actual emitted lambda-body entry installs an authenticated execution frame
and restores its exact caller, even when the result is a language failure.
The child runs under all four administrative/argument slots actually emitted. -/
theorem lambda_body_evaluates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {lexical current : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after) :
    CellState inputs layout location (selectedFrame origin lexical current)
        (before.set location (encode layout (selectedFrame origin lexical current))) ∧
    Evaluates (argument :: encode layout lexical :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      result (after.set location (encode layout current)) ∧
    CellState inputs layout location current (after.set location (encode layout current)) := by
  have selected : Selects (argument :: encode layout lexical :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  have next := lambda_next_evaluates (referenceIndex := referenceIndex + 2) origin (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout lexical :: environment)[1]? = some (encode layout lexical) from rfl) caller.read
  have evaluated := CallableContextFrames.withFrame_evaluates selected caller.read next bodyEvaluation
  exact ⟨installed_history caller.read (.stable entry.authenticates), evaluated,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluated).1, caller.history⟩⟩

/-- Completed emitted code exposes the real body trace and exact restoration;
no successful source trace is a premise of this inversion. -/
theorem lambda_body_reflects {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before finalStore : Store}
    {lexical current : PairedFrame} {state : MetadataState}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (evaluation : Evaluates (argument :: encode layout lexical :: environment) before
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1)) result finalStore) :
    Authenticates inputs (selectedFrame origin lexical current) (some state) ∧
    (∃ bodyStore, Evaluates (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location (encode layout current)) ∧
    CellState inputs layout location current finalStore := by
  have selected : Selects (argument :: encode layout lexical :: environment)
      (.var (referenceIndex + 2)) (.cellRef layout.type location) := .var (by simpa [Nat.add_assoc] using reference)
  obtain ⟨installed, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects selected caller.read evaluation
  have expected := lambda_next_evaluates (referenceIndex := referenceIndex + 2) origin (by simpa [Nat.add_assoc] using reference)
    (show (argument :: encode layout lexical :: environment)[1]? = some (encode layout lexical) from rfl) caller.read
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation expected
  exact ⟨entry.authenticates, ⟨bodyStore, bodyEvaluation, finalEq⟩,
    ⟨(CallableContextFrames.withFrame_restores selected caller.read evaluation).1, caller.history⟩⟩


/-- A read wrapper captures the actual successful read's caller. Its lexical
payload is passed through exactly; authenticating that payload is an independent
lambda-snapshot receipt, not a consequence of its projected function type. -/
theorem viewLower_history {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {environment : Environment} {before after : Store} {readCode : Expr}
    {parameter result : Ty} {id target descriptor : Word} {referenceIndex location : Nat}
    {identity originalPayload : Value} {caller : PairedFrame} {callerState : MetadataState}
    (history : Authenticates inputs caller (some callerState))
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs callerState id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead inputs callerState id target = .ok read)
    (evaluated : Evaluates environment before readCode
      (.inRight .word (.pair (.pair identity originalPayload) (.word descriptor))) after)
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (snapshot : after.read? location = some (encode layout caller)) :
    Evaluates environment before (SourceCoreCallablePairedAncestry.viewLower layout parameter result id target referenceIndex readCode)
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result)
          (SourceCoreCallablePairedAncestry.viewBody layout id target referenceIndex)
          (encode layout caller :: .pair (.pair identity originalPayload) (.word descriptor) :: environment))) (.word descriptor))) after ∧
    Current inputs (.view id target caller) :=
  ⟨SourceCoreCallablePairedAncestry.viewLower_evaluates evaluated reference snapshot, .reading history read prepared⟩

/-- Named entry resets execution metadata to its exact named plan receipt,
then restores the previous stable or transient protocol frame on completion. -/
theorem named_body_evaluates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {environment : Environment} {before after : Store} {body : Expr}
    {referenceIndex location : Nat} {origin : Word} {state : MetadataState} {caller : PairedFrame} {result : Value}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (saved : CellState inputs layout location caller before)
    (namedReceipt : SourceCoreCallableAncestryPairedPreparation.named? inputs origin = some state)
    (bodyEvaluation : Evaluates (.unit :: encode layout caller :: environment)
      (before.set location (encode layout (.named origin))) ((body.weakenAt 0).weakenAt 0) result after) :
    CellState inputs layout location (.named origin) (before.set location (encode layout (.named origin))) ∧
    Evaluates environment before (withFrame (.var referenceIndex) (named layout origin) body)
      result (after.set location (encode layout caller)) ∧
    CellState inputs layout location caller (after.set location (encode layout caller)) := by
  have next : Evaluates (encode layout caller :: environment) before ((named layout origin).weakenAt 0)
      (encode layout (.named origin)) before := by
    simpa [named, Expr.weakenAt, encode] using
      (show Evaluates (encode layout caller :: environment) before (.construct layout.named (.word origin))
        (.constructed layout.named (.word origin)) before from .construct .word)
  have evaluated := CallableContextFrames.withFrame_evaluates (.var reference) saved.read next bodyEvaluation
  exact ⟨installed_history saved.read (.stable (.named namedReceipt)), evaluated,
    ⟨(CallableContextFrames.withFrame_restores (.var reference) saved.read evaluated).1, saved.history⟩⟩

/-- Pending execution keeps its real checkpoint. The native resumption law
preserves the eventual caller restoration; it does not call exhaustion a
source completion or claim the caller is installed while execution is paused. -/
theorem lambda_body_resumed_finishes {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {layout : Layout} {origin : Word} {referenceIndex location : Nat} {body : Expr}
    {environment : Environment} {argument result : Value} {before after : Store}
    {lexical current : PairedFrame} {state : MetadataState} {spent : Nat} {checkpoint : Core.State}
    (reference : environment[referenceIndex]? = some (.cellRef layout.type location))
    (caller : CellState inputs layout location current before)
    (entry : Entry inputs origin lexical current state)
    (bodyEvaluation : Evaluates
      (.unit :: encode layout current :: argument :: encode layout lexical :: environment)
      (before.set location (encode layout (selectedFrame origin lexical current)))
      (((body.weakenAt 1).weakenAt 0).weakenAt 0) result after)
    (exhausted : runStateful spent (.initial
      (withFrame (.var (referenceIndex + 2))
        (lambdaFrame layout origin (.var 1) (.loadCell (.var (referenceIndex + 2)))) (body.weakenAt 1))
      (argument :: encode layout lexical :: environment) before) = .outOfFuel checkpoint) :
    ∃ remaining, ∀ additional, remaining ≤ additional →
      runStateful additional checkpoint = .done result (after.set location (encode layout current)) := by
  have evaluated := (lambda_body_evaluates reference caller entry bodyEvaluation).2.1
  obtain ⟨required, sufficient⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨required, fun additional enough => by
    rw [runStateful_resume exhausted additional]
    exact sufficient _ (by omega)⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePairedEmission
/-! Static receipts from the actual paired compiler hooks. These identify the
emitted native helper and descriptor lookup; finite protocol lemmas carry the
separate dynamic metadata history. Neither layer infers history from a Word. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedEmission
open Core Frontend SourceInference
open SourceCoreCallablePairedAncestry

private theorem key_eq_of_beq (left right : Key) (accepted : (left == right) = true) : left = right := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializationKey SourceSpecialization.instBEqSpecializationKey.beq at accepted
  simp only [Bool.and_eq_true, beq_iff_eq] at accepted
  simp_all

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

/-- The hook's selected word belongs to its actual base callable table. -/
theorem originId_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (accepted : originId prepared origin = .ok id) :
    ∃ native, base.callableContext = some native ∧ native.table.idAt? origin = some id := by
  unfold originId at accepted
  split at accepted
  · next native selected =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · next actual found =>
      cases accepted
      exact ⟨native, selected, found⟩
    · cases accepted
  · cases accepted

/-- A successful actual lambda expression hook emits this exact snapshot
helper with the source occurrence's owned descriptor. Header checks and source
owner checks are retained independently of any runtime closure value. -/
theorem expressionHook_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = snapshotLambda prepared.layout.frame origin (creationReferenceIndex context scope) parameter result body := by
  by_cases globals : (context.owner != owner || context.globals != base.globals) = true
  · simp [expressionHook, globals, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · have checkedGlobals : (context.owner == owner) = true ∧ context.globals = base.globals := by
      simpa [bne] using globals
    have globalsEq : context.owner = owner ∧ context.globals = base.globals :=
      ⟨key_eq_of_beq _ _ checkedGlobals.1, checkedGlobals.2⟩
    cases originSelected : originId prepared (.lambda owner node.id active) with
    | error error => simp [expressionHook, globals, originSelected, bind, Except.bind] at accepted
    | ok origin =>
      obtain ⟨native, nativeSelected, selected⟩ := originId_receipt prepared originSelected
      cases raw <;> simp only [expressionHook, globals, originSelected, pure, Except.pure, bind, Except.bind] at accepted
      all_goals try cases accepted
      next actualParameter actualResult body =>
        by_cases header : (actualParameter != parameter || actualResult != LanguageResult.resultType result) = true
        · simp [header, throw, throwThe, MonadExceptOf.throw] at accepted
        · have headerChecks : (actualParameter == parameter) = true ∧ (actualResult == LanguageResult.resultType result) = true := by
            simpa [bne] using header
          have headerEq := And.intro ((type_beq _ _).mp headerChecks.1) ((type_beq _ _).mp headerChecks.2)
          by_cases ownerEq : (source.owner != owner.declaration) = true
          · simp [header, ownerEq, throw, throwThe, MonadExceptOf.throw] at accepted
          · have sourceOwner : source.owner = owner.declaration := by simpa using ownerEq
            simp [header, ownerEq] at accepted
            exact ⟨native, origin, body, nativeSelected, selected, by simp only [headerEq.1, headerEq.2],
              globalsEq.1, globalsEq.2, sourceOwner, accepted.symm⟩

theorem namedBody_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ native origin, base.callableContext = some native ∧
      native.table.idAt? (.named function.signature.key) = some origin ∧
      output = SourceCoreCallablePairedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallablePairedFrames.named prepared.layout.frame origin) body := by
  unfold namedBody at accepted
  obtain ⟨origin, selected, accepted⟩ := CallableAncestryPairedExpansion.bind_ok accepted
  cases accepted
  obtain ⟨native, nativeSelected, originSelected⟩ := originId_receipt prepared selected
  exact ⟨native, origin, nativeSelected, originSelected, rfl⟩


/-- A real successful expression hook creates exactly a closure retaining the
current authenticated source metadata and the original lexical environment. -/
theorem expressionHook_history {checked : Checked} {base : Base checked}
    (prepared : Prepared base) {inputs : CallableAncestryPairedLookup.Inputs base}
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {store : Store} {location : Location}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallablePairedFrames.encode prepared.layout.frame frame))
    (history : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ native origin body value, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      Evaluates environment store output value store ∧
      CallablePairedProtocol.LambdaSnapshot inputs prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨native, origin, body, nativeSelected, originSelected, rawShape, _, _, _, rfl⟩ := expressionHook_receipt prepared accepted
  obtain ⟨value, evaluated, snapshot⟩ := CallablePairedProtocol.snapshotLambda_history reference read history
  exact ⟨native, origin, body, value, nativeSelected, originSelected, rawShape, evaluated, snapshot⟩

/-- Every completed execution of this emitted formation helper keeps precisely
the same saved frame and capture order, with no new heap effects. -/
theorem expressionHook_reflects {checked : Checked} {base : Base checked}
    (prepared : Prepared base) {inputs : CallableAncestryPairedLookup.Inputs base}
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {before after : Store} {location : Location} {value : Value}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallablePairedFrames.encode prepared.layout.frame frame))
    (history : CallableAncestryPairedLookup.Authenticates inputs frame (some state))
    (evaluated : Evaluates environment before output value after) :
    after = before ∧ ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      CallablePairedProtocol.LambdaSnapshot inputs prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨native, origin, body, expected, nativeSelected, originSelected, rawShape, expectedEval, snapshot⟩ :=
    expressionHook_history prepared accepted reference read history
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expectedEval
  exact ⟨rfl, native, origin, body, nativeSelected, originSelected, rawShape, snapshot⟩

/-- The actual named-body hook selects a successful named metadata seed from
the codebook generated by the same compatible compiler. -/
theorem namedBody_enters {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat} {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (prepared : Prepared base) (inputs : CallableAncestryPairedLookup.Inputs base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin state, SourceCoreCallableAncestryPairedPreparation.named? inputs origin = some state ∧
      output = SourceCoreCallablePairedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallablePairedFrames.named prepared.layout.frame origin) body := by
  obtain ⟨native, origin, nativeSelected, originSelected, emitted⟩ := namedBody_receipt prepared accepted
  have nativeSame := Option.some.inj (nativeSelected.symm.trans inputs.callableSelected)
  subst native
  unfold SourceCoreStageCodebook.Table.idAt? at originSelected
  cases found : inputs.callable.table.entries.find? (fun entry => decide (entry.origin = .named function.signature.key)) with
  | none => simp only [found, Option.map_none] at originSelected; cases originSelected
  | some entry =>
    have namedOrigin : entry.origin = .named function.signature.key := by simpa using List.find?_some found
    have identifier : entry.id = origin := by simpa only [found, Option.map_some, Option.some.injEq] using originSelected
    obtain ⟨state, generated⟩ := CallableAncestryPairedSeeds.named_total
      (CallableAncestryPairedSeeds.factory_authenticated compiled inputs) (List.mem_of_find?_eq_some found) namedOrigin
    exact ⟨origin, state, identifier ▸ generated, emitted⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedEmission
end
