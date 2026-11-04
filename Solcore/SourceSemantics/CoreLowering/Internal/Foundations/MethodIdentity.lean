import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection

/-!
# Identity of recursive methods

Identity of recursive method selections, dictionaries and origins, their prepared stage scopes, and the coherence of cached and leaf trait evidence.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
/-! The actual method cache row and authenticated codebook descriptor select
its staged body scope. The full method dictionary stays attached; no ordinary
function declaration or body execution is inferred from the compiler row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
open Frontend SourceInference SourceCoreStageContracts
open CallContractCertificates CallEntryCertificates
open CallableIndexedOwnedMethodPrincipal

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : Key}
    {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at record
  split at record <;> try contradiction
  rename_i selected selectedEq
  cases record
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [selectedEq]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  {method : ExecutableImplMethods.CheckedMethod}

/-- Real descriptor authentication fixes the complete sidecar. Independent
method authority supplies its Source body and chosen dictionary. -/
theorem selected_of_descriptor
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (principal : Principal compiled method)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named principal.named.signature.key)) :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan method.specialized.key = .ok sidecar ∧
      sidecar.caller = method.specialized ∧
      (RecursiveNamedPreparedStageScopes.registry actual).Closure principal.sourceFunction
        (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction) := by
  obtain ⟨entry, member, origin, _⟩ := descriptor_entry descriptor
  have authenticated := actual.entries_authenticated entry member
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named issued =>
    obtain ⟨receipt⟩ := named_of_accepted issued
    have same := RecursiveNamedPreparedStageScopes.sidecar_caller receipt.prepared principal.record
    have sameMethod : receipt.sidecar.caller = method.specialized := same.trans principal.cached.same
    have keyEq : principal.named.signature.key = method.specialized.key :=
      (exact_key principal.record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) principal.cached.same)
    have prepared : prepareSidecar compiled.indexed.base.plan method.specialized.key = .ok receipt.sidecar := by
      simpa only [keyEq] using receipt.prepared
    exact ⟨receipt.sidecar, prepared, sameMethod,
      .method principal.selected principal.source_frame.roots receipt.sidecar prepared sameMethod⟩

/-- The original stage analysis and declaration substitution remain those of
the actual selected method, with no lexical local instantiation. -/
theorem original_stages
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (principal : Principal compiled method)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named principal.named.signature.key)) :
    ∃ sidecar : Sidecar,
      (RecursiveNamedPreparedStageScopes.registry actual).Closure principal.sourceFunction
        (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction) ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).origin.declarationSubstitution = method.specialized.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).evidence = principal.dictionary ∧
      SourceStageAnalysis.analyzeFunction method.specialized.function = .ok method.specialized.stageAnalysis := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual principal descriptor
  exact ⟨sidecar, selected, by simp only [RecursiveStageRegistry.scope_declarationSubstitution, same],
    rfl, rfl, by simpa only [same] using sidecar.analyzed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
/-! Independent method selection retains an ordered dictionary assembled for
exactly the method assumptions. Empty method assumptions therefore determine
that dictionary; nonempty dictionaries are not equated from body identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- This follows from the real selected method's assembly, not from evidence
coverage (which may also hold for a larger dictionary). -/
theorem dictionary_empty {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance}
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary)
    (empty : body.context.assumptions = []) : dictionary = [] := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ instantiated assembled _ =>
    cases instantiated with
    | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
      have assumptions := congrArg Context.assumptions contextEq
      change body.context.assumptions = _ at assumptions
      have goalsEmpty := assumptions.symm.trans empty
      dsimp [declarationContext, Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration, Context.ofSignatures, Context.withResidualTypeVariables] at goalsEmpty
      rw [goalsEmpty] at assembled
      cases assembled
      rfl

/-- The actual catalog and reached primary requirement identify the method
body. Its genuine empty assumption list also identifies the full dictionary. -/
theorem same_empty {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance} {expectedDictionary actualDictionary : EvidenceEnvironment}
    (unique : ∀ first second, ContainsRequirement context primary first → ContainsRequirement context primary second → first = second)
    (expected : OperatorMethodSelected program context caller traitName methodName (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName (primary :: rest) actualBody actualDictionary)
    (empty : expectedBody.context.assumptions = []) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog unique actual expected
  refine ⟨same, ?_⟩
  exact (dictionary_empty actual (by simpa only [same] using empty)).trans (dictionary_empty expected empty).symm

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
/-! Actual dictionary assembly retains an ordered, pointwise valid evidence
spine. Catalog uniqueness for the reached assumptions identifies that entire
spine, including repeated goals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Uniqueness is required only for the selected body's actual assumptions. -/
def Coherent (rules : List ProgramImplRule) (goals : List ProgramPredicate) : Prop :=
  ∀ goal ∈ goals, ∀ left right,
    EvidenceValid [] rules goal left → EvidenceValid [] rules goal right → left = right

theorem Coherent.empty (rules : List ProgramImplRule) : Coherent rules [] := by
  intro goal member
  cases member

/-- Every ordered entry carries its own validity, even when keys repeat. -/
def OrderedValid (rules : List ProgramImplRule) (goals : List ProgramPredicate)
    (dictionary : EvidenceEnvironment) : Prop :=
  Forall₂ (fun goal entry => entry.1 = goal ∧ EvidenceValid [] rules goal entry.2)
    goals dictionary

private theorem valid_member {rules : List ProgramImplRule}
    {goals : List ProgramPredicate} {trees : List TraitEvidence}
    (valid : Forall₂ (EvidenceValid [] rules) goals trees) :
    ∀ tree ∈ trees, EvidenceValid [] rules tree.goal tree := by
  induction valid with
  | nil => simp
  | cons head _ induction =>
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.evidence_goal_eq ▸ head
    · exact induction tree member

theorem subtree_valid {rules : List ProgramImplRule} {root tree : TraitEvidence}
    (valid : EvidenceValid [] rules root.goal root)
    (subtree : EvidenceSubtree root tree) :
    EvidenceValid [] rules tree.goal tree := by
  induction subtree with
  | self => exact valid
  | premise member _ induction =>
    cases valid with
    | implementation _ _ _ premises =>
      exact induction (valid_member premises _ member)

theorem origin_valid {rules : List ProgramImplRule}
    {caller : EvidenceEnvironment} {roots : List TraitEvidence}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (callerValid : caller.Valid rules)
    (rootsValid : ∀ root ∈ roots, EvidenceValid [] rules root.goal root)
    (origin : EvidenceEntryOriginates caller roots goal tree) :
    EvidenceValid [] rules goal tree := by
  cases origin with
  | caller found => exact callerValid _ _ found
  | root member subtree same =>
    exact same ▸ subtree_valid (rootsValid _ member) subtree

theorem assembled_valid {rules : List ProgramImplRule}
    {caller dictionary : EvidenceEnvironment} {roots : List TraitEvidence}
    {goals : List ProgramPredicate}
    (callerValid : caller.Valid rules)
    (rootsValid : ∀ root ∈ roots, EvidenceValid [] rules root.goal root)
    (assembled : EvidenceEnvironment.AssembledFrom caller roots goals dictionary) :
    OrderedValid rules goals dictionary := by
  induction assembled with
  | nil => exact .nil
  | cons head _ induction =>
    exact .cons ⟨rfl, origin_valid callerValid rootsValid head⟩ induction

private theorem requirements_valid {context : Context} {caller dictionary : EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate}
    (produced : RequirementsProduceEnvironment context caller ids goals dictionary) :
    ∀ tree ∈ dictionary.map Prod.snd,
      EvidenceValid [] context.signatures.resolutionRules tree.goal tree := by
  induction produced with
  | nil => simp
  | cons head _ induction =>
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.evidence_goal_eq ▸ head.closed_valid
    · exact induction tree member

/-- Validity follows from the actual caller and selected roots, not merely
from first-match coverage of the returned dictionary. -/
theorem selected_valid {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance}
    (signatures : context.signatures = program.signatures)
    (callerValid : caller.Valid program.signatures.resolutionRules)
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary) :
    OrderedValid program.signatures.resolutionRules body.context.assumptions dictionary := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ requirements instantiated assembled _ =>
    have valid := assembled_valid (assembled := assembled) callerValid (by
      intro root member
      rcases List.mem_cons.mp member with rfl | member
      · cases selects with
        | intro produced _ =>
          have rootValid := produced.closed_valid
          rw [← produced.evidence_goal_eq, signatures] at rootValid
          exact rootValid
      · simpa only [signatures] using requirements_valid requirements root member)
    cases instantiated with
    | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
      rw [contextEq]
      exact valid

theorem ordered_functional {rules : List ProgramImplRule}
    {goals : List ProgramPredicate} {left right : EvidenceEnvironment}
    (coherent : Coherent rules goals)
    (first : OrderedValid rules goals left)
    (second : OrderedValid rules goals right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons goal entry goals entries head tail induction =>
    cases second with
    | @cons _ other _ others otherHead otherTail =>
      have same : entry = other := Prod.ext (head.1.trans otherHead.1.symm)
        (coherent goal (by simp) _ _ head.2 otherHead.2)
      cases same
      exact congrArg (List.cons entry)
        (induction (fun goal member => coherent goal (by simp [member])) otherTail)

/-- Source body identity and reached catalog coherence determine the whole
independently assembled dictionary in its original order. -/
theorem same_coherent {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance}
    {expectedDictionary actualDictionary : EvidenceEnvironment}
    (unique : ∀ first second, ContainsRequirement context primary first → ContainsRequirement context primary second → first = second)
    (signatures : context.signatures = program.signatures)
    (callerValid : caller.Valid program.signatures.resolutionRules)
    (expected : OperatorMethodSelected program context caller traitName methodName (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName (primary :: rest) actualBody actualDictionary)
    (coherent : Coherent program.signatures.resolutionRules expectedBody.context.assumptions) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog unique actual expected
  refine ⟨same, ordered_functional coherent ?_ (selected_valid signatures callerValid expected)⟩
  simpa only [same] using selected_valid signatures callerValid actual

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
/-! Ordered dictionary identity depends on the concrete caller and selected
evidence roots. Unrelated valid implementations are outside this condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

def Coherent (caller : EvidenceEnvironment) (roots : List TraitEvidence)
    (goals : List ProgramPredicate) : Prop :=
  ∀ goal ∈ goals, ∀ left right,
    EvidenceEntryOriginates caller roots goal left →
    EvidenceEntryOriginates caller roots goal right → left = right

theorem assembled_functional {caller left right : EvidenceEnvironment}
    {roots : List TraitEvidence} {goals : List ProgramPredicate}
    (coherent : Coherent caller roots goals)
    (first : EvidenceEnvironment.AssembledFrom caller roots goals left)
    (second : EvidenceEnvironment.AssembledFrom caller roots goals right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head _ induction =>
    cases second with
    | cons other tail =>
      have same := coherent _ (by simp) _ _ head other
      cases same
      exact congrArg (List.cons _) (induction
        (fun goal member => coherent goal (by simp [member])) tail)

theorem requirements_functional {context : Context} {caller : EvidenceEnvironment}
    {ids : List RequirementId} {leftGoals rightGoals : List ProgramPredicate}
    {left right : EvidenceEnvironment}
    (unique : RequirementIdsUnique context)
    (first : RequirementsProduceEnvironment context caller ids leftGoals left)
    (second : RequirementsProduceEnvironment context caller ids rightGoals right) :
    leftGoals = rightGoals ∧ left = right := by
  induction first generalizing rightGoals right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons head _ induction =>
    cases second with
    | cons other tail =>
      obtain ⟨rfl, rfl⟩ := CallableCoercionSelectionIdentity.requirement_functional
        (fun _ _ => unique.contains_unique) head other
      obtain ⟨rfl, rfl⟩ := induction tail
      exact ⟨rfl, rfl⟩

/-- The exact primary and method requirements produce these roots in order. -/
inductive RootsProduced (context : Context) (caller : EvidenceEnvironment) :
    List RequirementId → List TraitEvidence → Prop where
  | intro {primary : RequirementId} {rest : List RequirementId}
      {goal : ProgramPredicate} {tree : TraitEvidence}
      {goals : List ProgramPredicate} {dictionary : EvidenceEnvironment}
      (head : RequirementProducesEvidence context caller primary goal tree)
      (tail : RequirementsProduceEnvironment context caller rest goals dictionary) :
      RootsProduced context caller (primary :: rest) (tree :: dictionary.map Prod.snd)

theorem RootsProduced.functional {context : Context} {caller : EvidenceEnvironment}
    {ids : List RequirementId} {left right : List TraitEvidence}
    (unique : RequirementIdsUnique context)
    (first : RootsProduced context caller ids left)
    (second : RootsProduced context caller ids right) : left = right := by
  cases first with
  | intro head tail =>
    cases second with
    | intro other remaining =>
      obtain ⟨_, rfl⟩ := CallableCoercionSelectionIdentity.requirement_functional
        (fun _ _ => unique.contains_unique) head other
      obtain ⟨_, rfl⟩ := requirements_functional unique tail remaining
      rfl

theorem selected_assembly {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {ids : List RequirementId} {body : BodyInstance}
    (selected : OperatorMethodSelected program context caller traitName methodName ids body dictionary) :
    ∃ roots, RootsProduced context caller ids roots ∧
      EvidenceEnvironment.AssembledFrom caller roots body.context.assumptions dictionary := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ requirements instantiated assembled _ =>
    cases selects with
    | intro produced _ =>
      refine ⟨_, .intro produced requirements, ?_⟩
      cases instantiated with
      | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
        rw [contextEq]
        exact assembled

/-- Independent Source selection reuses exactly the actual caller and roots.
Only their finite reachable alternatives must agree. -/
theorem same_from_origins {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance}
    {expectedDictionary actualDictionary : EvidenceEnvironment} {roots : List TraitEvidence}
    (unique : RequirementIdsUnique context)
    (produced : RootsProduced context caller (primary :: rest) roots)
    (expected : OperatorMethodSelected program context caller traitName methodName
      (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName
      (primary :: rest) actualBody actualDictionary)
    (coherent : Coherent caller roots expectedBody.context.assumptions) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog
    (fun _ _ => unique.contains_unique) actual expected
  obtain ⟨expectedRoots, expectedProduced, expectedAssembly⟩ := selected_assembly expected
  obtain ⟨actualRoots, actualProduced, actualAssembly⟩ := selected_assembly actual
  have expectedEq := expectedProduced.functional unique produced
  have actualEq := actualProduced.functional unique produced
  subst expectedRoots actualRoots
  refine ⟨same, assembled_functional coherent ?_ expectedAssembly⟩
  simpa only [same] using actualAssembly

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence
/-! A trait whose matching catalog rules share one implementation identity and
have no premises has a unique complete evidence tree. These are factual catalog
conditions; method body behavior is not involved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence
open Frontend SourceInference
open RecursiveMethodDictionaryIdentity

structure Catalog (rules : List ProgramImplRule) (trait : ProgramTraitId)
    (implementation : ProgramImplId) : Prop where
  entries : ∀ rule ∈ rules, rule.head.trait = trait →
    rule.id = implementation ∧ rule.wherePredicates = []

theorem evidence_eq {rules : List ProgramImplRule} {trait : ProgramTraitId}
    {implementation : ProgramImplId} (catalog : Catalog rules trait implementation)
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (goalTrait : goal.trait = trait)
    (valid : EvidenceValid [] rules goal tree) :
    tree = .implementation goal implementation [] := by
  cases valid with
  | assumption member => cases member
  | implementation member identity instantiated premises =>
    cases instantiated with
    | intro substitution _ head premisesEq =>
      have traitEq : _ = trait :=
        (congrArg (fun predicate : ProgramPredicate => predicate.trait) head).trans goalTrait
      obtain ⟨same, empty⟩ := catalog.entries _ member traitEq
      rw [empty, List.map_nil] at premisesEq
      cases premisesEq
      cases premises
      cases identity.symm.trans same
      rfl

theorem coherent {rules : List ProgramImplRule} {trait : ProgramTraitId}
    {implementation : ProgramImplId} (catalog : Catalog rules trait implementation)
    {goals : List ProgramPredicate} (traits : ∀ goal ∈ goals, goal.trait = trait) :
    Coherent rules goals := by
  intro goal member left right first second
  exact (evidence_eq catalog (traits goal member) first).trans
    (evidence_eq catalog (traits goal member) second).symm

end Solcore.SourceSemantics.CoreLowering.LeafTraitEvidenceCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
/-! A finite compiler cache can authenticate evidence coherence for its actual
method rows. Original method owners exclude ordinary rows; full cached record
equality identifies the reached method without changing its substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
open Frontend SourceInference
open RecursiveMethodDictionaryIdentity

def Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Coherent compiled.sourceProgram.signatures.resolutionRules named.specialized.assumptions

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  rows : ∀ named ∈ compiled.indexed.base.functions, Row compiled named

theorem Catalog.of_instantiated {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {actual : ExecutableImplMethods.CheckedMethod}
    (cached : CallablePreparedMethodSelection.Cached compiled actual.specialized)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : TypeSystem.ParameterSubstitution}
    (instantiated : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      implementation method trait definition substitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual)) :
    Coherent compiled.sourceProgram.signatures.resolutionRules actual.specialized.assumptions := by
  rcases catalog.rows cached.named (List.mem_of_getElem? cached.selected) with excluded | coherent
  · cases instantiated with
    | intro _ _ _ _ definitionMember _ _ _ _ source _ _ =>
      have sourceOwner : actual.specialized.function.typedBody.owner = definition.body.source.owner := by
        have same := congrArg (fun source : TypedSource => source.owner) source
        exact same
      have namedOwner : cached.named.specialized.function.typedBody.owner =
          actual.specialized.function.typedBody.owner := by rw [cached.same]
      exact False.elim (excluded definition definitionMember (namedOwner.trans sourceOwner))
  · simpa only [cached.same] using coherent

theorem Catalog.of_principal {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : Catalog compiled) {actual : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled actual) :
    Coherent compiled.sourceProgram.signatures.resolutionRules actual.specialized.assumptions := by
  obtain ⟨_, _, _, _, _, instantiated⟩ := principal.source_instantiation
  exact catalog.of_instantiated principal.cached instantiated

private def rowsOfLeaf? (compiled : SourceCoreUnifiedCompilation.Compiled)
    {trait : ProgramTraitId} {implementation : ProgramImplId}
    (leaf : LeafTraitEvidenceCoherence.Catalog
      compiled.sourceProgram.signatures.resolutionRules trait implementation) :
    (rows : List SourceCoreGeneralFunctions.Function) →
      Option (PLift (∀ named ∈ rows, Row compiled named))
  | [] => some ⟨by intro named member; cases member⟩
  | named :: rest => do
    let head ← (if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
        (fun definition => decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
      some ⟨Or.inl (by
        intro definition member
        exact of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
      else if traits : named.specialized.assumptions.all (fun goal => decide (goal.trait = trait)) = true then
        some ⟨Or.inr (LeafTraitEvidenceCoherence.coherent leaf (by
          intro goal member
          exact of_decide_eq_true (List.all_eq_true.mp traits goal member)))⟩
      else none : Option (PLift (Row compiled named)))
    let tail ← rowsOfLeaf? compiled leaf rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head.down
      · exact tail.down row member⟩

/-- Only finite source owners and actual assumption trait tags are checked.
The proved leaf catalog supplies complete evidence-tree uniqueness. -/
def of_leaf? (compiled : SourceCoreUnifiedCompilation.Compiled)
    {trait : ProgramTraitId} {implementation : ProgramImplId}
    (leaf : LeafTraitEvidenceCoherence.Catalog
      compiled.sourceProgram.signatures.resolutionRules trait implementation) :
    Option (PLift (Catalog compiled)) := do
  let rows ← rowsOfLeaf? compiled leaf compiled.indexed.base.functions
  return ⟨⟨rows.down⟩⟩

end Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
end
