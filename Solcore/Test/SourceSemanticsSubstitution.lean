import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.Graph

/-!
Focused public checks for rigid substitution through implementation matching,
semantic evidence, and solved-requirement ledgers.
-/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem
open SourceSemantics
open SourceSemantics.StructuralSubstitution

private def captureSource : TypeVarId := ⟨0⟩

private def captureProtected : TypeVarId := ⟨1⟩

private def captureSafeRange : TypeVarId := ⟨2⟩

private def captureInner : Substitution :=
  [(captureProtected, .word)]

private def capturingOuter : Substitution :=
  [(captureSource, .variable captureProtected)]

private def captureSafeOuter : Substitution :=
  [(captureSource, .variable captureSafeRange)]

private def captureType : Ty := .variable captureSource

private theorem captureInnerExact :
    ExactSubstitution captureInner [captureProtected] := by
  exact ExactSubstitution.singleton captureProtected .word

private theorem captureSafeOuterFresh :
    ∀ metavariable, metavariable ∈ [captureProtected] →
      metavariable ∉ captureSafeOuter.domain := by
  intro metavariable protectedMember
  simp only [List.mem_singleton] at protectedMember
  subst metavariable
  simp [captureSafeOuter, captureProtected, captureSource,
    TypeSystem.Substitution.domain]

private theorem captureSafeRangeAvoids :
    captureSafeOuter.RangeAvoidsVariablesOn [captureProtected]
      captureType := by
  intro sourceVariable occurs replacement found protectedVariable captured
  simp only [captureType, Ty.freeVariables, List.mem_singleton] at occurs
  subst sourceVariable
  simp [captureSafeOuter] at found
  subst replacement
  simp only [Ty.freeVariables, List.mem_singleton] at captured
  subst protectedVariable
  simp [captureSafeRange, captureProtected]

/-- The tempting weaker premise `protected ∉ outer.domain` is insufficient:
an outer replacement can introduce the inner variable and be captured by the
mapped inner substitution. -/
example :
    capturingOuter.apply (captureInner.apply captureType) ≠
      (FlexibleSubstitution.Substitution.mapRange
        capturingOuter captureInner).apply (capturingOuter.apply captureType) := by
  simp [capturingOuter, captureInner, captureType, captureSource,
    captureProtected, FlexibleSubstitution.Substitution.mapRange,
    TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?]
  intro impossible
  cases impossible

/-- The counterexample is rejected exactly by the relevance-restricted
no-capture premise. -/
example : ¬ capturingOuter.RangeAvoidsVariablesOn [captureProtected]
    captureType := by
  intro avoids
  have outside := avoids captureSource
    (by simp [captureType, captureSource, Ty.freeVariables])
    (.variable captureProtected)
    (by simp [capturingOuter, captureSource])
    captureProtected
    (by simp [Ty.freeVariables])
  exact outside (by simp)

/-- When the only relevant outer range avoids the protected inner variable,
the flexible composition theorem applies without requiring a ground range. -/
example :
    captureSafeOuter.apply (captureInner.apply captureType) =
      (FlexibleSubstitution.Substitution.mapRange
        captureSafeOuter captureInner).apply
          (captureSafeOuter.apply captureType) :=
  FlexibleSubstitution.Ty.applyFlexible_compose_of_rangeAvoidsVariablesOn
    captureSafeOuter captureInner captureInnerExact captureSafeOuterFresh
    captureSafeRangeAvoids

/-- The same local algebraic boundary covers the subject and arguments of a
trait predicate. -/
example :
    let predicate := ProgramSignatures.builtinIntPredicate captureType
    TypedTraitResolution.applySubstitution captureSafeOuter
        (TypedTraitResolution.applySubstitution captureInner predicate) =
      TypedTraitResolution.applySubstitution
        (FlexibleSubstitution.Substitution.mapRange
          captureSafeOuter captureInner)
        (TypedTraitResolution.applySubstitution captureSafeOuter predicate) := by
  dsimp only
  apply
    FlexibleSubstitution.TypedTraitResolution.applySubstitution_compose_of_rangeAvoidsVariablesOn
    captureSafeOuter captureInner captureInnerExact captureSafeOuterFresh
  constructor
  · exact captureSafeRangeAvoids
  · intro argument member
    simp [ProgramSignatures.builtinIntPredicate] at member

/-- An already matched implementation head remains matched after applying an
outer declaration-parameter substitution to its goal and premises. -/
example (outer : ParameterSubstitution) (rule : ProgramImplRule)
    (goal : ProgramPredicate) (premises : List ProgramPredicate)
    (matched : ImplHeadInstantiates rule goal premises) :
    ImplHeadInstantiates rule
      (ProgramPredicate.applyParameters outer goal)
      (premises.map (ProgramPredicate.applyParameters outer)) :=
  StructuralSubstitution.ImplHeadInstantiates.applyParameters outer matched

/-- Nested semantic evidence is closed by the same structural action. -/
example (outer : ParameterSubstitution)
    (assumptions : List ProgramPredicate) (rules : List ProgramImplRule)
    (goal : ProgramPredicate) (evidence : TraitEvidence)
    (valid : EvidenceValid assumptions rules goal evidence) :
    EvidenceValid
      (assumptions.map (ProgramPredicate.applyParameters outer)) rules
      (ProgramPredicate.applyParameters outer goal)
      (applyTraitEvidence outer evidence) :=
  StructuralSubstitution.EvidenceValid.applyParameters outer valid

/-- A well-formed solved-requirement ledger supplies the evidence premise for
transporting the complete source typing derivation. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (ledger : RequirementLedgerWellFormed context) :
    ContextSubstitutionValid substitution context :=
  ContextSubstitutionValid.ofRequirementLedger exact range ledger

/-- A scoped whole-body ledger likewise supplies the implementation-only
evidence premise without treating initializer templates as global assumptions. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context) (source : TypedSource)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (ledger : ScopedRequirementLedgerWellFormed context source) :
    ContextSubstitutionValid substitution context :=
  ContextSubstitutionValid.ofScopedRequirementLedger exact range ledger

/-- A finalized scoped ledger is already stated in the substitution target;
it therefore discharges the mapped implementation-row obligation directly. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context) (typedSource : TypedSource)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (schemesFresh : FlexibleSubstitution.LocalSchemesFreshFor source
      substitution)
    (ledger : ScopedRequirementLedgerWellFormed target typedSource) :
    FlexibleSubstitution.ContextSubstitutionValid substitution closedVariables
      source target :=
  FlexibleSubstitution.ContextSubstitutionValid.ofTargetScopedRequirementLedger
    closes schemesFresh ledger

/-- Rigid declaration instantiation transports both ordinary rows and
initializer-scoped template rows of the whole-body ledger. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context) (source : TypedSource)
    (ledger : ScopedRequirementLedgerWellFormed context source) :
    ScopedRequirementLedgerWellFormed (applyContext substitution context)
      (applyTypedSource substitution source) :=
  ScopedRequirementLedgerWellFormed.applyParameters substitution ledger

/-- The external substitution premise is needed only for implementation
evidence.  Assumption evidence is transported from its lexical validity by
`RequirementProves.applyParameters`. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (valid : ContextSubstitutionValid substitution context)
    (requirement : SolvedRequirement)
    (evidence : TypedTraitResolution.Evidence)
    (member : requirement ∈ context.solvedRequirements)
    (implementation : requirement.evidence = .implementation evidence) :
    SolvedRequirementValid (applyContext substitution context)
      (applySolvedRequirement substitution requirement) :=
  valid.implementationRequirements requirement evidence member implementation

/-- A ledger consisting only of assumption rows needs no evidence-transport
premise beyond exactness and range well-formedness.  The local proof supplies
the assumption membership used by rigid substitution. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (assumptionRows : ∀ requirement,
      requirement ∈ context.solvedRequirements →
        ∃ predicate, requirement.evidence = .assumption predicate)
    (id : RequirementId) (predicate : ProgramPredicate)
    (proves : RequirementProves context id predicate) :
    RequirementProves (applyContext substitution context) id
      (ProgramPredicate.applyParameters substitution predicate) := by
  apply RequirementProves.applyParameters
      ({ exact, range, implementationRequirements := ?_ } :
        ContextSubstitutionValid substitution context)
    proves
  intro requirement evidence member implementation
  rcases assumptionRows requirement member with ⟨assumption, assumptionEq⟩
  rw [assumptionEq] at implementation
  cases implementation

/-- One rigid declaration instantiation preserves the shared local-scheme
type/predicate witness and its ordered actual requirement identities. -/
example (substitution : ParameterSubstitution)
    (context : SourceSemantics.Context)
    (resolution : ReferenceResolution) (type : Ty)
    (requirements : List RequirementId)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : ReferenceUseValid context resolution type requirements) :
    ReferenceUseValid (applyContext substitution context)
      (applyReferenceResolution substitution resolution)
      (substitution.apply type) requirements :=
  ReferenceUseValid.applyParameters catalog contextValid valid

/-- Rigid substitution cannot change the occurrence graph of a generic body. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (closed : OccurrenceGraphClosed source) :
    OccurrenceGraphClosed (applyTypedSource substitution source) :=
  StructuralSubstitution.OccurrenceGraphClosed.applyParameters substitution
    closed

/-- Template-owner uniqueness is invariant under rigid declaration
instantiation. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (ownership : LocalSchemeTemplateOwnership source) :
    LocalSchemeTemplateOwnership (applyTypedSource substitution source) :=
  LocalSchemeTemplateOwnership.applyParameters substitution ownership

/-- Exact template-row ownership maps its predicate while retaining the
stable template identity. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (row : SolvedRequirement)
    (owned : LocalSchemeTemplateRowOwned source row) :
    LocalSchemeTemplateRowOwned (applyTypedSource substitution source)
      (applySolvedRequirement substitution row) :=
  LocalSchemeTemplateRowOwned.applyParameters substitution owned

/-- Exact template ownership, its primary attachment, and initializer scope
all survive rigid declaration instantiation together. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (row : SolvedRequirement)
    (rowScoped : LocalSchemeTemplateRowScoped source row) :
    LocalSchemeTemplateRowScoped (applyTypedSource substitution source)
      (applySolvedRequirement substitution row) :=
  LocalSchemeTemplateRowScoped.applyParameters substitution rowScoped

/-- Rigid instantiation preserves the initializer subtree in which a template
owner may be used. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (owner : LocalSchemeTemplateOwner) (occurrence : NodeId)
    (scope : owner.Scopes source occurrence) :
    (applyLocalSchemeTemplateOwner substitution owner).Scopes
      (applyTypedSource substitution source) occurrence :=
  LocalSchemeTemplateOwner.Scopes.applyParameters substitution scope

/-- The occurrence-aware primary-requirement inventory forgets to the legacy
flat identity inventory exactly. -/
example (source : TypedSource) :
    (primaryRequirementOccurrences source).map
        (fun occurrence => occurrence.requirement) =
      primaryRequirementIds source :=
  primaryRequirementOccurrenceIds_eq source

/-- Rigid substitution preserves exact primary requirement attachment sites. -/
example (substitution : ParameterSubstitution) (source : TypedSource) :
    primaryRequirementOccurrences (applyTypedSource substitution source) =
      primaryRequirementOccurrences source :=
  primaryRequirementOccurrences_applyTypedSource substitution source

/-- Flexible closure concretizes an assumption/template row while preserving
its stable identity. -/
example (substitution : Substitution) (id : RequirementId)
    (predicate : ProgramPredicate) :
    FlexibleSubstitution.applySolvedRequirement substitution {
        id
        predicate
        evidence := .assumption predicate
      } = {
        id
        predicate := TypedTraitResolution.applySubstitution substitution predicate
        evidence := .assumption
          (TypedTraitResolution.applySubstitution substitution predicate)
      } := by
  rfl

/-- A substitution cannot enter the quantified variables of an existing
lexical scheme or its parallel qualified-requirement scope when the complete
context is closed. -/
example (signatures : ProgramSignatures) (id : Resolved.LocalId)
    (requirementId : RequirementId)
    (metavariable : TypeVarId) :
    let scheme : Scheme := {
      quantified := [metavariable]
      body := .variable metavariable
    }
    let predicate := ProgramSignatures.builtinIntPredicate
      (.variable metavariable)
    let requirement : LocalSchemeRequirement := {
      templateRequirement := requirementId
      predicate
    }
    let context := (SourceSemantics.Context.ofSignatures signatures).withLocal
      id scheme [requirement]
    FlexibleSubstitution.closeContext [(metavariable, .word)] context =
      context := by
  simp [FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext,
    FlexibleSubstitution.applyLocals,
    FlexibleSubstitution.applyLocalSchemeRequirements,
    FlexibleSubstitution.forLocal, Resolved.LocalScope.lookup?,
    SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal,
    Scheme.apply,
    TypeSystem.Substitution.without, TypeSystem.Substitution.erase,
    LocalSchemeRequirement.applySubstitution,
    TypedTraitResolution.applySubstitution,
    ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.apply,
    TypeSystem.Substitution.lookup?]

/-- Flexible closing concretizes outer assumptions, assumption-backed
template rows, and every recursively retained implementation premise. -/
example (signatures : ProgramSignatures)
    (templateId implementationId : RequirementId)
    (metavariable : TypeVarId) :
    let templatePredicate := ProgramSignatures.builtinIntPredicate
      (.variable metavariable)
    let implementationPredicate := ProgramSignatures.builtinIntPredicate
      (.proxy (.variable metavariable))
    let premisePredicate := ProgramSignatures.builtinIntPredicate
      (.comptime (.variable metavariable))
    let implementationEvidence : TypedTraitResolution.Evidence :=
      .byImpl implementationPredicate (.builtin .intWord)
        [.byImpl premisePredicate (.builtin .intInteger) []]
    let context : SourceSemantics.Context := {
      SourceSemantics.Context.ofSignatures signatures with
      assumptions := [templatePredicate]
      solvedRequirements := [
        {
          id := templateId
          predicate := templatePredicate
          evidence := .assumption templatePredicate
        },
        {
          id := implementationId
          predicate := implementationPredicate
          evidence := .implementation implementationEvidence
        }
      ]
    }
    FlexibleSubstitution.closeContext [(metavariable, .word)] context = {
      SourceSemantics.Context.ofSignatures signatures with
      assumptions := [ProgramSignatures.builtinIntPredicate .word]
      solvedRequirements := [
        {
          id := templateId
          predicate := ProgramSignatures.builtinIntPredicate .word
          evidence := .assumption
            (ProgramSignatures.builtinIntPredicate .word)
        },
        {
          id := implementationId
          predicate := ProgramSignatures.builtinIntPredicate (.proxy .word)
          evidence := .implementation (.byImpl
            (ProgramSignatures.builtinIntPredicate (.proxy .word))
            (.builtin .intWord)
            [.byImpl
              (ProgramSignatures.builtinIntPredicate (.comptime .word))
              (.builtin .intInteger) []])
        }
      ]
    } := by
  simp [FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext,
    FlexibleSubstitution.applySolvedRequirement,
    FlexibleSubstitution.applyPredicateEvidence,
    FlexibleSubstitution.applyEvidence,
    FlexibleSubstitution.applyEvidences,
    FlexibleSubstitution.applyLocals,
    FlexibleSubstitution.applyLocalSchemeRequirements,
    SourceSemantics.Context.ofSignatures,
    TypedTraitResolution.applySubstitution,
    ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.apply,
    TypeSystem.Substitution.lookup?]

/-- Closing an initializer maps its outer and scheme-local assumptions in one
source-ordered context transformation. -/
example (substitution : Substitution) (context : SourceSemantics.Context)
    (binder : TypedBinder) :
    FlexibleSubstitution.closeContext substitution
        (localSchemeInitializerContext context binder) =
      (FlexibleSubstitution.closeContext substitution context).withAssumptions
        ((FlexibleSubstitution.closeContext substitution context).assumptions ++
          instantiateLocalSchemePredicates substitution binder) :=
  FlexibleSubstitution.closeContext_localSchemeInitializerContext
    substitution context binder

/-- A nested generalized initializer can close an outer metavariable while
retaining the inner initializer's lexical metavariable. -/
example (signatures : ProgramSignatures) (outer inner : TypeVarId) :
    FlexibleSubstitution.applyContext [(outer, .word)] [inner]
        ((SourceSemantics.Context.ofSignatures signatures).withTypeVariables
          [outer, inner]) =
      (SourceSemantics.Context.ofSignatures signatures).withTypeVariables
        [inner] := by
  rfl

/-- Type-scope transport closes a concrete outer metavariable while retaining
the nested generalized initializer's concrete inner metavariable. -/
example (signatures : ProgramSignatures) :
    let inner : TypeVarId := ⟨1⟩
    let target := (SourceSemantics.Context.ofSignatures signatures)
      |>.withTypeVariables [inner]
    TypeAdmissible target (.product .word (.variable inner)) := by
  dsimp
  let outer : TypeVarId := ⟨0⟩
  let inner : TypeVarId := ⟨1⟩
  let source := (SourceSemantics.Context.ofSignatures signatures)
    |>.withTypeVariables [outer, inner]
  let target := (SourceSemantics.Context.ofSignatures signatures)
    |>.withTypeVariables [inner]
  have sourceAdmissible :
      TypeAdmissible source
        (.product (.variable outer) (.variable inner)) := {
    binders :=
      (TypeParameterBindersWellFormed.ofSignatures signatures)
        |>.withTypeVariables [outer, inner]
    typeWellScoped := .product
      (.variable (by
        simp [admissibleTypeVariables, source, Context.withTypeVariables,
          Context.ofSignatures]))
      (.variable (by
        simp [admissibleTypeVariables, source, Context.withTypeVariables,
          Context.ofSignatures]))
  }
  have closes : FlexibleSubstitution.ContextCloses
      [(outer, .word)] [outer] source target := {
    variables_eq := rfl
    exact := ExactSubstitution.singleton outer .word
    retained_fresh := by
      intro metavariable member
      change metavariable ∈ [inner] at member
      change metavariable ∉ [outer]
      simp only [List.mem_singleton] at member ⊢
      subst metavariable
      decide
    range := by
      intro metavariable replacement member
      simp only [List.mem_singleton] at member
      cases member
      exact {
        binders :=
          (TypeParameterBindersWellFormed.ofSignatures signatures)
            |>.withTypeVariables [inner]
        typeWellScoped := .builtin .word
      }
    target_eq := rfl
  }
  simpa [outer, inner, source, target, TypeSystem.Substitution.apply,
    TypeSystem.Substitution.lookup?] using
      (FlexibleSubstitution.TypeAdmissible.applySubstitution closes
        sourceAdmissible)

/-- A ground substitution removes exactly its domain from the stable
free-variable order, including when the same survivor occurs in both sides. -/
example (context : SourceSemantics.Context) (substitution : Substitution)
    (range : SubstitutionRangeWellFormed context substitution)
    (left right : Ty) :
    (substitution.apply (Ty.product left right)).freeVariables =
      (Ty.product left right).freeVariables.filter fun metavariable =>
        !(substitution.domain.contains metavariable) :=
  FlexibleSubstitution.Substitution.freeVariables_apply range
    (Ty.product left right)

/-- Capture avoidance removes quantified lookup keys, retains all other
lookups, and preserves the duplicate-free domain invariant. -/
example (substitution : Substitution) (variables : List TypeVarId)
    (removed retained : TypeVarId) (removedMem : removed ∈ variables)
    (retainedAbsent : retained ∉ variables)
    (unique : substitution.domain.Nodup) :
    (substitution.without variables).lookup? removed = none ∧
      (substitution.without variables).lookup? retained =
        substitution.lookup? retained ∧
      (substitution.without variables).domain.Nodup := by
  exact ⟨TypeSystem.Substitution.lookup?_without_of_mem substitution removedMem,
    FlexibleSubstitution.Substitution.lookup?_without_of_not_mem substitution
      retainedAbsent,
    FlexibleSubstitution.Substitution.domain_without_nodup substitution variables
      unique⟩

/-- Closed type transport remains valid when residual inference is enabled;
`TypeWellFormed` itself still contributes no residual free variables. -/
example (signatures : ProgramSignatures) :
    let outer : TypeVarId := ⟨0⟩
    let target := (SourceSemantics.Context.ofSignatures signatures)
      |>.withResidualTypeVariables
    TypeWellFormed target
      (TypeSystem.Substitution.apply [(outer, .word)] .word) := by
  dsimp
  let outer : TypeVarId := ⟨0⟩
  let source := (SourceSemantics.Context.ofSignatures signatures)
    |>.withResidualTypeVariables
    |>.withTypeVariables [outer]
  let target := (SourceSemantics.Context.ofSignatures signatures)
    |>.withResidualTypeVariables
  have sourceWellFormed : TypeWellFormed source .word := {
    binders :=
      ((TypeParameterBindersWellFormed.ofSignatures signatures)
        |>.withResidualTypeVariables)
        |>.withTypeVariables [outer]
    typeWellScoped := .builtin .word
  }
  have closes : FlexibleSubstitution.ContextCloses
      [(outer, .word)] [outer] source target := {
    variables_eq := rfl
    exact := ExactSubstitution.singleton outer .word
    retained_fresh := by simp [target, Context.withResidualTypeVariables,
      Context.ofSignatures]
    range := by
      intro metavariable replacement member
      simp only [List.mem_singleton] at member
      cases member
      exact {
        binders :=
          (TypeParameterBindersWellFormed.ofSignatures signatures)
            |>.withResidualTypeVariables
        typeWellScoped := .builtin .word
      }
    target_eq := rfl
  }
  simpa [outer, source, target, TypeSystem.Substitution.apply] using
    (FlexibleSubstitution.TypeWellFormed.applySubstitution closes
      sourceWellFormed)

/-- Rank-1 scheme formation transports through an outer closure while the
scheme's own quantified variables remain protected. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context) (scheme : Scheme)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (wellFormed : SchemeWellFormed source scheme) :
    SchemeWellFormed target (scheme.apply substitution) :=
  FlexibleSubstitution.SchemeWellFormed.applySubstitution closes wellFormed

private def canonicalLocalQuantified : TypeVarId := ⟨7⟩

private def canonicalLocalOuterVariable : TypeVarId := ⟨3⟩

private def canonicalLocalOuterSubstitution : Substitution :=
  [(canonicalLocalOuterVariable, .word)]

private def canonicalGenericLocalBinder
    (owner : Resolved.DeclarationId) : TypedBinder := {
  id := { owner, binderIndex := 0 }
  name := "identity"
  scheme := {
    quantified := [canonicalLocalQuantified]
    body := .function (.variable canonicalLocalQuantified)
      (.variable canonicalLocalQuantified)
  }
}

private def canonicalGenericLocalSource
    (signatures : ProgramSignatures) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures signatures)
    |>.withResidualTypeVariables)
    |>.withTypeVariables [canonicalLocalOuterVariable]

private def canonicalGenericLocalTarget
    (signatures : ProgramSignatures) : SourceSemantics.Context :=
  (SourceSemantics.Context.ofSignatures signatures)
    |>.withResidualTypeVariables

/-- Canonical instantiation of a concrete generic local composes with a later
outer closure: the outer metavariable closes to `word`, while the generic
identity's freshly allocated occurrence variable remains shared by its
parameter and result. -/
theorem canonicalGenericLocalInstantiationAfterOuterClosure
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId) :
    LocalSchemeInstantiationValid (canonicalGenericLocalTarget signatures)
      ((canonicalGenericLocalBinder owner).applySubstitution
        canonicalLocalOuterSubstitution)
      (.function (.variable ⟨10⟩) (.variable ⟨10⟩)) [] := by
  have closes : FlexibleSubstitution.ContextCloses
      canonicalLocalOuterSubstitution [canonicalLocalOuterVariable]
      (canonicalGenericLocalSource signatures)
      (canonicalGenericLocalTarget signatures) := {
    variables_eq := rfl
    exact := ExactSubstitution.singleton canonicalLocalOuterVariable .word
    retained_fresh := by
      simp [canonicalGenericLocalTarget, Context.withResidualTypeVariables,
        Context.ofSignatures]
    range := by
      intro metavariable replacement member
      simp only [canonicalLocalOuterSubstitution, List.mem_singleton] at member
      cases member
      exact {
        binders :=
          (TypeParameterBindersWellFormed.ofSignatures signatures)
            |>.withResidualTypeVariables
        typeWellScoped := .builtin .word
      }
    target_eq := rfl
  }
  have contextValid : FlexibleSubstitution.ContextSubstitutionValid
      canonicalLocalOuterSubstitution [canonicalLocalOuterVariable]
      (canonicalGenericLocalSource signatures)
      (canonicalGenericLocalTarget signatures) := {
    closes
    localSchemesFresh := by
      intro entry member
      simp [canonicalGenericLocalSource, Context.withResidualTypeVariables,
        Context.withTypeVariables, Context.ofSignatures] at member
    implementationRequirements := by
      intro requirement evidence member evidenceEq
      simp [canonicalGenericLocalSource, Context.withResidualTypeVariables,
        Context.withTypeVariables, Context.ofSignatures] at member
  }
  have formation : LocalSchemeRequirementsWellFormed
      (canonicalGenericLocalSource signatures)
      (canonicalGenericLocalBinder owner) :=
    LocalSchemeRequirementsWellFormed.empty _ _ rfl
  have schemeWellFormed : SchemeWellFormed
      (canonicalGenericLocalSource signatures)
      (canonicalGenericLocalBinder owner).scheme := {
    binders :=
      ((TypeParameterBindersWellFormed.ofSignatures signatures)
        |>.withResidualTypeVariables)
        |>.withTypeVariables [canonicalLocalOuterVariable]
    quantified_nodup := by simp [canonicalGenericLocalBinder]
    body := by
      apply TypeWellScoped.function <;> apply TypeWellScoped.variable <;>
        simp [canonicalGenericLocalBinder, canonicalLocalQuantified,
          canonicalGenericLocalSource, admissibleTypeVariables,
          Context.withResidualTypeVariables, Context.withTypeVariables,
          Context.ofSignatures, TypeSystem.Ty.freeVariables]
  }
  have fresh : ∀ metavariable,
      metavariable ∈
          (canonicalGenericLocalBinder owner).scheme.quantified →
        metavariable ∉ canonicalLocalOuterSubstitution.domain := by
    intro metavariable quantified
    simp [canonicalGenericLocalBinder, canonicalLocalQuantified] at quantified
    subst metavariable
    simp [canonicalLocalOuterSubstitution, canonicalLocalOuterVariable,
      TypeSystem.Substitution.domain]
  have instantiatedBody :
      ((canonicalGenericLocalBinder owner).scheme
        |>.instantiateWithSubstitution 10).body =
        .function (.variable ⟨10⟩) (.variable ⟨10⟩) := by
    rfl
  have valid :=
    FlexibleSubstitution.LocalSchemeInstantiationValid.of_instantiateWithSubstitution_afterSubstitution
      (actualRequirements := []) contextValid fresh formation schemeWellFormed
      (by rfl) 10 (by simp)
      (by simp [localSchemeTemplateIds, canonicalGenericLocalBinder])
      (by
        simpa [instantiateLocalSchemePredicates, canonicalGenericLocalBinder]
          using (RequirementSequenceProves.nil :
            RequirementSequenceProves
              (canonicalGenericLocalTarget signatures) [] []))
  rw [instantiatedBody] at valid
  simpa [canonicalGenericLocalBinder, canonicalLocalOuterSubstitution,
    canonicalLocalOuterVariable, canonicalLocalQuantified,
    TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?] using valid

/-- Admissible predicates reuse type transport for the subject and every
source-ordered argument without changing trait selection. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context)
    (predicate : ProgramPredicate)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (admissible : PredicateAdmissible source predicate) :
    PredicateAdmissible target
      (TypedTraitResolution.applySubstitution substitution predicate) :=
  FlexibleSubstitution.PredicateAdmissible.applySubstitution closes admissible

/-- Exact outer closure removes the outer generalized variable from a nested
scheme body while preserving the inner variable as that scheme's sole
quantifier. -/
example (signatures : ProgramSignatures) :
    let outer : TypeVarId := ⟨0⟩
    let inner : TypeVarId := ⟨1⟩
    let source := (SourceSemantics.Context.ofSignatures signatures)
      |>.withTypeVariables [outer]
    let target := SourceSemantics.Context.ofSignatures signatures
    let scheme : Scheme := {
      quantified := [inner]
      body := .product (.variable outer) (.variable inner)
    }
    SchemeGeneralizes source scheme ∧
      SchemeGeneralizes target (scheme.apply [(outer, .word)]) := by
  let outer : TypeVarId := ⟨0⟩
  let inner : TypeVarId := ⟨1⟩
  let source := (SourceSemantics.Context.ofSignatures signatures)
    |>.withTypeVariables [outer]
  let target := SourceSemantics.Context.ofSignatures signatures
  let scheme : Scheme := {
    quantified := [inner]
    body := .product (.variable outer) (.variable inner)
  }
  have closes : FlexibleSubstitution.ContextCloses
      [(outer, .word)] [outer] source target := {
    variables_eq := rfl
    exact := ExactSubstitution.singleton outer .word
    retained_fresh := by
      simp [target, SourceSemantics.Context.ofSignatures]
    range := by
      intro metavariable replacement member
      simp only [List.mem_singleton] at member
      cases member
      exact {
        binders := TypeParameterBindersWellFormed.ofSignatures signatures
        typeWellScoped := .builtin .word
      }
    target_eq := rfl
  }
  have generalizes : SchemeGeneralizes source scheme := by
    simp only [SchemeGeneralizes, SchemeGeneralizesExcept, scheme, source,
      GeneralizationBlockedVariablesExcept, Context.withTypeVariables,
      Context.ofSignatures, Ty.freeVariables, outer, inner]
    change [inner] =
      ([outer, inner] : List TypeVarId).filter (fun metavariable =>
        !(metavariable ∈ [outer]))
    simp [outer, inner]
  refine ⟨by simpa [outer, inner, source, target, scheme] using generalizes, ?_⟩
  simpa [outer, inner, source, target, scheme] using
    (FlexibleSubstitution.SchemeGeneralizes.applySubstitution closes generalizes)

/-- Exact generalization makes each scheme variable fresh for the ambient
lexical scope, hence also for an exact outer-closing substitution. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context) (binder : TypedBinder)
    (exemptRequirements : List RequirementId)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements
      binder.scheme) :
    FlexibleSubstitution.ContextCloses substitution closedVariables
      (localSchemeInitializerContext source binder)
      (localSchemeInitializerContext target
        (binder.applySubstitution substitution)) := by
  apply FlexibleSubstitution.ContextCloses.localSchemeInitializer closes binder
  intro metavariable quantified domainMember
  apply FlexibleSubstitution.SchemeGeneralizesExcept.quantified_fresh
    generalizes metavariable quantified
  rw [closes.variables_eq]
  exact List.mem_append.mpr (Or.inl
    ((closes.exact.mem_domain_iff metavariable).mp domainMember))

/-- Qualified predicate formation and template identity transport together
using the same capture-avoiding substitution as the binder. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context) (binder : TypedBinder)
    (requirement : LocalSchemeRequirement)
    (exemptRequirements : List RequirementId)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements
      binder.scheme)
    (wellFormed : LocalSchemeRequirementWellFormed source binder requirement) :
    LocalSchemeRequirementWellFormed target
      (binder.applySubstitution substitution)
      (requirement.applySubstitution
        (substitution.without binder.scheme.quantified)) :=
  FlexibleSubstitution.LocalSchemeRequirementWellFormed.applySubstitution
    closes generalizes wellFormed

/-- The list judgment preserves both source order and uniqueness of stable
template requirement identities. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context) (binder : TypedBinder)
    (exemptRequirements : List RequirementId)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements
      binder.scheme)
    (wellFormed : LocalSchemeRequirementsWellFormed source binder) :
    LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution substitution) :=
  FlexibleSubstitution.LocalSchemeRequirementsWellFormed.applySubstitution
    closes generalizes wellFormed

/-- Common binder formation needs no generalization premise: capture avoidance
is already part of `TypedBinder.applySubstitution`. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context)
    (owner : Resolved.DeclarationId) (binder : TypedBinder)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (wellFormed : BinderWellFormed source owner binder) :
    BinderWellFormed target owner (binder.applySubstitution substitution) :=
  FlexibleSubstitution.BinderWellFormed.applySubstitution closes wellFormed

/-- Fresh inner binders extend a structural outer closure without being
captured by its exact substitution. -/
example (substitution : Substitution) (closedVariables variables : List TypeVarId)
    (source target : SourceSemantics.Context)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (fresh : ∀ metavariable, metavariable ∈ variables →
      metavariable ∉ substitution.domain) :
    FlexibleSubstitution.ContextCloses substitution closedVariables
      (source.withTypeVariables variables)
      (target.withTypeVariables variables) :=
  closes.withTypeVariables variables fresh

/-- Fresh local extension preserves the same outer context-closing relation
and installs the capture-avoiding image of the local scheme metadata. -/
example (substitution : Substitution) (closedVariables : List TypeVarId)
    (source target : SourceSemantics.Context)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      source target)
    (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement)
    (fresh : id ∉ source.localSchemeRequirements.map Prod.fst) :
    FlexibleSubstitution.ContextCloses substitution closedVariables
      (source.withLocal id scheme requirements)
      (target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified)))) :=
  closes.withLocal id scheme requirements fresh

/-- Flexible closing preserves globally unique, declaration-owned local
identities. -/
example (substitution : Substitution) (source : TypedSource)
    (ownership : LocalIdentityOwnership source) :
    LocalIdentityOwnership (source.applySubstitution substitution) :=
  FlexibleSubstitution.LocalIdentityOwnership.applySubstitution substitution
    ownership

/-- A qualified local template row is transformed with its owner's
capture-avoiding substitution, rather than the unrestricted outer map. -/
example (substitution : Substitution) (source : TypedSource)
    (row : SolvedRequirement)
    (owned : LocalSchemeTemplateRowOwned source row) :
    ∃ owner, ContainsLocalSchemeTemplate source owner ∧
      LocalSchemeTemplateRowOwned (source.applySubstitution substitution)
        (FlexibleSubstitution.applyLocalSchemeTemplateRow substitution owner
          row) :=
  FlexibleSubstitution.LocalSchemeTemplateRowOwned.applySubstitution
    substitution owned

/-- Owner-local substitution preserves both a template row's primary
attachment and its initializer scope. -/
example (substitution : Substitution) (source : TypedSource)
    (row : SolvedRequirement)
    (rowScoped : LocalSchemeTemplateRowScoped source row) :
    ∃ owner, ContainsLocalSchemeTemplate source owner ∧
      LocalSchemeTemplateRowScoped (source.applySubstitution substitution)
        (FlexibleSubstitution.applyLocalSchemeTemplateRow substitution owner
          row) :=
  FlexibleSubstitution.LocalSchemeTemplateRowScoped.applySubstitution
    substitution rowScoped

/-- Flexible source and context closure preserve the exact correspondence
between primary requirement attachments and ledger identities. -/
example (substitution : Substitution) (context : SourceSemantics.Context)
    (source : TypedSource)
    (ownership : RequirementOwnership context source) :
    RequirementOwnership
      (FlexibleSubstitution.closeContext substitution context)
      (source.applySubstitution substitution) :=
  FlexibleSubstitution.RequirementOwnership.applySubstitution substitution
    ownership

/-- The relational view of an exact primary attachment transports without
changing either stable identity. -/
example (substitution : ParameterSubstitution) (source : TypedSource)
    (occurrence : NodeId) (requirement : RequirementId)
    (occurs : PrimaryRequirementOccursAt source occurrence requirement) :
    PrimaryRequirementOccursAt (applyTypedSource substitution source)
      occurrence requirement := by
  simpa using occurs

/-- The declaration-level API closes the evidence side condition internally:
an exact, range-valid rigid substitution transports both input binders and the
complete generic body typing derivation. -/
example (signatures : ProgramSignatures)
    (parameters : List TypeParameterId)
    (assumptions : List ProgramPredicate)
    (parameterNames : List String) (parameterTypes : List Ty)
    (parameterComptime : List Bool) (returnTypes : List Ty)
    (returnComptime : Bool) (definition : BodyDefinition) (facts : BodyFacts)
    (substitution : ParameterSubstitution)
    (catalog : SignatureCatalogWellFormed signatures)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)) substitution)
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    ∃ lexicalContext,
      MonoBindersExtend definition.source.owner
        (applyContext substitution
          (declarationContext signatures definition.owner parameters assumptions
            definition.solvedRequirements))
        (definition.source.inputs.map (applyBinder substitution))
        (parameterTypes.map substitution.apply) lexicalContext ∧
      BodyHasType (applyTypedSource substitution definition.source)
        lexicalContext (substitution.apply definition.resultType)
        (applyBodyFacts substitution facts) :=
  BodyDefinitionHasType.instantiate substitution catalog exact range typing

end Solcore.Test.SourceSemanticsSubstitution
