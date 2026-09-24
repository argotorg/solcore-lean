import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.TypeSystem.Properties

/-!
Static preservation properties for structural rigid-parameter substitution.

The definitions in `Substitution` describe the structural action on the
resolved source carrier.  This file records the corresponding action on proof
indices (contexts and control summaries) and proves that well-scoped types are
closed by an exact, well-formed declaration substitution.  The higher-level
lemmas below use these facts to transport source typing derivations.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.StructuralSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

theorem eq_of_mem_of_mapped_nodup
    {alpha beta : Type} {values : List alpha} {key : alpha → beta}
    {left right : alpha}
    (keysNodup : (values.map key).Nodup)
    (leftMem : left ∈ values) (rightMem : right ∈ values)
    (keysEq : key left = key right) :
    left = right := by
  induction values with
  | nil => simp at leftMem
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at keysNodup
      rcases keysNodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftTail
      · rcases rightMem with rfl | rightTail
        · rfl
        · exfalso
          apply headFresh
          rw [keysEq]
          exact List.mem_map.mpr ⟨right, rightTail, rfl⟩
      · rcases rightMem with rfl | rightTail
        · exfalso
          apply headFresh
          rw [← keysEq]
          exact List.mem_map.mpr ⟨left, leftTail, rfl⟩
        · exact induction tailNodup leftTail rightTail

/-- Substitute every type-bearing component of a local scope. -/
def applyLocals (substitution : ParameterSubstitution)
    (locals : Resolved.LocalScope Scheme) : Resolved.LocalScope Scheme :=
  locals.map fun entry => (entry.1, applyScheme substitution entry.2)

/-- Substitute every predicate retained by the proof-facing qualified-local
scope while preserving stable binder and template identities. -/
def applyLocalSchemeRequirements (substitution : ParameterSubstitution)
    (requirements :
      Resolved.LocalScope (List LocalSchemeRequirement)) :
    Resolved.LocalScope (List LocalSchemeRequirement) :=
  requirements.map fun entry =>
    (entry.1, entry.2.map (LocalSchemeRequirement.applyParameters substitution))

/-- The rigidly instantiated use-site context corresponding to a generic
declaration context.  Lexical and residual flexible-variable policy is
preserved unchanged. -/
def applyContext (substitution : ParameterSubstitution)
    (context : Context) : Context := {
  signatures := context.signatures
  currentDeclaration := context.currentDeclaration
  typeParameters := []
  typeVariables := context.typeVariables
  residualTypeVariables := context.residualTypeVariables
  locals := applyLocals substitution context.locals
  localSchemeRequirements :=
    applyLocalSchemeRequirements substitution context.localSchemeRequirements
  assumptions := context.assumptions.map
    (ProgramPredicate.applyParameters substitution)
  solvedRequirements := context.solvedRequirements.map
    (applySolvedRequirement substitution)
}

def applyControlSummary (substitution : ParameterSubstitution)
    (summary : ControlSummary) : ControlSummary := {
  fallthrough := summary.fallthrough.map substitution.apply
  mayReturn := summary.mayReturn
  mayBreak := summary.mayBreak
  mayContinue := summary.mayContinue
}

def applyControlContext (substitution : ParameterSubstitution)
    (control : ControlContext) : ControlContext := {
  returnType := substitution.apply control.returnType
  loopDepth := control.loopDepth
}

def applyStatementFacts (substitution : ParameterSubstitution)
    (facts : StatementFacts) : StatementFacts := {
  type := substitution.apply facts.type
  hasValue := facts.hasValue
  sawReturn := facts.sawReturn
  control := applyControlSummary substitution facts.control
}

def applyBodyFacts (substitution : ParameterSubstitution)
    (facts : BodyFacts) : BodyFacts := {
  type := substitution.apply facts.type
  sawReturn := facts.sawReturn
  control := applyControlSummary substitution facts.control
}

/-- Structural action on the proof-only description of requirement ownership
for an expression. -/
def applyExpressionRequirementPlan (substitution : ParameterSubstitution) :
    ExpressionRequirementPlan → ExpressionRequirementPlan
  | .ordinary owned => .ordinary owned
  | .directCall predicates =>
      .directCall (predicates.map (ProgramPredicate.applyParameters substitution))
  | .indirectCall coercions =>
      .indirectCall (coercions.map (applyCoercionStep substitution))

@[simp] theorem apply_builtin (substitution : ParameterSubstitution)
    (builtin : BuiltinType) :
    substitution.apply (.constructor (.builtin builtin)) =
      .constructor (.builtin builtin) := rfl

@[simp] theorem apply_word (substitution : ParameterSubstitution) :
    substitution.apply Ty.word = Ty.word := rfl

@[simp] theorem apply_integer (substitution : ParameterSubstitution) :
    substitution.apply Ty.integer = Ty.integer := rfl

@[simp] theorem apply_bool (substitution : ParameterSubstitution) :
    substitution.apply Ty.bool = Ty.bool := rfl

@[simp] theorem apply_unit (substitution : ParameterSubstitution) :
    substitution.apply Ty.unit = Ty.unit := rfl

@[simp] theorem apply_ite (substitution : ParameterSubstitution)
    (condition : Prop) [Decidable condition] (thenType elseType : Ty) :
    substitution.apply (if condition then thenType else elseType) =
      if condition then substitution.apply thenType
      else substitution.apply elseType := by
  split <;> rfl

@[simp] theorem apply_function (substitution : ParameterSubstitution)
    (parameter result : Ty) :
    substitution.apply (.function parameter result) =
      .function (substitution.apply parameter) (substitution.apply result) := rfl

@[simp] theorem apply_product (substitution : ParameterSubstitution)
    (left right : Ty) :
    substitution.apply (.product left right) =
      .product (substitution.apply left) (substitution.apply right) := rfl

@[simp] theorem apply_mapping (substitution : ParameterSubstitution)
    (key value : Ty) :
    substitution.apply (.mapping key value) =
      .mapping (substitution.apply key) (substitution.apply value) := rfl

@[simp] theorem apply_proxy (substitution : ParameterSubstitution)
    (inner : Ty) :
    substitution.apply (.proxy inner) = .proxy (substitution.apply inner) := rfl

@[simp] theorem apply_comptime (substitution : ParameterSubstitution)
    (inner : Ty) :
    substitution.apply (.comptime inner) =
      .comptime (substitution.apply inner) := rfl

theorem apply_productMany (substitution : ParameterSubstitution)
    (types : List Ty) :
    substitution.apply (Ty.productMany types) =
      Ty.productMany (types.map substitution.apply) := by
  induction types with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [Ty.productMany, apply_product, List.map_cons]
          rw [induction]
          rfl

theorem apply_applyMany (substitution : ParameterSubstitution)
    (head : Ty) (arguments : List Ty) :
    substitution.apply (Ty.applyMany head arguments) =
      Ty.applyMany (substitution.apply head)
        (arguments.map substitution.apply) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments induction =>
      simpa [Ty.applyMany, TypeSystem.ParameterSubstitution.apply] using
        induction (.application head argument)

theorem apply_nominal (substitution : ParameterSubstitution)
    (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    substitution.apply (Ty.nominal declaration arguments) =
      Ty.nominal declaration (arguments.map substitution.apply) := by
  unfold Ty.nominal
  rw [apply_applyMany]
  rfl

theorem applyFlexible_applyMany (substitution : TypeSystem.Substitution)
    (head : Ty) (arguments : List Ty) :
    substitution.apply (Ty.applyMany head arguments) =
      Ty.applyMany (substitution.apply head)
        (arguments.map substitution.apply) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments induction =>
      simpa [Ty.applyMany, TypeSystem.Substitution.apply] using
        induction (.application head argument)

theorem applyFlexible_nominal (substitution : TypeSystem.Substitution)
    (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    substitution.apply (Ty.nominal declaration arguments) =
      Ty.nominal declaration (arguments.map substitution.apply) := by
  unfold Ty.nominal
  rw [applyFlexible_applyMany]
  rfl

@[simp] theorem patternInstructionBinderIds_applyMatchPatternInstructions
    (substitution : ParameterSubstitution)
    (instructions : List MatchPatternInstruction) :
    patternInstructionBinderIds
        (instructions.map (applyMatchPatternInstruction substitution)) =
      patternInstructionBinderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest induction =>
      have tail := induction
      simp only [patternInstructionBinderIds] at tail
      cases instruction <;>
        simp [patternInstructionBinderIds, applyMatchPatternInstruction,
          applyBinder, tail]

@[simp] theorem patternBinderIds_applyTypedMatchPattern
    (substitution : ParameterSubstitution) (pattern : TypedMatchPattern) :
    patternBinderIds (applyTypedMatchPattern substitution pattern) =
      patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
      cases resolution <;>
        simp [patternBinderIds, applyTypedMatchPattern,
          applyMatchPatternResolution, applyBinder]

@[simp] theorem forItemDefinedLocalIds_applyForItemForm
    (substitution : ParameterSubstitution) (item : ForItemForm) :
    forItemDefinedLocalIds (applyForItemForm substitution item) =
      forItemDefinedLocalIds item := by
  cases item <;> rfl

@[simp] theorem expressionDefinedLocalIds_applyExpressionForm
    (substitution : ParameterSubstitution) (form : ExpressionForm) :
    expressionDefinedLocalIds (applyExpressionForm substitution form) =
      expressionDefinedLocalIds form := by
  cases form <;>
    simp [expressionDefinedLocalIds, applyExpressionForm, applyBinder,
      List.map_map, Function.comp_def]

@[simp] theorem statementDefinedLocalIds_applyStatementForm
    (substitution : ParameterSubstitution) (form : StatementForm) :
    statementDefinedLocalIds (applyStatementForm substitution form) =
      statementDefinedLocalIds form := by
  cases form <;>
    simp [statementDefinedLocalIds, applyStatementForm, applyMatchResolution,
      applyTypedMatchCase, applyBinder, List.flatMap_map]

@[simp] theorem nodeDefinedLocalIds_applyNode
    (substitution : ParameterSubstitution) (node : Node) :
    (match applyNode substitution node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) =
    (match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) := by
  cases node <;>
    simp [applyNode, applyExpressionNode, applyStatementNode]

@[simp] theorem flatMap_definedLocalIds_applyNodes
    (substitution : ParameterSubstitution) (nodes : List Node) :
    (nodes.map (applyNode substitution)).flatMap (fun node =>
      match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) =
    nodes.flatMap (fun node =>
      match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction =>
      simp [induction]

@[simp] theorem definedLocalIds_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    definedLocalIds (applyTypedSource substitution source) =
      definedLocalIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      change
        (inputs.map (applyBinder substitution) |>.map fun binder => binder.id) ++
            (nodes.map (applyNode substitution) |>.flatMap fun node =>
              match node with
              | .expression expression =>
                  expressionDefinedLocalIds expression.form
              | .statement statement =>
                  statementDefinedLocalIds statement.form) =
          (inputs.map fun binder => binder.id) ++
            (nodes.flatMap fun node =>
              match node with
              | .expression expression =>
                  expressionDefinedLocalIds expression.form
              | .statement statement =>
                  statementDefinedLocalIds statement.form)
      rw [StructuralSubstitution.flatMap_definedLocalIds_applyNodes]
      simp [applyBinder, List.map_map, Function.comp_def]

theorem LocalIdentityOwnership.applyParameters
    (substitution : ParameterSubstitution) {source : TypedSource}
    (ownership : LocalIdentityOwnership source) :
    LocalIdentityOwnership (applyTypedSource substitution source) := by
  constructor
  · simpa using ownership.unique
  · intro id member
    simpa [applyTypedSource] using ownership.owned id (by simpa using member)

/-- Rigid substitution acts on the retained type and predicate data of an
initialized let without changing its initializer occurrence. -/
def applyInitializedLetBinding (substitution : ParameterSubstitution)
    (binding : InitializedLetBinding) : InitializedLetBinding := {
  binder := applyBinder substitution binding.binder
  initializer := binding.initializer
}

/-- Rigid substitution acts pointwise on one exact local-template owner. -/
def applyLocalSchemeTemplateOwner (substitution : ParameterSubstitution)
    (owner : LocalSchemeTemplateOwner) : LocalSchemeTemplateOwner := {
  binder := applyBinder substitution owner.binder
  initializer := owner.initializer
  requirement := owner.requirement.applyParameters substitution
}

@[simp] theorem forItemInitializedLetBindings_applyForItemForm
    (substitution : ParameterSubstitution) (item : ForItemForm) :
    forItemInitializedLetBindings (applyForItemForm substitution item) =
      (forItemInitializedLetBindings item).map
        (applyInitializedLetBinding substitution) := by
  cases item with
  | letDecl binder initializer => cases initializer <;> rfl
  | expression expression => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl

@[simp] theorem statementInitializedLetBindings_applyStatementForm
    (substitution : ParameterSubstitution) (form : StatementForm) :
    statementInitializedLetBindings (applyStatementForm substitution form) =
      (statementInitializedLetBindings form).map
        (applyInitializedLetBinding substitution) := by
  cases form with
  | letDecl binder initializer => cases initializer <;> rfl
  | returnStmt value => rfl
  | expression expression trailingSemicolon => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl
  | ifThen condition thenBody elseBody => rfl
  | block body => rfl
  | matchWith resolution => rfl
  | forLoop initializer condition post body =>
      simp [statementInitializedLetBindings, applyStatementForm,
        List.flatMap_map, List.map_flatMap]
  | whileLoop condition body => rfl
  | breakStmt => rfl
  | continueStmt => rfl

@[simp] theorem nodeInitializedLetBindings_applyNode
    (substitution : ParameterSubstitution) (node : Node) :
    (match applyNode substitution node with
      | .expression _ => []
      | .statement statement =>
          statementInitializedLetBindings statement.form) =
    (match node with
      | .expression _ => []
      | .statement statement =>
          statementInitializedLetBindings statement.form).map
        (applyInitializedLetBinding substitution) := by
  cases node <;> simp [applyNode, applyStatementNode]

@[simp] theorem initializedLetBindings_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    initializedLetBindings (applyTypedSource substitution source) =
      (initializedLetBindings source).map
        (applyInitializedLetBinding substitution) := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [initializedLetBindings, applyTypedSource, List.flatMap_map,
        List.map_flatMap]
      induction nodes with
      | nil => rfl
      | cons node nodes induction =>
          simp only [List.flatMap_cons]
          calc
            _ = (match node with
                  | .expression _ => []
                  | .statement statement =>
                      statementInitializedLetBindings statement.form).map
                    (applyInitializedLetBinding substitution) ++
                List.flatMap
                  (fun node =>
                    match applyNode substitution node with
                    | .expression _ => []
                    | .statement statement =>
                        statementInitializedLetBindings statement.form)
                  nodes := congrArg
                    (fun head => head ++ List.flatMap
                      (fun node =>
                        match applyNode substitution node with
                        | .expression _ => []
                        | .statement statement =>
                            statementInitializedLetBindings statement.form)
                      nodes)
                    (nodeInitializedLetBindings_applyNode substitution node)
            _ = _ := congrArg
              (fun tail =>
                (match node with
                  | .expression _ => []
                  | .statement statement =>
                      statementInitializedLetBindings statement.form).map
                    (applyInitializedLetBinding substitution) ++ tail)
              induction

@[simp] theorem templateOwners_applyInitializedLetBinding
    (substitution : ParameterSubstitution) (binding : InitializedLetBinding) :
    InitializedLetBinding.templateOwners
        (applyInitializedLetBinding substitution binding) =
      binding.templateOwners.map
        (applyLocalSchemeTemplateOwner substitution) := by
  simp [InitializedLetBinding.templateOwners, applyInitializedLetBinding,
    applyLocalSchemeTemplateOwner, applyBinder, List.map_map,
    Function.comp_def]

@[simp] theorem localSchemeTemplateOwners_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    localSchemeTemplateOwners (applyTypedSource substitution source) =
      (localSchemeTemplateOwners source).map
        (applyLocalSchemeTemplateOwner substitution) := by
  simp [localSchemeTemplateOwners, List.flatMap_map, List.map_flatMap]

@[simp] theorem applyLocalSchemeTemplateOwner_templateRequirement
    (substitution : ParameterSubstitution) (owner : LocalSchemeTemplateOwner) :
    (applyLocalSchemeTemplateOwner substitution owner).requirement.templateRequirement =
      owner.requirement.templateRequirement := by
  rfl

@[simp] theorem sourceLocalSchemeTemplateIds_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    sourceLocalSchemeTemplateIds (applyTypedSource substitution source) =
      sourceLocalSchemeTemplateIds source := by
  simp [sourceLocalSchemeTemplateIds, List.map_map, Function.comp_def]

theorem ContainsLocalSchemeTemplate.applyParameters
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    (substitution : ParameterSubstitution)
    (contains : ContainsLocalSchemeTemplate source owner) :
    ContainsLocalSchemeTemplate (applyTypedSource substitution source)
      (applyLocalSchemeTemplateOwner substitution owner) := by
  unfold ContainsLocalSchemeTemplate at contains ⊢
  rw [localSchemeTemplateOwners_applyTypedSource]
  exact List.mem_map.mpr ⟨owner, contains, rfl⟩

theorem LocalSchemeTemplateOwnership.applyParameters
    (substitution : ParameterSubstitution) {source : TypedSource}
    (ownership : LocalSchemeTemplateOwnership source) :
    LocalSchemeTemplateOwnership (applyTypedSource substitution source) := by
  constructor
  simpa using ownership.ids_unique

theorem InReflexiveSubtree.applyParameters
    {source : TypedSource} {root occurrence : NodeId}
    (substitution : ParameterSubstitution)
    (scope : InReflexiveSubtree source root occurrence) :
    InReflexiveSubtree (applyTypedSource substitution source) root occurrence := by
  rcases scope with rootEq | descends
  · exact Or.inl rootEq
  · exact Or.inr
      (StructuralSubstitution.descends_applyParameters substitution descends)

theorem InInitializedLetSubtree.applyParameters
    {source : TypedSource} {binding : InitializedLetBinding}
    {occurrence : NodeId} (substitution : ParameterSubstitution)
    (scope : InInitializedLetSubtree source binding occurrence) :
    InInitializedLetSubtree (applyTypedSource substitution source)
      (applyInitializedLetBinding substitution binding) occurrence := by
  exact ⟨by
    rw [initializedLetBindings_applyTypedSource]
    exact List.mem_map.mpr ⟨binding, scope.1, rfl⟩,
    StructuralSubstitution.InReflexiveSubtree.applyParameters substitution
      scope.2⟩

theorem LocalSchemeTemplateOwner.Scopes.applyParameters
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    {occurrence : NodeId} (substitution : ParameterSubstitution)
    (scope : owner.Scopes source occurrence) :
    (applyLocalSchemeTemplateOwner substitution owner).Scopes
      (applyTypedSource substitution source) occurrence := by
  exact ⟨StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters
      substitution scope.1,
    StructuralSubstitution.InReflexiveSubtree.applyParameters substitution
      scope.2⟩

theorem LocalSchemeTemplateRowOwned.applyParameters
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : ParameterSubstitution)
    (owned : LocalSchemeTemplateRowOwned source row) :
    LocalSchemeTemplateRowOwned (applyTypedSource substitution source)
      (applySolvedRequirement substitution row) := by
  cases owned with
  | intro owner contains idEq predicateEq evidenceEq =>
      refine .intro (applyLocalSchemeTemplateOwner substitution owner)
        (StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters
          substitution contains) ?_ ?_ ?_
      · simpa [applySolvedRequirement] using idEq
      · simpa [applySolvedRequirement, applyLocalSchemeTemplateOwner,
          LocalSchemeRequirement.applyParameters] using congrArg
            (ProgramPredicate.applyParameters substitution) predicateEq
      · simpa [applySolvedRequirement, applyLocalSchemeTemplateOwner,
          LocalSchemeRequirement.applyParameters, applyPredicateEvidence] using
            congrArg (applyPredicateEvidence substitution) evidenceEq

@[simp] theorem forItemPrimaryRequirementIds_applyForItemForm
    (substitution : ParameterSubstitution) (item : ForItemForm) :
    forItemPrimaryRequirementIds (applyForItemForm substitution item) =
      forItemPrimaryRequirementIds item := by
  cases item <;>
    simp [forItemPrimaryRequirementIds, applyForItemForm,
      applyAssignmentResolution]

@[simp] theorem statementPrimaryRequirementIds_applyStatementForm
    (substitution : ParameterSubstitution) (form : StatementForm) :
    statementPrimaryRequirementIds (applyStatementForm substitution form) =
      statementPrimaryRequirementIds form := by
  cases form <;>
    simp [statementPrimaryRequirementIds, applyStatementForm,
      applyAssignmentResolution, applyMatchResolution, applyTypedMatchCase,
      applyTypedMatchPattern, List.flatMap_map]

@[simp] theorem nodePrimaryRequirementIds_applyNode
    (substitution : ParameterSubstitution) (node : Node) :
    (match applyNode substitution node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) =
    (match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) := by
  cases node <;>
    simp [applyNode, applyExpressionNode, applyStatementNode]

@[simp] theorem flatMap_primaryRequirementIds_applyNodes
    (substitution : ParameterSubstitution) (nodes : List Node) :
    (nodes.map (applyNode substitution)).flatMap (fun node =>
      match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) =
    nodes.flatMap (fun node =>
      match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction =>
      simp [induction]

@[simp] theorem primaryRequirementIds_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    primaryRequirementIds (applyTypedSource substitution source) =
      primaryRequirementIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      change
        (nodes.map (applyNode substitution) |>.flatMap fun node =>
          match node with
          | .expression expression => expression.requirements
          | .statement statement =>
              statementPrimaryRequirementIds statement.form) =
        (nodes.flatMap fun node =>
          match node with
          | .expression expression => expression.requirements
          | .statement statement =>
              statementPrimaryRequirementIds statement.form)
      exact StructuralSubstitution.flatMap_primaryRequirementIds_applyNodes
        substitution nodes

@[simp] theorem expressionPrimaryRequirementOccurrences_applyExpressionNode
    (substitution : ParameterSubstitution) (expression : ExpressionNode) :
    expressionPrimaryRequirementOccurrences
        (applyExpressionNode substitution expression) =
      expressionPrimaryRequirementOccurrences expression := by
  simp [expressionPrimaryRequirementOccurrences, applyExpressionNode]

@[simp] theorem statementPrimaryRequirementOccurrences_applyStatementNode
    (substitution : ParameterSubstitution) (statement : StatementNode) :
    statementPrimaryRequirementOccurrences
        (applyStatementNode substitution statement) =
      statementPrimaryRequirementOccurrences statement := by
  simp [statementPrimaryRequirementOccurrences, applyStatementNode]

@[simp] theorem nodePrimaryRequirementOccurrences_applyNode
    (substitution : ParameterSubstitution) (node : Node) :
    nodePrimaryRequirementOccurrences (applyNode substitution node) =
      nodePrimaryRequirementOccurrences node := by
  cases node <;>
    simp [nodePrimaryRequirementOccurrences, applyNode]

@[simp] theorem flatMap_primaryRequirementOccurrences_applyNodes
    (substitution : ParameterSubstitution) (nodes : List Node) :
    (nodes.map (applyNode substitution)).flatMap
        nodePrimaryRequirementOccurrences =
      nodes.flatMap nodePrimaryRequirementOccurrences := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction => simp [induction]

/-- Rigid type substitution preserves both stable requirement identities and
their exact primary owning occurrences. -/
@[simp] theorem primaryRequirementOccurrences_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource) :
    primaryRequirementOccurrences (applyTypedSource substitution source) =
      primaryRequirementOccurrences source := by
  cases source with
  | mk owner inputs roots nodes =>
      exact flatMap_primaryRequirementOccurrences_applyNodes substitution nodes

@[simp] theorem primaryRequirementOccursAt_applyTypedSource
    (substitution : ParameterSubstitution) (source : TypedSource)
    (occurrence : NodeId) (requirement : RequirementId) :
    PrimaryRequirementOccursAt (applyTypedSource substitution source)
        occurrence requirement ↔
      PrimaryRequirementOccursAt source occurrence requirement := by
  simp [PrimaryRequirementOccursAt]

theorem LocalSchemeTemplateRowScoped.applyParameters
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : ParameterSubstitution)
    (rowScoped : LocalSchemeTemplateRowScoped source row) :
    LocalSchemeTemplateRowScoped (applyTypedSource substitution source)
      (applySolvedRequirement substitution row) := by
  cases rowScoped with
  | intro owner contains idEq predicateEq evidenceEq occurrence occurs scope =>
      refine .intro (applyLocalSchemeTemplateOwner substitution owner)
        (StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters
          substitution contains) ?_ ?_ ?_ occurrence ?_ ?_
      · simpa [applySolvedRequirement] using idEq
      · simpa [applySolvedRequirement, applyLocalSchemeTemplateOwner,
          LocalSchemeRequirement.applyParameters] using congrArg
            (ProgramPredicate.applyParameters substitution) predicateEq
      · simpa [applySolvedRequirement, applyLocalSchemeTemplateOwner,
          LocalSchemeRequirement.applyParameters, applyPredicateEvidence] using
            congrArg (applyPredicateEvidence substitution) evidenceEq
      · simpa [applySolvedRequirement] using
          (primaryRequirementOccursAt_applyTypedSource substitution source
            occurrence row.id).mpr occurs
      · exact LocalSchemeTemplateOwner.Scopes.applyParameters substitution
          scope

theorem RequirementOwnership.applyParameters
    (substitution : ParameterSubstitution) {context : Context}
    {source : TypedSource}
    (ownership : RequirementOwnership context source) :
    RequirementOwnership (applyContext substitution context)
      (applyTypedSource substitution source) := by
  constructor
  · simpa using ownership.primary_unique
  · simpa [applyContext, applySolvedRequirement, List.map_map,
      Function.comp_def] using ownership.ledger_exact

namespace ParameterSubstitution

def mapRange (outer inner : TypeSystem.ParameterSubstitution) :
    TypeSystem.ParameterSubstitution :=
  inner.map fun entry => (entry.1, outer.apply entry.2)

theorem lookup?_eq_none_of_not_mem_domain
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId}
    (absent : parameter ∉ SourceSemantics.ParameterSubstitution.domain
      substitution) :
    substitution.lookup? parameter = none := by
  induction substitution with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      simp only [SourceSemantics.ParameterSubstitution.domain,
        List.map_cons, List.mem_cons, not_or] at absent
      have different : candidate ≠ parameter := fun equal =>
        absent.1 equal.symm
      simp [TypeSystem.ParameterSubstitution.lookup?, different,
        induction absent.2]

theorem mem_of_lookup?_eq_some
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {replacement : Ty}
    (found : substitution.lookup? parameter = some replacement) :
    (parameter, replacement) ∈ substitution := by
  induction substitution with
  | nil => simp [TypeSystem.ParameterSubstitution.lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      by_cases same : candidate = parameter
      · subst candidate
        simp [TypeSystem.ParameterSubstitution.lookup?] at found
        cases found
        simp
      · have tailFound :
            TypeSystem.ParameterSubstitution.lookup? rest parameter =
              some replacement := by
          simpa [TypeSystem.ParameterSubstitution.lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

/-- Replacing rigid parameters by closed types preserves the exact ordered
list of flexible variables. -/
theorem freeVariables_apply
    (substitution : TypeSystem.ParameterSubstitution)
    (rangeClosed : ∀ parameter replacement,
      (parameter, replacement) ∈ substitution →
        replacement.freeVariables = [])
    (type : Ty) :
    (substitution.apply type).freeVariables = type.freeVariables := by
  induction type with
  | @«variable» metavariable => rfl
  | parameter parameter =>
      cases lookup : substitution.lookup? parameter with
      | none => simp [TypeSystem.ParameterSubstitution.apply, lookup]
      | some replacement =>
          have member := mem_of_lookup?_eq_some lookup
          simp only [TypeSystem.ParameterSubstitution.apply, lookup,
            Option.getD_some]
          exact rangeClosed parameter replacement member
  | constructor => rfl
  | application left right leftInduction rightInduction =>
      simp only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
      rw [leftInduction, rightInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
      rw [domainInduction, codomainInduction]
  | product left right leftInduction rightInduction =>
      simp only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
      rw [leftInduction, rightInduction]
  | mapping key value keyInduction valueInduction =>
      simp only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
      rw [keyInduction, valueInduction]
  | proxy inner induction =>
      simpa only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
        using induction
  | comptime inner induction =>
      simpa only [TypeSystem.ParameterSubstitution.apply, Ty.freeVariables]
        using induction
  | error => rfl

theorem lookup?_eq_some_of_mem_of_domain_nodup
    {substitution : TypeSystem.ParameterSubstitution}
    {parameter : TypeParameterId} {replacement : Ty}
    (unique :
      (SourceSemantics.ParameterSubstitution.domain substitution).Nodup)
    (member : (parameter, replacement) ∈ substitution) :
    substitution.lookup? parameter = some replacement := by
  induction substitution with
  | nil => simp at member
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      simp only [SourceSemantics.ParameterSubstitution.domain,
        List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨candidateAbsent, restUnique⟩
      simp only [List.mem_cons] at member
      rcases member with member | member
      · cases member
        simp [TypeSystem.ParameterSubstitution.lookup?]
      · have different : candidate ≠ parameter := by
          intro equal
          apply candidateAbsent
          rw [equal]
          exact List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
        simp [TypeSystem.ParameterSubstitution.lookup?, different,
          induction restUnique member]

theorem exists_lookup?_eq_some
    {substitution : TypeSystem.ParameterSubstitution}
    {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    {parameter : TypeParameterId} (member : parameter ∈ parameters) :
    ∃ replacement,
      (parameter, replacement) ∈ substitution ∧
        substitution.lookup? parameter = some replacement := by
  have domainMember : parameter ∈
      SourceSemantics.ParameterSubstitution.domain substitution :=
    (exact.mem_domain_iff parameter).mpr member
  rcases List.mem_map.mp domainMember with ⟨entry, entryMember, keyEq⟩
  rcases entry with ⟨candidate, replacement⟩
  simp only at keyEq
  subst candidate
  exact ⟨replacement, entryMember,
    lookup?_eq_some_of_mem_of_domain_nodup exact.domain_nodup entryMember⟩

theorem Exact.mapRange
    {inner : TypeSystem.ParameterSubstitution}
    {parameters : List TypeParameterId}
    (outer : TypeSystem.ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact inner parameters) :
    SourceSemantics.ParameterSubstitution.Exact
      (StructuralSubstitution.ParameterSubstitution.mapRange outer inner)
      parameters := by
  constructor
  · exact exact.parameters_nodup
  · have domainEq :
        SourceSemantics.ParameterSubstitution.domain
            (StructuralSubstitution.ParameterSubstitution.mapRange outer inner) =
          SourceSemantics.ParameterSubstitution.domain inner := by
        simp [StructuralSubstitution.ParameterSubstitution.mapRange,
          SourceSemantics.ParameterSubstitution.domain, List.map_map,
          Function.comp_def]
    rw [domainEq]
    exact exact.domain_permutation

end ParameterSubstitution

namespace Substitution

def mapRange (outer : ParameterSubstitution)
    (inner : TypeSystem.Substitution) : TypeSystem.Substitution :=
  inner.map fun entry => (entry.1, outer.apply entry.2)

theorem lookup?_eq_none_of_not_mem_domain
    {substitution : TypeSystem.Substitution}
    {metavariable : TypeVarId}
    (absent : metavariable ∉ substitution.domain) :
    substitution.lookup? metavariable = none := by
  induction substitution with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      simp only [TypeSystem.Substitution.domain, List.map_cons,
        List.mem_cons, not_or] at absent
      have different : candidate ≠ metavariable := fun equal =>
        absent.1 equal.symm
      simp [TypeSystem.Substitution.lookup?, different, induction absent.2]

theorem lookup?_eq_some_of_mem_of_domain_nodup
    {substitution : TypeSystem.Substitution}
    {metavariable : TypeVarId} {replacement : Ty}
    (unique : substitution.domain.Nodup)
    (member : (metavariable, replacement) ∈ substitution) :
    substitution.lookup? metavariable = some replacement := by
  induction substitution with
  | nil => simp at member
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      simp only [TypeSystem.Substitution.domain, List.map_cons,
        List.nodup_cons] at unique
      rcases unique with ⟨candidateAbsent, restUnique⟩
      simp only [List.mem_cons] at member
      rcases member with member | member
      · cases member
        simp [TypeSystem.Substitution.lookup?]
      · have different : candidate ≠ metavariable := by
          intro equal
          apply candidateAbsent
          rw [equal]
          exact List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
        simp [TypeSystem.Substitution.lookup?, different,
          induction restUnique member]

theorem exists_lookup?_eq_some
    {substitution : TypeSystem.Substitution}
    {variables : List TypeVarId}
    (exact : ExactSubstitution substitution variables)
    {metavariable : TypeVarId} (member : metavariable ∈ variables) :
    ∃ replacement,
      (metavariable, replacement) ∈ substitution ∧
        substitution.lookup? metavariable = some replacement := by
  have domainMember : metavariable ∈ substitution.domain :=
    (exact.mem_domain_iff metavariable).mpr member
  rcases List.mem_map.mp domainMember with ⟨entry, entryMember, keyEq⟩
  rcases entry with ⟨candidate, replacement⟩
  simp only at keyEq
  subst candidate
  exact ⟨replacement, entryMember,
    lookup?_eq_some_of_mem_of_domain_nodup exact.domain_nodup entryMember⟩

theorem ExactSubstitution.mapRange
    {inner : TypeSystem.Substitution} {variables : List TypeVarId}
    (outer : ParameterSubstitution)
    (exact : ExactSubstitution inner variables) :
    ExactSubstitution (Substitution.mapRange outer inner) variables := by
  constructor
  · exact exact.variables_nodup
  · have domainEq :
        (Substitution.mapRange outer inner).domain = inner.domain := by
        simp [Substitution.mapRange, TypeSystem.Substitution.domain,
          List.map_map, Function.comp_def]
    rw [domainEq]
    exact exact.domain_permutation

end Substitution

theorem TypeWellScoped.weakenFlexible
    {context : Context} {smaller larger : List TypeVarId} {type : Ty}
    (included : ∀ metavariable, metavariable ∈ smaller →
      metavariable ∈ larger)
    (wellScoped : TypeWellScoped context smaller type) :
    TypeWellScoped context larger type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped context larger type)
    (motive_2 := fun types _ => TypesWellScoped context larger types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable (included metavariable bound)
  · intro parameter bound owned
    exact .parameter bound owned
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments cataloged arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypesWellScoped.weakenFlexible
    {context : Context} {smaller larger : List TypeVarId} {types : List Ty}
    (included : ∀ metavariable, metavariable ∈ smaller →
      metavariable ∈ larger)
    (wellScoped : TypesWellScoped context smaller types) :
    TypesWellScoped context larger types := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped context larger type)
    (motive_2 := fun types _ => TypesWellScoped context larger types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable (included metavariable bound)
  · intro parameter bound owned
    exact .parameter bound owned
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments cataloged arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

private theorem mem_freeVariables_foldl_application_iff
    (metavariable : TypeVarId) (head : Ty) (arguments : List Ty) :
    metavariable ∈ (arguments.foldl Ty.application head).freeVariables ↔
      metavariable ∈ head.freeVariables ∨
        ∃ argument, argument ∈ arguments ∧
          metavariable ∈ argument.freeVariables := by
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      rw [List.foldl_cons, induction,
        SourceSemantics.mem_freeVariables_application_iff]
      simp only [List.mem_cons]
      constructor
      · rintro ((headMember | argumentMember) | tailMember)
        · exact Or.inl headMember
        · exact Or.inr ⟨argument, Or.inl rfl, argumentMember⟩
        · rcases tailMember with ⟨candidate, candidateMember, occurs⟩
          exact Or.inr ⟨candidate, Or.inr candidateMember, occurs⟩
      · rintro (headMember | ⟨candidate, candidateMember, occurs⟩)
        · exact Or.inl (Or.inl headMember)
        · rcases candidateMember with rfl | candidateMember
          · exact Or.inl (Or.inr occurs)
          · exact Or.inr ⟨candidate, candidateMember, occurs⟩

private theorem mem_freeVariables_nominal_iff
    {metavariable : TypeVarId} {declaration : Resolved.DeclarationId}
    {arguments : List Ty} :
    metavariable ∈ (Ty.nominal declaration arguments).freeVariables ↔
      ∃ argument, argument ∈ arguments ∧
        metavariable ∈ argument.freeVariables := by
  rw [Ty.nominal, Ty.applyMany,
    mem_freeVariables_foldl_application_iff]
  simp [Ty.freeVariables]

/-- Every flexible variable occurring in a well-scoped type belongs to the
explicit flexible binder list of the judgment. -/
theorem TypeWellScoped.freeVariable_mem
    {context : Context} {flexibleVariables : List TypeVarId} {type : Ty}
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    ∀ metavariable, metavariable ∈ type.freeVariables →
      metavariable ∈ flexibleVariables := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      ∀ metavariable, metavariable ∈ type.freeVariables →
        metavariable ∈ flexibleVariables)
    (motive_2 := fun types _ =>
      ∀ type, type ∈ types → ∀ metavariable,
        metavariable ∈ type.freeVariables →
          metavariable ∈ flexibleVariables)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound candidate member
    simp [Ty.freeVariables] at member
    subst candidate
    exact bound
  · intro parameter _ _ metavariable member
    simp [Ty.freeVariables] at member
  · intro builtin metavariable member
    simp [Ty.freeVariables] at member
  · intro dataType arguments _ _ _ argumentsInduction metavariable member
    rw [mem_freeVariables_nominal_iff] at member
    rcases member with ⟨argument, argumentMember, occurs⟩
    exact argumentsInduction argument argumentMember metavariable occurs
  · intro domain codomain _ _ domainInduction codomainInduction
      metavariable member
    rw [SourceSemantics.mem_freeVariables_function_iff] at member
    rcases member with member | member
    · exact domainInduction metavariable member
    · exact codomainInduction metavariable member
  · intro left right _ _ leftInduction rightInduction metavariable member
    rw [SourceSemantics.mem_freeVariables_product_iff] at member
    rcases member with member | member
    · exact leftInduction metavariable member
    · exact rightInduction metavariable member
  · intro key value _ _ keyInduction valueInduction metavariable member
    rw [SourceSemantics.mem_freeVariables_mapping_iff] at member
    rcases member with member | member
    · exact keyInduction metavariable member
    · exact valueInduction metavariable member
  · intro inner _ innerInduction metavariable member
    exact innerInduction metavariable member
  · intro inner _ innerInduction metavariable member
    exact innerInduction metavariable member
  · intro type member
    simp at member
  · intro head tail _ _ headInduction tailInduction type member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact headInduction
    · exact tailInduction type member

theorem TypeWellFormed.freeVariables_eq_nil
    {context : Context} {type : Ty}
    (wellFormed : TypeWellFormed context type) :
    type.freeVariables = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro metavariable member
  have impossible :=
    StructuralSubstitution.TypeWellScoped.freeVariable_mem
      wellFormed.typeWellScoped metavariable member
  simp at impossible

/-- A type closed in the empty whole-program context remains closed after
installing locals, predicates, and a declaration marker, provided the target
still has no rigid binders and shares the same signature catalog. -/
theorem TypeWellScoped.ofSignatures_transport
    {signatures : ProgramSignatures} {target : Context}
    {flexibleVariables : List TypeVarId} {type : Ty}
    (signatures_eq : target.signatures = signatures)
    (wellScoped : TypeWellScoped (Context.ofSignatures signatures)
      flexibleVariables type) :
    TypeWellScoped target flexibleVariables type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexibleVariables type)
    (motive_2 := fun types _ => TypesWellScoped target flexibleVariables types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound
    simp [Context.ofSignatures] at bound
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [Context.ofSignatures, signatures_eq] using cataloged)
      arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypesWellScoped.ofSignatures_transport
    {signatures : ProgramSignatures} {target : Context}
    {flexibleVariables : List TypeVarId} {types : List Ty}
    (signatures_eq : target.signatures = signatures)
    (wellScoped : TypesWellScoped (Context.ofSignatures signatures)
      flexibleVariables types) :
    TypesWellScoped target flexibleVariables types := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexibleVariables type)
    (motive_2 := fun types _ => TypesWellScoped target flexibleVariables types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound
    simp [Context.ofSignatures] at bound
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [Context.ofSignatures, signatures_eq] using cataloged)
      arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypeWellFormed.ofSignatures_transport
    {signatures : ProgramSignatures} {target : Context} {type : Ty}
    (signatures_eq : target.signatures = signatures)
    (binders : TypeParameterBindersWellFormed target)
    (wellFormed : TypeWellFormed (Context.ofSignatures signatures) type) :
    TypeWellFormed target type := {
  binders
  typeWellScoped := TypeWellScoped.ofSignatures_transport signatures_eq
    wellFormed.typeWellScoped
}

theorem TypeWellScoped.transportContext
    {source target : Context} {flexibleVariables : List TypeVarId}
    {type : Ty}
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq : target.currentDeclaration = source.currentDeclaration)
    (wellScoped : TypeWellScoped source flexibleVariables type) :
    TypeWellScoped target flexibleVariables type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexibleVariables type)
    (motive_2 := fun types _ => TypesWellScoped target flexibleVariables types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound owned
    exact .parameter (by simpa [parameters_eq] using bound)
      (by simpa [declaration_eq] using owned)
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [signatures_eq] using cataloged) arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypesWellScoped.transportContext
    {source target : Context} {flexibleVariables : List TypeVarId}
    {types : List Ty}
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq : target.currentDeclaration = source.currentDeclaration)
    (wellScoped : TypesWellScoped source flexibleVariables types) :
    TypesWellScoped target flexibleVariables types := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexibleVariables type)
    (motive_2 := fun types _ => TypesWellScoped target flexibleVariables types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound owned
    exact .parameter (by simpa [parameters_eq] using bound)
      (by simpa [declaration_eq] using owned)
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [signatures_eq] using cataloged) arity argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypeParameterBindersWellFormed.transportContext
    {source target : Context}
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq : target.currentDeclaration = source.currentDeclaration)
    (wellFormed : TypeParameterBindersWellFormed source) :
    TypeParameterBindersWellFormed target := by
  rcases wellFormed with ⟨nodup, owned⟩
  constructor
  · simpa [parameters_eq] using nodup
  · intro parameter member
    rw [declaration_eq]
    exact owned parameter (by simpa [parameters_eq] using member)

theorem TypeWellFormed.transportContext
    {source target : Context} {type : Ty}
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq : target.currentDeclaration = source.currentDeclaration)
    (wellFormed : TypeWellFormed source type) :
    TypeWellFormed target type := {
  binders := StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    parameters_eq declaration_eq wellFormed.binders
  typeWellScoped := StructuralSubstitution.TypeWellScoped.transportContext
    signatures_eq parameters_eq declaration_eq wellFormed.typeWellScoped
}

theorem SchemeWellFormed.transportContext
    {source target : Context} {scheme : Scheme}
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq : target.currentDeclaration = source.currentDeclaration)
    (variables_eq : target.typeVariables = source.typeVariables)
    (residualVariables_eq :
      target.residualTypeVariables = source.residualTypeVariables)
    (wellFormed : SchemeWellFormed source scheme) :
    SchemeWellFormed target scheme := {
  binders := StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    parameters_eq declaration_eq wellFormed.binders
  quantified_nodup := wellFormed.quantified_nodup
  body := by
    unfold admissibleTypeVariables
    rw [variables_eq, residualVariables_eq]
    exact StructuralSubstitution.TypeWellScoped.transportContext signatures_eq
      parameters_eq declaration_eq wellFormed.body
}

/-- Exact substitution of every rigid binder turns a generic well-scoped type
into a type scoped by the closed substituted context. -/
theorem TypeWellScoped.applyParameters
    {context : Context} {flexibleVariables : List TypeVarId} {type : Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    TypeWellScoped (applyContext substitution context) flexibleVariables
      (substitution.apply type) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      TypeWellScoped (applyContext substitution context) flexibleVariables
        (substitution.apply type))
    (motive_2 := fun types _ =>
      TypesWellScoped (applyContext substitution context) flexibleVariables
        (types.map substitution.apply))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound _
    obtain ⟨replacement, member, lookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some exact bound
    simp only [TypeSystem.ParameterSubstitution.apply, lookup,
      Option.getD_some]
    exact StructuralSubstitution.TypeWellScoped.weakenFlexible
      (fun metavariable impossible => by simp at impossible)
      (range _ _ member).typeWellScoped
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    rw [apply_nominal]
    exact .nominal dataType (arguments.map substitution.apply)
      (by simpa [applyContext] using cataloged)
      (by simpa using arity) argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypesWellScoped.applyParameters
    {context : Context} {flexibleVariables : List TypeVarId}
    {types : List Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellScoped : TypesWellScoped context flexibleVariables types) :
    TypesWellScoped (applyContext substitution context) flexibleVariables
      (types.map substitution.apply) := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ =>
      TypeWellScoped (applyContext substitution context) flexibleVariables
        (substitution.apply type))
    (motive_2 := fun types _ =>
      TypesWellScoped (applyContext substitution context) flexibleVariables
        (types.map substitution.apply))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound _
    obtain ⟨replacement, member, lookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some exact bound
    simp only [TypeSystem.ParameterSubstitution.apply, lookup,
      Option.getD_some]
    exact StructuralSubstitution.TypeWellScoped.weakenFlexible
      (fun metavariable impossible => by simp at impossible)
      (range _ _ member).typeWellScoped
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    rw [apply_nominal]
    exact .nominal dataType (arguments.map substitution.apply)
      (by simpa [applyContext] using cataloged)
      (by simpa using arity) argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypeParameterBindersWellFormed.applyContext
    (substitution : ParameterSubstitution) (context : Context) :
    TypeParameterBindersWellFormed (applyContext substitution context) := by
  constructor
  · change ([] : List TypeParameterId).Nodup
    simp
  · intro parameter member
    change parameter ∈ ([] : List TypeParameterId) at member
    simp at member

theorem TypeWellFormed.applyParameters
    {context : Context} {type : Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : TypeWellFormed context type) :
    TypeWellFormed (applyContext substitution context)
      (substitution.apply type) := {
  binders := TypeParameterBindersWellFormed.applyContext substitution context
  typeWellScoped := StructuralSubstitution.TypeWellScoped.applyParameters
    substitution exact range wellFormed.typeWellScoped
}

@[simp] theorem freeVariables_applyParameters
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (type : Ty) :
    (substitution.apply type).freeVariables = type.freeVariables := by
  apply StructuralSubstitution.ParameterSubstitution.freeVariables_apply
  intro parameter replacement member
  exact StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
    (range parameter replacement member)

@[simp] theorem admissibleTypeVariables_applyContext_apply
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (type : Ty) :
    admissibleTypeVariables (applyContext substitution context)
        (substitution.apply type) =
      admissibleTypeVariables context type := by
  unfold admissibleTypeVariables
  rw [StructuralSubstitution.freeVariables_applyParameters substitution range]
  rfl

theorem TypeAdmissible.applyParameters
    {context : Context} {type : Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (admissible : TypeAdmissible context type) :
    TypeAdmissible (applyContext substitution context)
      (substitution.apply type) := {
  binders := TypeParameterBindersWellFormed.applyContext substitution context
  typeWellScoped := by
    rw [StructuralSubstitution.admissibleTypeVariables_applyContext_apply
      substitution range]
    exact StructuralSubstitution.TypeWellScoped.applyParameters
      substitution exact range admissible.typeWellScoped
}

@[simp] theorem Scheme.freeVariables_applyScheme
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (scheme : Scheme) :
    (applyScheme substitution scheme).freeVariables = scheme.freeVariables := by
  change
    (substitution.apply scheme.body).freeVariables.filter
        (fun metavariable => !(metavariable ∈ scheme.quantified)) =
      scheme.body.freeVariables.filter
        (fun metavariable => !(metavariable ∈ scheme.quantified))
  rw [StructuralSubstitution.freeVariables_applyParameters substitution range]

@[simp] theorem predicateVariables_applyParameters
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (predicate : ProgramPredicate) :
    Frontend.TypedTraitResolution.predicateVariables
        (ProgramPredicate.applyParameters substitution predicate) =
      Frontend.TypedTraitResolution.predicateVariables predicate := by
  change Frontend.TypedTraitResolution.predicateVariables
      (Frontend.TypedTraitResolution.applyParameterSubstitution substitution
        predicate) =
    Frontend.TypedTraitResolution.predicateVariables predicate
  exact
    Frontend.TypedTraitResolution.predicateVariables_applyParameterSubstitution_of_freeVariables_eq
      substitution predicate fun type =>
        StructuralSubstitution.freeVariables_applyParameters substitution range
          type

@[simp] theorem GeneralizationBlockedVariablesExcept.applyParameters
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (exemptRequirements : List RequirementId) :
    GeneralizationBlockedVariablesExcept (applyContext substitution context)
        exemptRequirements =
      GeneralizationBlockedVariablesExcept context exemptRequirements := by
  have ledger :
      ((context.solvedRequirements.map (applySolvedRequirement substitution)).filter
          fun requirement => !exemptRequirements.contains requirement.id).flatMap
            (fun requirement =>
              Frontend.TypedTraitResolution.predicateVariables
                requirement.predicate) =
        (context.solvedRequirements.filter fun requirement =>
          !exemptRequirements.contains requirement.id).flatMap
            (fun requirement =>
              Frontend.TypedTraitResolution.predicateVariables
                requirement.predicate) := by
    induction context.solvedRequirements with
    | nil => rfl
    | cons requirement requirements induction =>
        by_cases exempt : exemptRequirements.contains requirement.id
        · simp [applySolvedRequirement, exempt, induction]
        · simp [applySolvedRequirement, exempt, induction,
            StructuralSubstitution.predicateVariables_applyParameters
              substitution range]
  simp [GeneralizationBlockedVariablesExcept, applyContext, applyLocals,
    StructuralSubstitution.Scheme.freeVariables_applyScheme substitution range,
    List.flatMap_map, ledger]

@[simp] theorem GeneralizationBlockedVariables.applyParameters
    {context : Context} (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution) :
    GeneralizationBlockedVariables (applyContext substitution context) =
      GeneralizationBlockedVariables context := by
  exact GeneralizationBlockedVariablesExcept.applyParameters substitution range []

theorem SchemeGeneralizesExcept.applyParameters
    {context : Context} {scheme : Scheme}
    (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (exemptRequirements : List RequirementId)
    (generalizes : SchemeGeneralizesExcept context exemptRequirements scheme) :
    SchemeGeneralizesExcept (applyContext substitution context)
      exemptRequirements (applyScheme substitution scheme) := by
  unfold SchemeGeneralizesExcept at generalizes ⊢
  change
    scheme.quantified =
      (substitution.apply scheme.body).freeVariables.filter
        (fun metavariable =>
          !(GeneralizationBlockedVariablesExcept
            (applyContext substitution context) exemptRequirements).contains
              metavariable)
  rw [StructuralSubstitution.freeVariables_applyParameters substitution range,
    StructuralSubstitution.GeneralizationBlockedVariablesExcept.applyParameters
      substitution range]
  exact generalizes

theorem SchemeGeneralizes.applyParameters
    {context : Context} {scheme : Scheme}
    (substitution : ParameterSubstitution)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (generalizes : SchemeGeneralizes context scheme) :
    SchemeGeneralizes (applyContext substitution context)
      (applyScheme substitution scheme) := by
  exact SchemeGeneralizesExcept.applyParameters substitution range [] generalizes

theorem SchemeWellFormed.applyParameters
    {context : Context} {scheme : Scheme}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : SchemeWellFormed context scheme) :
    SchemeWellFormed (applyContext substitution context)
      (applyScheme substitution scheme) := {
  binders := TypeParameterBindersWellFormed.applyContext substitution context
  quantified_nodup := wellFormed.quantified_nodup
  body := by
    change TypeWellScoped (applyContext substitution context)
      (admissibleTypeVariables (applyContext substitution context)
        (substitution.apply scheme.body) ++ scheme.quantified)
      (substitution.apply scheme.body)
    rw [StructuralSubstitution.admissibleTypeVariables_applyContext_apply
      substitution range]
    exact StructuralSubstitution.TypeWellScoped.applyParameters substitution
      exact range wellFormed.body
}

theorem TypeWellScoped.applySubstitution_eq_self
    {context : Context} {type : Ty} (substitution : TypeSystem.Substitution)
    (wellScoped : TypeWellScoped context [] type) :
    substitution.apply type = type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => substitution.apply type = type)
    (motive_2 := fun types _ => types.map substitution.apply = types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    simp at bound
  · intro parameter _ _
    rfl
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [applyFlexible_nominal, argumentsInduction]
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply]
    rw [keyInduction, valueInduction]
  · intro inner _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · intro inner _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem TypesWellScoped.applySubstitution_eq_self
    {context : Context} {types : List Ty}
    (substitution : TypeSystem.Substitution)
    (wellScoped : TypesWellScoped context [] types) :
    types.map substitution.apply = types := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ => substitution.apply type = type)
    (motive_2 := fun types _ => types.map substitution.apply = types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    simp at bound
  · intro parameter _ _
    rfl
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [applyFlexible_nominal, argumentsInduction]
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply]
    rw [keyInduction, valueInduction]
  · intro inner _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · intro inner _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem TypeWellScoped.applyMixed_compose
    {context : Context} {flexibleVariables substitutedVariables : List TypeVarId}
    {type : Ty}
    (outer : ParameterSubstitution) (inner : TypeSystem.Substitution)
    (outerExact : SourceSemantics.ParameterSubstitution.Exact outer
      context.typeParameters)
    (outerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context) outer)
    (innerExact : ExactSubstitution inner substitutedVariables)
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    outer.apply (inner.apply type) =
      (Substitution.mapRange outer inner).apply (outer.apply type) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (Substitution.mapRange outer inner).apply (outer.apply type))
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        (types.map outer.apply).map
          (Substitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable _
    by_cases substituted : metavariable ∈ substitutedVariables
    · obtain ⟨replacement, member, innerLookup⟩ :=
        Substitution.exists_lookup?_eq_some innerExact substituted
      have mappedMember :
          (metavariable, outer.apply replacement) ∈
            Substitution.mapRange outer inner :=
        List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
      have mappedLookup :=
        Substitution.lookup?_eq_some_of_mem_of_domain_nodup
          (StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
            innerExact).domain_nodup mappedMember
      simp [TypeSystem.Substitution.apply,
        TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
    · have innerAbsent : metavariable ∉ inner.domain := by
        intro member
        exact substituted ((innerExact.mem_domain_iff metavariable).mp member)
      have mappedExact :=
        StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
          innerExact
      have mappedAbsent :
          metavariable ∉ (Substitution.mapRange outer inner).domain := by
        intro member
        exact substituted ((mappedExact.mem_domain_iff metavariable).mp member)
      have innerLookup :=
        Substitution.lookup?_eq_none_of_not_mem_domain innerAbsent
      have mappedLookup :=
        Substitution.lookup?_eq_none_of_not_mem_domain mappedAbsent
      simp [TypeSystem.Substitution.apply,
        TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
  · intro parameter bound _
    obtain ⟨replacement, member, outerLookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some outerExact bound
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply, outerLookup, Option.getD_some]
    symm
    exact StructuralSubstitution.TypeWellScoped.applySubstitution_eq_self
      (Substitution.mapRange outer inner)
      (outerRange parameter replacement member).typeWellScoped
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [applyFlexible_nominal, apply_nominal, apply_nominal,
      applyFlexible_nominal]
    exact congrArg (fun arguments => Ty.nominal dataType.id arguments)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem SchemeInstantiatesAt.applyParameters
    {context : Context} {scheme : Scheme} {type : Ty}
    (outer : ParameterSubstitution)
    (outerExact : SourceSemantics.ParameterSubstitution.Exact outer
      context.typeParameters)
    (outerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context) outer)
    (instantiates : SchemeInstantiatesAt context scheme type) :
    SchemeInstantiatesAt (applyContext outer context)
      (applyScheme outer scheme) (outer.apply type) := by
  cases instantiates with
  | intro schemeWellFormed inner innerExact innerRange result =>
      refine .intro
        (StructuralSubstitution.SchemeWellFormed.applyParameters outer
          outerExact outerRange schemeWellFormed)
        (Substitution.mapRange outer inner)
        (StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
          innerExact)
        ?_ ?_
      · intro metavariable replacement member
        rcases List.mem_map.mp member with ⟨entry, entryMember, entryEq⟩
        rcases entry with ⟨innerVariable, innerReplacement⟩
        cases entryEq
        exact StructuralSubstitution.TypeAdmissible.applyParameters outer
          outerExact outerRange
          (innerRange innerVariable innerReplacement entryMember)
      · change (Substitution.mapRange outer inner).apply
          (outer.apply scheme.body) = outer.apply type
        rw [← result]
        exact (StructuralSubstitution.TypeWellScoped.applyMixed_compose outer
          inner outerExact outerRange innerExact schemeWellFormed.body).symm

theorem TypeWellScoped.applyParameters_compose
    {context : Context} {flexibleVariables : List TypeVarId} {type : Ty}
    (outer inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    outer.apply (inner.apply type) =
      (ParameterSubstitution.mapRange outer inner).apply type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (ParameterSubstitution.mapRange outer inner).apply type)
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        types.map (ParameterSubstitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable _
    rfl
  · intro parameter bound _
    obtain ⟨replacement, member, innerLookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some innerExact bound
    have mappedMember :
        (parameter, outer.apply replacement) ∈
          ParameterSubstitution.mapRange outer inner :=
      List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
    have mappedLookup :=
      ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
        (StructuralSubstitution.ParameterSubstitution.Exact.mapRange outer
          innerExact).domain_nodup mappedMember
    simp [TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [apply_nominal, apply_nominal, apply_nominal]
    exact congrArg (fun arguments => Ty.nominal dataType.id arguments)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem TypesWellScoped.applyParameters_compose
    {context : Context} {flexibleVariables : List TypeVarId}
    {types : List Ty}
    (outer inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellScoped : TypesWellScoped context flexibleVariables types) :
    (types.map inner.apply).map outer.apply =
      types.map (ParameterSubstitution.mapRange outer inner).apply := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (ParameterSubstitution.mapRange outer inner).apply type)
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        types.map (ParameterSubstitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable _
    rfl
  · intro parameter bound _
    obtain ⟨replacement, member, innerLookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some innerExact bound
    have mappedMember :
        (parameter, outer.apply replacement) ∈
          ParameterSubstitution.mapRange outer inner :=
      List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
    have mappedLookup :=
      ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
        (StructuralSubstitution.ParameterSubstitution.Exact.mapRange outer
          innerExact).domain_nodup mappedMember
    simp [TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [apply_nominal, apply_nominal, apply_nominal]
    exact congrArg (fun arguments => Ty.nominal dataType.id arguments)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem ParameterSubstitution.RangeWellFormed.mapRange
    {context : Context} {inner outer : TypeSystem.ParameterSubstitution}
    (outerExact : SourceSemantics.ParameterSubstitution.Exact outer
      context.typeParameters)
    (outerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context) outer)
    (innerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      context inner) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context)
      (ParameterSubstitution.mapRange outer inner) := by
  intro parameter replacement member
  rcases List.mem_map.mp member with ⟨entry, entryMember, entryEq⟩
  rcases entry with ⟨innerParameter, innerReplacement⟩
  cases entryEq
  exact StructuralSubstitution.TypeWellFormed.applyParameters outer outerExact
    outerRange (innerRange innerParameter innerReplacement entryMember)

theorem ParameterSubstitution.RangeAdmissible.mapRange
    {context : Context} {inner outer : TypeSystem.ParameterSubstitution}
    (outerExact : SourceSemantics.ParameterSubstitution.Exact outer
      context.typeParameters)
    (outerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context) outer)
    (innerRange : SourceSemantics.ParameterSubstitution.RangeAdmissible
      context inner) :
    SourceSemantics.ParameterSubstitution.RangeAdmissible
      (applyContext outer context)
      (ParameterSubstitution.mapRange outer inner) := by
  intro parameter replacement member
  rcases List.mem_map.mp member with ⟨entry, entryMember, entryEq⟩
  rcases entry with ⟨innerParameter, innerReplacement⟩
  cases entryEq
  exact StructuralSubstitution.TypeAdmissible.applyParameters outer outerExact
    outerRange (innerRange innerParameter innerReplacement entryMember)

theorem TypesWellFormed.applyParameters
    {context : Context} {types : List Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : TypesWellFormed context types) :
    TypesWellFormed (applyContext substitution context)
      (types.map substitution.apply) := by
  intro type member
  rcases List.mem_map.mp member with ⟨original, originalMember, typeEq⟩
  subst type
  exact StructuralSubstitution.TypeWellFormed.applyParameters substitution exact
    range (wellFormed original originalMember)

theorem TypesWellFormed.applyParameters_compose
    {context : Context} {types : List Ty}
    (outer inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellFormed : TypesWellFormed context types) :
    (types.map inner.apply).map outer.apply =
      types.map (ParameterSubstitution.mapRange outer inner).apply := by
  induction types with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact StructuralSubstitution.TypeWellScoped.applyParameters_compose
          outer inner innerExact (wellFormed head (by simp)).typeWellScoped
      · exact induction (fun type member => wellFormed type (by simp [member]))

theorem TypesWellFormed.toTypesWellScoped
    {context : Context} {types : List Ty}
    (wellFormed : TypesWellFormed context types) :
    TypesWellScoped context [] types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (wellFormed head (by simp)).typeWellScoped
        (induction (fun type member => wellFormed type (by simp [member])))

theorem TypesWellScoped.productMany
    {context : Context} {flexibleVariables : List TypeVarId}
    {types : List Ty}
    (wellScoped : TypesWellScoped context flexibleVariables types) :
    TypeWellScoped context flexibleVariables (Ty.productMany types) := by
  cases wellScoped with
  | nil => exact .builtin .unit
  | @cons head tail headScoped tailScoped =>
      cases tail with
      | nil => exact headScoped
      | cons next rest =>
          exact .product headScoped
            (StructuralSubstitution.TypesWellScoped.productMany tailScoped)

theorem PredicateWellFormed.applyParameters
    {context : Context} {predicate : ProgramPredicate}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : PredicateWellFormed context predicate) :
    PredicateWellFormed (applyContext substitution context)
      (ProgramPredicate.applyParameters substitution predicate) := by
  constructor
  · exact StructuralSubstitution.TypeWellFormed.applyParameters substitution
      exact range wellFormed.subject
  · intro argument member
    rcases List.mem_map.mp member with ⟨original, originalMember, argumentEq⟩
    subst argument
    exact StructuralSubstitution.TypeWellFormed.applyParameters substitution
      exact range (wellFormed.arguments original originalMember)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin with
        | int =>
            have traitValid := wellFormed.trait
            rw [traitEq] at traitValid
            simpa [ProgramPredicate.applyParameters, traitEq] using traitValid
    | declaration id =>
        have traitValid := wellFormed.trait
        rw [traitEq] at traitValid
        rcases traitValid with ⟨signature, member, idEq, arity⟩
        simp only [ProgramPredicate.applyParameters, traitEq]
        exact ⟨signature, by simpa [applyContext] using member, idEq,
          by simpa [ProgramPredicate.applyParameters] using arity⟩

theorem PredicateAdmissible.applyParameters
    {context : Context} {predicate : ProgramPredicate}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (admissible : PredicateAdmissible context predicate) :
    PredicateAdmissible (applyContext substitution context)
      (ProgramPredicate.applyParameters substitution predicate) := by
  constructor
  · exact StructuralSubstitution.TypeAdmissible.applyParameters substitution
      exact range admissible.subject
  · intro argument member
    rcases List.mem_map.mp member with ⟨original, originalMember, argumentEq⟩
    subst argument
    exact StructuralSubstitution.TypeAdmissible.applyParameters substitution
      exact range (admissible.arguments original originalMember)
  · cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin with
        | int =>
            have traitValid := admissible.trait
            rw [traitEq] at traitValid
            simpa [ProgramPredicate.applyParameters, traitEq] using traitValid
    | declaration id =>
        have traitValid := admissible.trait
        rw [traitEq] at traitValid
        rcases traitValid with ⟨signature, member, idEq, arity⟩
        simp only [ProgramPredicate.applyParameters, traitEq]
        exact ⟨signature, by simpa [applyContext] using member, idEq,
          by simpa [ProgramPredicate.applyParameters] using arity⟩

/-- Rigid declaration instantiation commutes with one shared flexible
local-scheme instantiation when the predicate is meaningful in the source
context. -/
theorem PredicateAdmissible.applyMixed_compose
    {context : Context} {predicate : ProgramPredicate}
    {substitutedVariables : List TypeVarId}
    (outer : ParameterSubstitution) (inner : TypeSystem.Substitution)
    (outerExact : SourceSemantics.ParameterSubstitution.Exact outer
      context.typeParameters)
    (outerRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext outer context) outer)
    (innerExact : ExactSubstitution inner substitutedVariables)
    (admissible : PredicateAdmissible context predicate) :
    ProgramPredicate.applyParameters outer
        (Frontend.TypedTraitResolution.applySubstitution inner predicate) =
      Frontend.TypedTraitResolution.applySubstitution
        (Substitution.mapRange outer inner)
        (ProgramPredicate.applyParameters outer predicate) := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [ProgramPredicate.applyParameters,
        Frontend.TypedTraitResolution.applySubstitution]
      congr 1
      · exact StructuralSubstitution.TypeWellScoped.applyMixed_compose outer
          inner outerExact outerRange innerExact
          admissible.subject.typeWellScoped
      · rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro argument member
        exact StructuralSubstitution.TypeWellScoped.applyMixed_compose outer
          inner outerExact outerRange innerExact
          (admissible.arguments argument member).typeWellScoped

theorem PredicatesWellFormed.applyParameters
    {context : Context} {predicates : List ProgramPredicate}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : PredicatesWellFormed context predicates) :
    PredicatesWellFormed (applyContext substitution context)
      (predicates.map (ProgramPredicate.applyParameters substitution)) := by
  intro predicate member
  rcases List.mem_map.mp member with ⟨original, originalMember, predicateEq⟩
  subst predicate
  exact StructuralSubstitution.PredicateWellFormed.applyParameters substitution
    exact range (wellFormed original originalMember)

theorem PredicateWellFormed.applyParameters_compose
    {context : Context} {predicate : ProgramPredicate}
    (outer inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellFormed : PredicateWellFormed context predicate) :
    ProgramPredicate.applyParameters outer
        (ProgramPredicate.applyParameters inner predicate) =
      ProgramPredicate.applyParameters
        (ParameterSubstitution.mapRange outer inner) predicate := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [ProgramPredicate.applyParameters]
      congr 1
      · exact StructuralSubstitution.TypeWellScoped.applyParameters_compose
          outer inner innerExact wellFormed.subject.typeWellScoped
      · exact StructuralSubstitution.TypesWellFormed.applyParameters_compose
          outer inner innerExact wellFormed.arguments

theorem PredicatesWellFormed.applyParameters_compose
    {context : Context} {predicates : List ProgramPredicate}
    (outer inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellFormed : PredicatesWellFormed context predicates) :
    (predicates.map (ProgramPredicate.applyParameters inner)).map
        (ProgramPredicate.applyParameters outer) =
      predicates.map (ProgramPredicate.applyParameters
        (ParameterSubstitution.mapRange outer inner)) := by
  induction predicates with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact StructuralSubstitution.PredicateWellFormed.applyParameters_compose
          outer inner innerExact (wellFormed head (by simp))
      · exact induction (fun predicate member =>
          wellFormed predicate (by simp [member]))

namespace ParameterSubstitution.RangeWellFormed

theorem atApplyContextOfBase
    {context : Context} {substitution : ParameterSubstitution}
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures context.signatures) substitution) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution := by
  intro parameter replacement member
  exact StructuralSubstitution.TypeWellFormed.ofSignatures_transport rfl
    (TypeParameterBindersWellFormed.applyContext substitution context)
    (range parameter replacement member)

theorem underSourceLocal
    {context : Context} {substitution : ParameterSubstitution}
    {id : Resolved.LocalId} {scheme : Scheme}
    {requirements : List LocalSchemeRequirement}
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution
        (context.withLocal id scheme requirements)) substitution := by
  intro parameter replacement member
  exact StructuralSubstitution.TypeWellFormed.transportContext
    (source := applyContext substitution context)
    (target := applyContext substitution
      (context.withLocal id scheme requirements))
    rfl rfl rfl (range parameter replacement member)

end ParameterSubstitution.RangeWellFormed

@[simp] theorem applyContext_withLocal
    (substitution : ParameterSubstitution) (context : Context)
    (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement := []) :
    applyContext substitution (context.withLocal id scheme requirements) =
      (applyContext substitution context).withLocal id
        (applyScheme substitution scheme)
        (requirements.map
          (LocalSchemeRequirement.applyParameters substitution)) := by
  rfl

@[simp] theorem applyContext_withTypeVariables
    (substitution : ParameterSubstitution) (context : Context)
    (variables : List TypeVarId) :
    applyContext substitution (context.withTypeVariables variables) =
      (applyContext substitution context).withTypeVariables variables := by
  rfl

@[simp] theorem applyContext_withResidualTypeVariables
    (substitution : ParameterSubstitution) (context : Context) :
    applyContext substitution context.withResidualTypeVariables =
      (applyContext substitution context).withResidualTypeVariables := by
  rfl

@[simp] theorem applyContext_localSchemeInitializerContext
    (substitution : ParameterSubstitution) (context : Context)
    (binder : TypedBinder) :
    applyContext substitution (localSchemeInitializerContext context binder) =
      localSchemeInitializerContext (applyContext substitution context)
        (applyBinder substitution binder) := by
  simp [localSchemeInitializerContext, applyContext, Context.withTypeVariables,
    Context.withAssumptions, applyBinder, applyScheme,
    LocalSchemeRequirement.applyParameters, List.map_map,
    Function.comp_def]

@[simp] theorem applyContext_declarationContext
    (substitution : ParameterSubstitution) (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeParameterId)
    (assumptions : List ProgramPredicate)
    (requirements : List SolvedRequirement) :
    applyContext substitution
        (declarationContext signatures owner parameters assumptions requirements) =
      declarationContext signatures owner []
        (assumptions.map (ProgramPredicate.applyParameters substitution))
        (requirements.map (applySolvedRequirement substitution)) := by
  rfl

private theorem lookup_applyLocals
    {locals : Resolved.LocalScope Scheme} {id : Resolved.LocalId}
    {scheme : Scheme} (substitution : ParameterSubstitution)
    (lookup : Resolved.LocalScope.Lookup locals id scheme) :
    Resolved.LocalScope.Lookup (applyLocals substitution locals) id
      (applyScheme substitution scheme) := by
  induction lookup with
  | head => exact .head
  | tail different _ induction => exact .tail different induction

private theorem lookup_applyLocalSchemeRequirements
    {requirements : Resolved.LocalScope (List LocalSchemeRequirement)}
    {id : Resolved.LocalId} {localRequirements : List LocalSchemeRequirement}
    (substitution : ParameterSubstitution)
    (lookup : Resolved.LocalScope.Lookup requirements id localRequirements) :
    Resolved.LocalScope.Lookup
      (applyLocalSchemeRequirements substitution requirements) id
      (localRequirements.map
        (LocalSchemeRequirement.applyParameters substitution)) := by
  induction lookup with
  | head => exact .head
  | tail different _ induction => exact .tail different induction

theorem LocalLookup.applyParameters
    {context : Context} {id : Resolved.LocalId} {scheme : Scheme}
    (substitution : ParameterSubstitution)
    (lookup : context.LocalLookup id scheme) :
    (applyContext substitution context).LocalLookup id
      (applyScheme substitution scheme) := by
  exact lookup_applyLocals substitution lookup

theorem LocalSchemeRequirementsLookup.applyParameters
    {context : Context} {id : Resolved.LocalId}
    {requirements : List LocalSchemeRequirement}
    (substitution : ParameterSubstitution)
    (lookup : context.LocalSchemeRequirementsLookup id requirements) :
    (applyContext substitution context).LocalSchemeRequirementsLookup id
      (requirements.map
        (LocalSchemeRequirement.applyParameters substitution)) := by
  exact lookup_applyLocalSchemeRequirements substitution lookup

theorem LocalFresh.applyParameters
    {context : Context} {id : Resolved.LocalId}
    (substitution : ParameterSubstitution)
    (fresh : LocalFresh context id) :
    LocalFresh (applyContext substitution context) id := by
  simpa [LocalFresh, applyContext, applyLocals,
    applyLocalSchemeRequirements, List.map_map, Function.comp_def] using fresh

/-- The one semantic premise not supplied by purely structural substitution:
retained implementation evidence remains valid after its predicates and types
are instantiated.  Assumption evidence needs no global premise: its local
validity already records membership in the current assumption scope, which is
mapped structurally by `applyContext`.  `EvidenceValid.applyParameters`
discharges the implementation premise once impl-head matching closure is
available. -/
structure ContextSubstitutionValid (substitution : ParameterSubstitution)
    (context : Context) : Prop where
  exact : SourceSemantics.ParameterSubstitution.Exact substitution
    context.typeParameters
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (applyContext substitution context) substitution
  implementationRequirements : ∀ requirement evidence,
    requirement ∈ context.solvedRequirements →
    requirement.evidence = .implementation evidence →
      SolvedRequirementValid (applyContext substitution context)
        (applySolvedRequirement substitution requirement)

theorem SolvedRequirementValid.transportContext
    {source target : Context} {requirement : SolvedRequirement}
    (signatures_eq : target.signatures = source.signatures)
    (assumptions_eq : target.assumptions = source.assumptions)
    (valid : SolvedRequirementValid source requirement) :
    SolvedRequirementValid target requirement := by
  cases valid with
  | intro evidenceValid =>
      exact .intro (by simpa [signatures_eq, assumptions_eq] using evidenceValid)

theorem ContextSubstitutionValid.underLocal
    {substitution : ParameterSubstitution} {context : Context}
    {id : Resolved.LocalId} {scheme : Scheme}
    {requirements : List LocalSchemeRequirement}
    (valid : ContextSubstitutionValid substitution context) :
    ContextSubstitutionValid substitution
      (context.withLocal id scheme requirements) := {
  exact := by simpa [Context.withLocal] using valid.exact
  range := ParameterSubstitution.RangeWellFormed.underSourceLocal valid.range
  implementationRequirements := by
    intro requirement evidence member evidenceEq
    have member' : requirement ∈ context.solvedRequirements := by
      simpa [Context.withLocal] using member
    exact StructuralSubstitution.SolvedRequirementValid.transportContext
      (source := applyContext substitution context)
      (target := applyContext substitution
        (context.withLocal id scheme requirements))
      rfl rfl
        (valid.implementationRequirements requirement evidence member' evidenceEq)
}

/-- Rigid declaration instantiation is insensitive to an ambient flexible
initializer scope. -/
theorem ContextSubstitutionValid.withTypeVariables
    {substitution : ParameterSubstitution} {context : Context}
    (valid : ContextSubstitutionValid substitution context)
    (variables : List TypeVarId) :
    ContextSubstitutionValid substitution
      (context.withTypeVariables variables) := {
  exact := by simpa [Context.withTypeVariables] using valid.exact
  range := by
    intro parameter replacement member
    have original := valid.range parameter replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := applyContext substitution context)
      (target := applyContext substitution
        (context.withTypeVariables variables))
      rfl rfl rfl original
  implementationRequirements := by
    intro requirement evidence member evidenceEq
    have originalMember : requirement ∈ context.solvedRequirements := by
      simpa [Context.withTypeVariables] using member
    exact StructuralSubstitution.SolvedRequirementValid.transportContext
      (source := applyContext substitution context)
      (target := applyContext substitution
        (context.withTypeVariables variables))
      rfl rfl
        (valid.implementationRequirements requirement evidence originalMember
          evidenceEq)
}

/-- Rigid substitution remains valid while the predicates abstracted by a
qualified local scheme are temporarily added as initializer assumptions. -/
theorem ContextSubstitutionValid.localSchemeInitializer
    {substitution : ParameterSubstitution} {context : Context}
    (valid : ContextSubstitutionValid substitution context)
    (binder : TypedBinder) :
    ContextSubstitutionValid substitution
      (localSchemeInitializerContext context binder) := {
  exact := by
    simpa [localSchemeInitializerContext, Context.withTypeVariables,
      Context.withAssumptions] using valid.exact
  range := by
    intro parameter replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := applyContext substitution context)
      (target := applyContext substitution
        (localSchemeInitializerContext context binder))
      rfl rfl rfl (valid.range parameter replacement member)
  implementationRequirements := by
    intro requirement evidence member evidenceEq
    have originalMember : requirement ∈ context.solvedRequirements := by
      simpa [localSchemeInitializerContext, Context.withTypeVariables,
        Context.withAssumptions] using member
    cases valid.implementationRequirements requirement evidence originalMember
        evidenceEq with
    | intro evidenceValid =>
        exact .intro (evidenceValid.weakenAssumptions (by
          intro predicate predicateMem
          rw [StructuralSubstitution.applyContext_localSchemeInitializerContext]
          change predicate ∈
            (applyContext substitution context).assumptions ++
              (applyBinder substitution binder).schemeRequirements.map
                (fun requirement => requirement.predicate)
          exact List.mem_append_left _ predicateMem))
}

theorem RequirementProves.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {id : RequirementId} {predicate : ProgramPredicate}
    (valid : ContextSubstitutionValid substitution context)
    (proves : RequirementProves context id predicate) :
    RequirementProves (applyContext substitution context) id
      (ProgramPredicate.applyParameters substitution predicate) := by
  rcases proves with ⟨requirement, contains, predicateEq, evidenceValid⟩
  rcases contains with ⟨member, idEq⟩
  refine ⟨applySolvedRequirement substitution requirement, ?_, ?_, ?_⟩
  · constructor
    · change applySolvedRequirement substitution requirement ∈
        context.solvedRequirements.map (applySolvedRequirement substitution)
      exact List.mem_map.mpr ⟨requirement, member, rfl⟩
    · exact idEq
  · simp [applySolvedRequirement, predicateEq]
  · cases evidenceEq : requirement.evidence with
    | assumption assumption =>
        cases evidenceValid with
        | intro retainedValid =>
            rw [evidenceEq] at retainedValid
            cases retainedValid with
            | intro represents semanticValid =>
                cases represents with
                | assumption =>
                    cases semanticValid with
                    | assumption goalMem =>
                        apply SolvedRequirementValid.intro
                        simp only [applyContext, applySolvedRequirement,
                          evidenceEq, applyPredicateEvidence]
                        exact .intro (.assumption _) (.assumption (by
                          exact List.mem_map.mpr
                            ⟨requirement.predicate, goalMem, rfl⟩))
    | implementation evidence =>
        exact valid.implementationRequirements requirement evidence member
          evidenceEq

theorem RequirementValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {id : RequirementId}
    (valid : ContextSubstitutionValid substitution context)
    (requirement : RequirementValid context id) :
    RequirementValid (applyContext substitution context) id := by
  rcases requirement with ⟨predicate, proves⟩
  exact ⟨ProgramPredicate.applyParameters substitution predicate,
    StructuralSubstitution.RequirementProves.applyParameters valid proves⟩

theorem RequirementIdsValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {ids : List RequirementId}
    (valid : ContextSubstitutionValid substitution context)
    (requirements : RequirementIdsValid context ids) :
    RequirementIdsValid (applyContext substitution context) ids := by
  intro id member
  exact StructuralSubstitution.RequirementValid.applyParameters valid
    (requirements id member)

theorem RequirementSequenceProves.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {ids : List RequirementId} {predicates : List ProgramPredicate}
    (valid : ContextSubstitutionValid substitution context)
    (proves : RequirementSequenceProves context ids predicates) :
    RequirementSequenceProves (applyContext substitution context) ids
      (predicates.map (ProgramPredicate.applyParameters substitution)) := by
  induction proves with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (StructuralSubstitution.RequirementProves.applyParameters valid head)
        induction

theorem DeclarationInstantiation.Valid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instantiation : DeclarationInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : SourceSemantics.DeclarationInstantiation.Valid context
      instantiation) :
    SourceSemantics.DeclarationInstantiation.Valid
      (applyContext substitution context)
      (applyDeclarationInstantiation substitution instantiation) := by
  cases valid with
  | intro signature signatureMem declarationEq innerExact innerRange typeEq
      predicatesEq parameterComptimeEq returnComptimeEq =>
      have signatureWellFormed := catalog.functions_semantic signature signatureMem
      let signatureTypingContext := signatureContext context.signatures
        signature.id signature.scheme.parameters signature.scheme.predicates
      have schemeScoped : TypeWellScoped signatureTypingContext []
          signature.scheme.body := by
        rw [signatureWellFormed.scheme_body]
        exact .function
          (StructuralSubstitution.TypesWellScoped.productMany
            (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
              signatureWellFormed.parameter_types))
          (StructuralSubstitution.TypesWellScoped.productMany
            (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
              signatureWellFormed.return_types))
      refine .intro signature (by simpa [applyContext] using signatureMem)
        declarationEq ?_ ?_ ?_ ?_ parameterComptimeEq returnComptimeEq
      · simpa [applyDeclarationInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.Exact.mapRange
            substitution innerExact)
      · simpa [applyDeclarationInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.RangeWellFormed.mapRange
            contextValid.exact contextValid.range innerRange)
      · change substitution.apply instantiation.type =
          (ParameterSubstitution.mapRange substitution
            instantiation.parameterSubstitution).apply signature.scheme.body
        rw [typeEq]
        exact StructuralSubstitution.TypeWellScoped.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          schemeScoped
      · change instantiation.predicates.map
            (ProgramPredicate.applyParameters substitution) =
          signature.scheme.predicates.map
            (ProgramPredicate.applyParameters
              (ParameterSubstitution.mapRange substitution
                instantiation.parameterSubstitution))
        rw [predicatesEq]
        exact StructuralSubstitution.PredicatesWellFormed.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          signatureWellFormed.predicates

theorem DeclarationInstantiation.Admissible.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instantiation : DeclarationInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : SourceSemantics.DeclarationInstantiation.Admissible context
      instantiation) :
    SourceSemantics.DeclarationInstantiation.Admissible
      (applyContext substitution context)
      (applyDeclarationInstantiation substitution instantiation) := by
  cases valid with
  | intro signature signatureMem declarationEq innerExact innerRange typeEq
      predicatesEq parameterComptimeEq returnComptimeEq =>
      have signatureWellFormed := catalog.functions_semantic signature signatureMem
      let signatureTypingContext := signatureContext context.signatures
        signature.id signature.scheme.parameters signature.scheme.predicates
      have schemeScoped : TypeWellScoped signatureTypingContext []
          signature.scheme.body := by
        rw [signatureWellFormed.scheme_body]
        exact .function
          (StructuralSubstitution.TypesWellScoped.productMany
            (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
              signatureWellFormed.parameter_types))
          (StructuralSubstitution.TypesWellScoped.productMany
            (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
              signatureWellFormed.return_types))
      refine .intro signature (by simpa [applyContext] using signatureMem)
        declarationEq ?_ ?_ ?_ ?_ parameterComptimeEq returnComptimeEq
      · simpa [applyDeclarationInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.Exact.mapRange
            substitution innerExact)
      · simpa [applyDeclarationInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.RangeAdmissible.mapRange
            contextValid.exact contextValid.range innerRange)
      · change substitution.apply instantiation.type =
          (ParameterSubstitution.mapRange substitution
            instantiation.parameterSubstitution).apply signature.scheme.body
        rw [typeEq]
        exact StructuralSubstitution.TypeWellScoped.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          schemeScoped
      · change instantiation.predicates.map
            (ProgramPredicate.applyParameters substitution) =
          signature.scheme.predicates.map
            (ProgramPredicate.applyParameters
              (ParameterSubstitution.mapRange substitution
                instantiation.parameterSubstitution))
        rw [predicatesEq]
        exact StructuralSubstitution.PredicatesWellFormed.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          signatureWellFormed.predicates

theorem ParameterSubstitution.orderedArguments_mapRange
    {inner outer : ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact inner parameters) :
    SourceSemantics.ParameterSubstitution.orderedArguments
        (ParameterSubstitution.mapRange outer inner) parameters =
      (SourceSemantics.ParameterSubstitution.orderedArguments inner parameters).map
        outer.apply := by
  unfold SourceSemantics.ParameterSubstitution.orderedArguments
  rw [List.map_map]
  apply List.map_congr_left
  intro parameter member
  obtain ⟨replacement, pairMember, innerLookup⟩ :=
    ParameterSubstitution.exists_lookup?_eq_some exact member
  have mappedMember :
      (parameter, outer.apply replacement) ∈
        ParameterSubstitution.mapRange outer inner :=
    List.mem_map.mpr ⟨(parameter, replacement), pairMember, rfl⟩
  have mappedLookup :=
    ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
      (StructuralSubstitution.ParameterSubstitution.Exact.mapRange outer
        exact).domain_nodup mappedMember
  simp [innerLookup, mappedLookup]

theorem DataConstructorInstantiation.Valid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instantiation : DataConstructorInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context
      instantiation) :
    SourceSemantics.DataConstructorInstantiation.Valid
      (applyContext substitution context)
      (applyDataConstructorInstantiation substitution instantiation) := by
  cases valid with
  | intro dataType constructor dataTypeMem constructorMem constructorOwner
      constructorEq innerExact innerRange payloadTypesEq resultTypeEq =>
      have dataWellFormed := catalog.data_semantic dataType dataTypeMem
      have payloadWellFormed := dataWellFormed.constructor_payloads constructor
        constructorMem
      refine .intro dataType constructor (by simpa [applyContext] using dataTypeMem)
        constructorMem constructorOwner constructorEq ?_ ?_ ?_ ?_
      · simpa [applyDataConstructorInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.Exact.mapRange
            substitution innerExact)
      · simpa [applyDataConstructorInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.RangeWellFormed.mapRange
            contextValid.exact contextValid.range innerRange)
      · change instantiation.payloadTypes.map substitution.apply =
          constructor.payloadTypes.map
            (ParameterSubstitution.mapRange substitution
              instantiation.parameterSubstitution).apply
        rw [payloadTypesEq]
        exact StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          payloadWellFormed
      · change substitution.apply instantiation.resultType =
          Ty.nominal dataType.id
            (SourceSemantics.ParameterSubstitution.orderedArguments
              (ParameterSubstitution.mapRange substitution
                instantiation.parameterSubstitution) dataType.parameters)
        rw [resultTypeEq, apply_nominal,
          StructuralSubstitution.ParameterSubstitution.orderedArguments_mapRange
            innerExact]

theorem DataConstructorInstantiation.Admissible.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instantiation : DataConstructorInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : SourceSemantics.DataConstructorInstantiation.Admissible context
      instantiation) :
    SourceSemantics.DataConstructorInstantiation.Admissible
      (applyContext substitution context)
      (applyDataConstructorInstantiation substitution instantiation) := by
  cases valid with
  | intro dataType constructor dataTypeMem constructorMem constructorOwner
      constructorEq innerExact innerRange payloadTypesEq resultTypeEq =>
      have dataWellFormed := catalog.data_semantic dataType dataTypeMem
      have payloadWellFormed := dataWellFormed.constructor_payloads constructor
        constructorMem
      refine .intro dataType constructor (by simpa [applyContext] using dataTypeMem)
        constructorMem constructorOwner constructorEq ?_ ?_ ?_ ?_
      · simpa [applyDataConstructorInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.Exact.mapRange
            substitution innerExact)
      · simpa [applyDataConstructorInstantiation,
          ParameterSubstitution.mapRange] using
          (StructuralSubstitution.ParameterSubstitution.RangeAdmissible.mapRange
            contextValid.exact contextValid.range innerRange)
      · change instantiation.payloadTypes.map substitution.apply =
          constructor.payloadTypes.map
            (ParameterSubstitution.mapRange substitution
              instantiation.parameterSubstitution).apply
        rw [payloadTypesEq]
        exact StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution instantiation.parameterSubstitution innerExact
          payloadWellFormed
      · change substitution.apply instantiation.resultType =
          Ty.nominal dataType.id
            (SourceSemantics.ParameterSubstitution.orderedArguments
              (ParameterSubstitution.mapRange substitution
                instantiation.parameterSubstitution) dataType.parameters)
        rw [resultTypeEq, apply_nominal,
          StructuralSubstitution.ParameterSubstitution.orderedArguments_mapRange
            innerExact]

theorem ContainsExpression.applyParameters
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (substitution : ParameterSubstitution)
    (contains : ContainsExpression source id node) :
    ContainsExpression (applyTypedSource substitution source) id
      (applyExpressionNode substitution node) := by
  rcases contains with ⟨member, idEq⟩
  refine ⟨?_, idEq⟩
  exact List.mem_map.mpr ⟨Node.expression node, member, rfl⟩

theorem ContainsStatement.applyParameters
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    (substitution : ParameterSubstitution)
    (contains : ContainsStatement source id node) :
    ContainsStatement (applyTypedSource substitution source) id
      (applyStatementNode substitution node) := by
  rcases contains with ⟨member, idEq⟩
  refine ⟨?_, idEq⟩
  exact List.mem_map.mpr ⟨Node.statement node, member, rfl⟩

@[simp] theorem applyExpressionNode_rawType
    (substitution : ParameterSubstitution) (node : ExpressionNode) :
    (applyExpressionNode substitution node).rawType =
      substitution.apply node.rawType := by
  cases coercionsEq : node.coercions with
  | nil => simp [ExpressionNode.rawType, applyExpressionNode, coercionsEq]
  | cons head tail =>
      simp [ExpressionNode.rawType, applyExpressionNode, coercionsEq,
        applyCoercionStep]

@[simp] theorem applyCoercionStep_requirements
    (substitution : ParameterSubstitution) (step : CoercionStep) :
    (applyCoercionStep substitution step).requirements = step.requirements := by
  rfl

@[simp] theorem coercionRequirementIds_applyCoercionSteps
    (substitution : ParameterSubstitution) (steps : List CoercionStep) :
    coercionRequirementIds (steps.map (applyCoercionStep substitution)) =
      coercionRequirementIds steps := by
  induction steps with
  | nil => rfl
  | cons head tail induction =>
      change head.requirements ++
          coercionRequirementIds
            (tail.map (applyCoercionStep substitution)) =
        head.requirements ++ coercionRequirementIds tail
      rw [induction]

theorem IntegerLiteralValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : IntegerLiteralValid context literal resolution) :
    IntegerLiteralValid (applyContext substitution context) literal
      (applyIntegerLiteralResolution substitution resolution) := by
  cases valid with
  | word meaning targetEq evidence =>
      refine .word meaning ?_ ?_
      · simp [applyIntegerLiteralResolution, targetEq]
      · simpa [applyIntegerLiteralResolution,
          ProgramSignatures.builtinIntPredicate,
          ProgramPredicate.applyParameters] using
          (StructuralSubstitution.RequirementProves.applyParameters contextValid
            evidence)
  | integer meaning targetEq evidence =>
      refine .integer meaning ?_ ?_
      · simp [applyIntegerLiteralResolution, targetEq]
      · simpa [applyIntegerLiteralResolution,
          ProgramSignatures.builtinIntPredicate,
          ProgramPredicate.applyParameters] using
          (StructuralSubstitution.RequirementProves.applyParameters contextValid
            evidence)

theorem ReferenceHasRawType.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {resolution : ReferenceResolution} {type : Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : ReferenceHasRawType context resolution type) :
    ReferenceHasRawType (applyContext substitution context)
      (applyReferenceResolution substitution resolution)
      (substitution.apply type) := by
  cases typing with
  | «local» lookup instantiates =>
      exact .local
        (StructuralSubstitution.LocalLookup.applyParameters substitution lookup)
        (StructuralSubstitution.SchemeInstantiatesAt.applyParameters substitution
          contextValid.exact contextValid.range instantiates)
  | declaration valid =>
      exact .declaration
        (StructuralSubstitution.DeclarationInstantiation.Admissible.applyParameters
          catalog contextValid valid)
  | builtinFunction function =>
      cases function <;> simp [applyReferenceResolution,
        BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes,
        BuiltinFunctionId.returnType] <;> exact .builtinFunction _
  | builtinBoolean value =>
      simpa [applyReferenceResolution] using
        (ReferenceHasRawType.builtinBoolean
          (context := applyContext substitution context) value)

theorem CoercionProfileInstantiates.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {source target : Ty} {primary : ProgramPredicate}
    {methodPredicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (profile : CoercionProfileInstantiates context source target primary
      methodPredicates) :
    CoercionProfileInstantiates (applyContext substitution context)
      (substitution.apply source) (substitution.apply target)
      (ProgramPredicate.applyParameters substitution primary)
      (methodPredicates.map
        (ProgramPredicate.applyParameters substitution)) := by
  cases profile with
  | @intro signature method fromParameter toParameter signatureMem nameEq
      parametersEq methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter (fun candidate => candidate.name == "coerce") := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(fromParameter, source), (toParameter, target)]
          signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(fromParameter, source), (toParameter, target)]
          innerExact methodWellFormed.parameter_types
      have returnCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(fromParameter, source), (toParameter, target)]
          innerExact methodWellFormed.return_types
      have predicateCompose :=
        StructuralSubstitution.PredicatesWellFormed.applyParameters_compose
          substitution [(fromParameter, source), (toParameter, target)]
          innerExact methodWellFormed.predicates
      rw [predicateCompose]
      exact .intro
        (by simpa [applyContext] using signatureMem) nameEq parametersEq
        methodUnique (by
          change method.parameterTypes.map
            (ParameterSubstitution.mapRange substitution
              [(fromParameter, source), (toParameter, target)]).apply =
          [substitution.apply source]
          rw [← parameterCompose, parameterTypesEq]
          rfl)
        (by
          change method.returnTypes.map
            (ParameterSubstitution.mapRange substitution
              [(fromParameter, source), (toParameter, target)]).apply =
          [substitution.apply target]
          rw [← returnCompose, returnTypesEq]
          rfl)

theorem CoercionStepValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {step : CoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : CoercionStepValid context step) :
    CoercionStepValid (applyContext substitution context)
      (applyCoercionStep substitution step) := by
  cases valid with
  | intro profile requirements =>
      exact .intro
        (StructuralSubstitution.CoercionProfileInstantiates.applyParameters
          catalog profile)
        (by simpa [applyCoercionStep] using
          (StructuralSubstitution.RequirementSequenceProves.applyParameters
            contextValid requirements))

theorem CoercionPathValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {source target : Ty} {steps : List CoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : CoercionPathValid context source target steps) :
    CoercionPathValid (applyContext substitution context)
      (substitution.apply source) (substitution.apply target)
      (steps.map (applyCoercionStep substitution)) := by
  induction valid with
  | nil type => exact .nil _
  | cons head tail induction =>
      exact .cons
        (StructuralSubstitution.CoercionStepValid.applyParameters
          catalog contextValid head)
        induction

theorem OperatorProfileInstantiates.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {traitName methodName : String} {operand : Ty}
    {parameterTypes returnTypes : List Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (profile : OperatorProfileInstantiates context traitName methodName operand
      parameterTypes returnTypes predicates) :
    OperatorProfileInstantiates (applyContext substitution context)
      traitName methodName (substitution.apply operand)
      (parameterTypes.map substitution.apply)
      (returnTypes.map substitution.apply)
      (predicates.map (ProgramPredicate.applyParameters substitution)) := by
  cases profile with
  | @intro signature method parameter signatureMem traitNameEq parametersEq
      methodUnique parameterTypesEq returnTypesEq =>
      have signatureWellFormed := catalog.traits_semantic signature signatureMem
      have methodFiltered : method ∈
          signature.methods.filter
            (fun candidate => candidate.name == methodName) := by
        rw [methodUnique]
        simp
      have methodMem : method ∈ signature.methods :=
        (List.mem_filter.mp methodFiltered).1
      have methodWellFormed := signatureWellFormed.methods method methodMem
      have innerExact : SourceSemantics.ParameterSubstitution.Exact
          [(parameter, operand)] signature.parameters := by
        constructor
        · exact signatureWellFormed.parameters_nodup
        · rw [parametersEq]
          simp [SourceSemantics.ParameterSubstitution.domain]
      have parameterCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(parameter, operand)] innerExact
          methodWellFormed.parameter_types
      have returnCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution [(parameter, operand)] innerExact
          methodWellFormed.return_types
      have predicateCompose :=
        StructuralSubstitution.PredicatesWellFormed.applyParameters_compose
          substitution [(parameter, operand)] innerExact
          methodWellFormed.predicates
      change OperatorProfileInstantiates (applyContext substitution context)
        traitName methodName (substitution.apply operand)
        (parameterTypes.map substitution.apply)
        (returnTypes.map substitution.apply)
        ({ trait := .declaration signature.id
           subject := substitution.apply operand
           arguments := [] } ::
          (method.wherePredicates.map
            (ProgramPredicate.applyParameters [(parameter, operand)])).map
              (ProgramPredicate.applyParameters substitution))
      rw [predicateCompose]
      exact .intro (by simpa [applyContext] using signatureMem) traitNameEq
        parametersEq methodUnique
        (by
          change method.parameterTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            parameterTypes.map substitution.apply
          rw [← parameterCompose, parameterTypesEq])
        (by
          change method.returnTypes.map
              (ParameterSubstitution.mapRange substitution
                [(parameter, operand)]).apply =
            returnTypes.map substitution.apply
          rw [← returnCompose, returnTypesEq])

theorem UnaryOperatorHasType.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {operator : Syntax.UnaryOp} {operand result : Ty}
    {requirements : List RequirementId}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : UnaryOperatorHasType context operator operand result requirements) :
    UnaryOperatorHasType (applyContext substitution context) operator
      (substitution.apply operand) (substitution.apply result) requirements := by
  cases typing with
  | logicalNot => exact .logicalNot
  | wordBitNot => exact .wordBitNot
  | integerBitNot => exact .integerBitNot
  | trait dispatch profile evidence =>
      exact .trait dispatch
        (StructuralSubstitution.OperatorProfileInstantiates.applyParameters
          catalog profile)
        (StructuralSubstitution.RequirementSequenceProves.applyParameters
          contextValid evidence)

theorem BinaryOperatorHasType.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {operator : Syntax.BinaryOp} {left right result : Ty}
    {requirements : List RequirementId}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : BinaryOperatorHasType context operator left right result
      requirements) :
    BinaryOperatorHasType (applyContext substitution context) operator
      (substitution.apply left) (substitution.apply right)
      (substitution.apply result) requirements := by
  cases typing with
  | wordArithmetic kind => exact .wordArithmetic kind
  | integerArithmetic kind => exact .integerArithmetic kind
  | wordComparison kind => exact .wordComparison kind
  | integerComparison kind => exact .integerComparison kind
  | booleanAnd => exact .booleanAnd
  | booleanOr => exact .booleanOr
  | trait dispatch profile evidence =>
      exact .trait dispatch
        (StructuralSubstitution.OperatorProfileInstantiates.applyParameters
          catalog profile)
        (StructuralSubstitution.RequirementSequenceProves.applyParameters
          contextValid evidence)

theorem DeclarationApplicationValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instantiation : DeclarationInstantiation}
    {parameterTypes : List Ty} {resultType : Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : DeclarationApplicationValid context instantiation parameterTypes
      resultType predicates) :
    DeclarationApplicationValid (applyContext substitution context)
      (applyDeclarationInstantiation substitution instantiation)
      (parameterTypes.map substitution.apply) (substitution.apply resultType)
      (predicates.map (ProgramPredicate.applyParameters substitution)) := by
  cases valid with
  | intro signatureMem instantiationValid declarationEq
      parameterTypesEq resultTypeEq functionTypeEq predicatesEq =>
      rename_i signature
      cases instantiationValid with
      | intro selectedSignature selectedMem selectedDeclarationEq innerExact
          innerRange instantiationTypeEq instantiationPredicatesEq
          parameterComptimeEq returnComptimeEq =>
      have selectedEq : selectedSignature = signature :=
        eq_of_mem_of_mapped_nodup catalog.function_ids selectedMem signatureMem
          (by rw [← selectedDeclarationEq, declarationEq])
      subst selectedSignature
      have instantiationValid :
          SourceSemantics.DeclarationInstantiation.Admissible context
            instantiation :=
        .intro signature selectedMem selectedDeclarationEq innerExact innerRange
          instantiationTypeEq instantiationPredicatesEq parameterComptimeEq
          returnComptimeEq
      have signatureWellFormed := catalog.functions_semantic signature signatureMem
      have parameterCompose :=
        StructuralSubstitution.TypesWellFormed.applyParameters_compose
          substitution instantiation.parameterSubstitution
          innerExact signatureWellFormed.parameter_types
      have resultScoped :=
        StructuralSubstitution.TypesWellScoped.productMany
          (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
            signatureWellFormed.return_types)
      have resultCompose :=
        StructuralSubstitution.TypeWellScoped.applyParameters_compose
          substitution instantiation.parameterSubstitution
          innerExact resultScoped
      exact .intro (by simpa [applyContext] using signatureMem)
        (StructuralSubstitution.DeclarationInstantiation.Admissible.applyParameters
          catalog contextValid instantiationValid)
        declarationEq
        (by
          change signature.parameterTypes.map
              (ParameterSubstitution.mapRange substitution
                instantiation.parameterSubstitution).apply =
            parameterTypes.map substitution.apply
          rw [← parameterCompose, parameterTypesEq])
        (by
          change (ParameterSubstitution.mapRange substitution
              instantiation.parameterSubstitution).apply
              (Ty.productMany signature.returnTypes) =
            substitution.apply resultType
          rw [← resultCompose, resultTypeEq])
        (by
          simp [applyDeclarationInstantiation, functionTypeEq,
            StructuralSubstitution.apply_productMany])
        (by simp [applyDeclarationInstantiation, predicatesEq])

theorem DirectDeclarationCalleeValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {source : TypedSource} {callee : ExpressionId}
    {instantiation : DeclarationInstantiation}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : DirectDeclarationCalleeValid context source callee instantiation) :
    DirectDeclarationCalleeValid (applyContext substitution context)
      (applyTypedSource substitution source) callee
      (applyDeclarationInstantiation substitution instantiation) := by
  cases valid with
  | @intro node name _ hContains hForm hInstantiation hType hRequirements
      hCoercions =>
      exact .intro
        (StructuralSubstitution.ContainsExpression.applyParameters substitution
          hContains)
        (by
          change applyExpressionForm substitution node.form =
            .reference name
              (.declaration
                (applyDeclarationInstantiation substitution instantiation))
          rw [hForm]
          rfl)
        (StructuralSubstitution.DeclarationInstantiation.Admissible.applyParameters
          catalog contextValid hInstantiation)
        (by simp [applyExpressionNode, applyDeclarationInstantiation, hType])
        (by simp [applyExpressionNode, hRequirements])
        (by simp [applyExpressionNode, hCoercions])

theorem DirectBuiltinCalleeValid.applyParameters
    {substitution : ParameterSubstitution} {source : TypedSource}
    {callee : ExpressionId} {function : BuiltinFunctionId}
    (valid : DirectBuiltinCalleeValid source callee function) :
    DirectBuiltinCalleeValid (applyTypedSource substitution source) callee
      function := by
  cases valid with
  | @intro node name _ hContains hForm hType hRequirements hCoercions =>
      refine .intro
        (StructuralSubstitution.ContainsExpression.applyParameters substitution
          hContains)
        (by
          change applyExpressionForm substitution node.form =
            .reference name (.builtinFunction function)
          rw [hForm]
          rfl) ?_
        (by simp [applyExpressionNode, hRequirements])
        (by simp [applyExpressionNode, hCoercions])
      change substitution.apply node.type = function.type
      rw [hType]
      unfold BuiltinFunctionId.type
      rw [StructuralSubstitution.apply_function,
        StructuralSubstitution.apply_productMany]
      cases function <;> rfl

theorem DirectCallRequirementsValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {rawResult finalResult : Ty} {predicates : List ProgramPredicate}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : DirectCallRequirementsValid context rawResult finalResult
      predicates requirements coercions) :
    DirectCallRequirementsValid (applyContext substitution context)
      (substitution.apply rawResult) (substitution.apply finalResult)
      (predicates.map (ProgramPredicate.applyParameters substitution))
      requirements (coercions.map (applyCoercionStep substitution)) := by
  cases valid with
  | @intro selectedResult contextual selectedPath contextualPath
      signatureRequirements requirements coercions selectedValid contextualValid
      signatureValid coercionsEq requirementsEq =>
      exact .intro (contextual := substitution.apply contextual)
        (StructuralSubstitution.CoercionPathValid.applyParameters catalog
          contextValid selectedValid)
        (StructuralSubstitution.CoercionPathValid.applyParameters catalog
          contextValid contextualValid)
        (StructuralSubstitution.RequirementSequenceProves.applyParameters
          contextValid signatureValid)
        (by simp [coercionsEq, List.map_append])
        (by
          simp [requirementsEq,
            StructuralSubstitution.coercionRequirementIds_applyCoercionSteps])

theorem IndirectApplicationValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {metadata : IndirectCallResolution} {argumentTypes : List Ty}
    {parameterType : Ty}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : IndirectApplicationValid context metadata argumentTypes
      parameterType) :
    IndirectApplicationValid (applyContext substitution context)
      (applyIndirectCallResolution substitution metadata)
      (argumentTypes.map substitution.apply)
      (substitution.apply parameterType) := by
  cases valid with
  | intro countEq beforeEq afterEq pathValid =>
      exact .intro
        (by simp [applyIndirectCallResolution, countEq])
        (by simp [applyIndirectCallResolution, beforeEq,
          StructuralSubstitution.apply_productMany])
        (by simp [applyIndirectCallResolution, afterEq])
        (by
          change CoercionPathValid (applyContext substitution context)
            (substitution.apply metadata.argumentTypeBeforeCoercion)
            (substitution.apply parameterType)
            (metadata.argumentCoercions.map
              (applyCoercionStep substitution))
          exact StructuralSubstitution.CoercionPathValid.applyParameters catalog
            contextValid pathValid)

theorem TypeWellScoped.applyParameters_eq_of_orderedArguments_eq
    {context : Context} {flexibleVariables : List TypeVarId} {type : Ty}
    (left right : ParameterSubstitution)
    (leftExact : SourceSemantics.ParameterSubstitution.Exact left
      context.typeParameters)
    (rightExact : SourceSemantics.ParameterSubstitution.Exact right
      context.typeParameters)
    (argumentsEq : SourceSemantics.ParameterSubstitution.orderedArguments left
        context.typeParameters =
      SourceSemantics.ParameterSubstitution.orderedArguments right
        context.typeParameters)
    (wellScoped : TypeWellScoped context flexibleVariables type) :
    left.apply type = right.apply type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => left.apply type = right.apply type)
    (motive_2 := fun types _ =>
      types.map left.apply = types.map right.apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    rfl
  · intro parameter bound owned
    have pointwise := List.map_inj_left.mp argumentsEq parameter bound
    obtain ⟨leftReplacement, leftMember, leftLookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some leftExact bound
    obtain ⟨rightReplacement, rightMember, rightLookup⟩ :=
      ParameterSubstitution.exists_lookup?_eq_some rightExact bound
    simpa [SourceSemantics.ParameterSubstitution.orderedArguments,
      leftLookup, rightLookup, TypeSystem.ParameterSubstitution.apply] using
      pointwise
  · intro builtin
    rfl
  · intro dataType arguments cataloged arity argumentsWellScoped induction
    rw [StructuralSubstitution.apply_nominal,
      StructuralSubstitution.apply_nominal, induction]
  · intro parameter result parameterWellScoped resultWellScoped
      parameterInduction resultInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro leftType rightType leftWellScoped rightWellScoped leftInduction
      rightInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value keyWellScoped valueWellScoped keyInduction valueInduction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro inner wellScoped induction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [induction]
  · intro inner wellScoped induction
    simp only [TypeSystem.ParameterSubstitution.apply]
    rw [induction]
  · rfl
  · intro head tail headWellScoped tailWellScoped headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

private def substitutionApplicationHead : Ty → Ty
  | .application function _ => substitutionApplicationHead function
  | type => type

private def substitutionApplicationArguments : Ty → List Ty
  | .application function argument =>
      substitutionApplicationArguments function ++ [argument]
  | _ => []

private theorem substitutionApplicationHead_applyMany
    (head : Ty) (arguments : List Ty) :
    substitutionApplicationHead (Ty.applyMany head arguments) =
      substitutionApplicationHead head := by
  unfold Ty.applyMany
  induction arguments generalizing head with
  | nil => rfl
  | cons argument arguments induction =>
      simp only [List.foldl_cons]
      rw [induction]
      rfl

private theorem substitutionApplicationArguments_applyMany
    (head : Ty) (arguments : List Ty) :
    substitutionApplicationArguments (Ty.applyMany head arguments) =
      substitutionApplicationArguments head ++ arguments := by
  unfold Ty.applyMany
  induction arguments generalizing head with
  | nil => simp
  | cons argument arguments induction =>
      simp only [List.foldl_cons]
      rw [induction]
      simp [substitutionApplicationArguments, List.append_assoc]

private theorem nominal_injective
    {leftDeclaration rightDeclaration : Resolved.DeclarationId}
    {leftArguments rightArguments : List Ty}
    (equal : Ty.nominal leftDeclaration leftArguments =
      Ty.nominal rightDeclaration rightArguments) :
    leftDeclaration = rightDeclaration ∧ leftArguments = rightArguments := by
  constructor
  · have heads := congrArg substitutionApplicationHead equal
    simpa [Ty.nominal,
      substitutionApplicationHead_applyMany,
      substitutionApplicationHead] using heads
  · have arguments := congrArg substitutionApplicationArguments equal
    simpa [Ty.nominal,
      substitutionApplicationArguments_applyMany,
      substitutionApplicationArguments] using arguments

theorem WritableLocal.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {id : Resolved.LocalId} {type : Ty}
    (contextValid : ContextSubstitutionValid substitution context)
    (writable : WritableLocal context id type) :
    WritableLocal (applyContext substitution context) id
      (substitution.apply type) := by
  cases writable with
  | intro lookup schemeWellFormed quantifiedEq bodyEq =>
      exact .intro
        (StructuralSubstitution.LocalLookup.applyParameters substitution lookup)
        (StructuralSubstitution.SchemeWellFormed.applyParameters substitution
          contextValid.exact contextValid.range schemeWellFormed)
        (by simp [applyScheme, quantifiedEq])
        (by simp [applyScheme, bodyEq])

theorem UniformMemberProjection.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {base member : Ty} {index : Nat}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (projection : UniformMemberProjection context base index member) :
    UniformMemberProjection (applyContext substitution context)
      (substitution.apply base) index (substitution.apply member) := by
  cases projection with
  | intro dataTypeMem innerExact baseEq baseWellFormed memberWellFormed
      constructorsNonempty memberUniform validInstantiations =>
      rename_i dataType inner
      have dataWellFormed := catalog.data_semantic dataType dataTypeMem
      have mappedExact :=
        StructuralSubstitution.ParameterSubstitution.Exact.mapRange
          substitution innerExact
      have mappedUniform : ∀ constructor,
          constructor ∈ dataType.constructors →
          (constructor.payloadTypes.map
            (ParameterSubstitution.mapRange substitution inner).apply)[index]? =
              some (substitution.apply member) := by
        intro constructor constructorMem
        have payloadWellFormed :=
          dataWellFormed.constructor_payloads constructor constructorMem
        have compose :=
          StructuralSubstitution.TypesWellFormed.applyParameters_compose
            substitution inner innerExact payloadWellFormed
        rw [← compose, List.getElem?_map, memberUniform constructor constructorMem]
        rfl
      exact .intro (by simpa [applyContext] using dataTypeMem) mappedExact
        (by
          rw [baseEq, StructuralSubstitution.apply_nominal,
            StructuralSubstitution.ParameterSubstitution.orderedArguments_mapRange
              innerExact])
        (StructuralSubstitution.TypeAdmissible.applyParameters substitution
          contextValid.exact contextValid.range baseWellFormed)
        (StructuralSubstitution.TypeAdmissible.applyParameters substitution
          contextValid.exact contextValid.range memberWellFormed)
        constructorsNonempty mappedUniform
        (by
          intro instantiation instantiationValid resultEq
          cases instantiationValid with
          | intro instantiatedData constructor instantiatedDataMem constructorMem
              constructorOwner constructorEq instantiatedExact instantiatedRange
              payloadTypesEq resultTypeEq =>
              have nominalEq :
                  Ty.nominal instantiatedData.id
                      (SourceSemantics.ParameterSubstitution.orderedArguments
                        instantiation.parameterSubstitution
                        instantiatedData.parameters) =
                    Ty.nominal dataType.id
                      (SourceSemantics.ParameterSubstitution.orderedArguments
                        (ParameterSubstitution.mapRange substitution inner)
                        dataType.parameters) := by
                rw [← resultTypeEq, resultEq, baseEq,
                  StructuralSubstitution.apply_nominal,
                  StructuralSubstitution.ParameterSubstitution.orderedArguments_mapRange
                    innerExact]
              have nominalParts := nominal_injective nominalEq
              have dataEq : instantiatedData = dataType :=
                eq_of_mem_of_mapped_nodup catalog.data_ids instantiatedDataMem
                  dataTypeMem nominalParts.1
              subst instantiatedData
              have payloadWellFormed :=
                dataWellFormed.constructor_payloads constructor constructorMem
              have payloadMapsEq :
                  constructor.payloadTypes.map
                      instantiation.parameterSubstitution.apply =
                    constructor.payloadTypes.map
                      (ParameterSubstitution.mapRange substitution inner).apply := by
                apply List.map_congr_left
                intro payload payloadMem
                exact StructuralSubstitution.TypeWellScoped.applyParameters_eq_of_orderedArguments_eq
                    instantiation.parameterSubstitution
                    (ParameterSubstitution.mapRange substitution inner)
                    instantiatedExact mappedExact nominalParts.2
                    (payloadWellFormed payload payloadMem).typeWellScoped
              rw [payloadTypesEq, payloadMapsEq]
              exact mappedUniform constructor constructorMem)

theorem PatternBinderValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {type : Ty} {binder : TypedBinder}
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : PatternBinderValid context type binder) :
    PatternBinderValid (applyContext substitution context)
      (substitution.apply type) (applyBinder substitution binder) := by
  refine ⟨?_, valid.runtime, ?_⟩
  · simp [applyBinder, applyScheme, valid.scheme_eq, Scheme.mono]
  · intro declaration declarationEq
    have original := valid.wellFormed declaration
      (by simpa [applyContext] using declarationEq)
    exact {
      owned := original.owned
      scheme := StructuralSubstitution.SchemeWellFormed.applyParameters
        substitution contextValid.exact contextValid.range original.scheme
      quantified_fresh := by
        intro metavariable quantified
        simp [applyBinder, applyScheme, valid.scheme_eq, Scheme.mono] at quantified
      monomorphic_requirements_empty := by
        intro quantifiedEmpty
        have originalQuantifiedEmpty : binder.scheme.quantified = [] := by
          simpa [applyBinder, applyScheme] using quantifiedEmpty
        simp [applyBinder, original.monomorphic_requirements_empty
          originalQuantifiedEmpty]
    }

theorem PatternBindersDistinct.applyParameters
    {substitution : ParameterSubstitution} {binders : List TypedBinder}
    (distinct : PatternBindersDistinct binders) :
    PatternBindersDistinct (binders.map (applyBinder substitution)) := by
  constructor
  · simpa [List.map_map, Function.comp_def, applyBinder] using distinct.ids
  · simpa [List.map_map, Function.comp_def, applyBinder] using distinct.names

theorem PatternInstructionHasType.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instructions rest : List MatchPatternInstruction} {type : Ty}
    {requirements : List RequirementId} {binders : List TypedBinder}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : PatternInstructionHasType context instructions type requirements
      binders rest) :
    PatternInstructionHasType (applyContext substitution context)
      (instructions.map (applyMatchPatternInstruction substitution))
      (substitution.apply type) requirements
      (binders.map (applyBinder substitution))
      (rest.map (applyMatchPatternInstruction substitution)) := by
  refine PatternInstructionHasType.rec
    (motive_1 := fun instructions type requirements binders rest _ =>
      PatternInstructionHasType (applyContext substitution context)
        (instructions.map (applyMatchPatternInstruction substitution))
        (substitution.apply type) requirements
        (binders.map (applyBinder substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    (motive_2 := fun instructions types requirements binders rest _ =>
      PatternInstructionsHaveTypes (applyContext substitution context)
        (instructions.map (applyMatchPatternInstruction substitution))
        (types.map substitution.apply) requirements
        (binders.map (applyBinder substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro rest type
    exact .wildcard
  · intro rest source resolution valid
    exact .integerLiteral
      (StructuralSubstitution.IntegerLiteralValid.applyParameters
        contextValid valid)
  · intro rest binder type valid
    exact .binder
      (StructuralSubstitution.PatternBinderValid.applyParameters
        contextValid valid)
  · intro instructions rest instantiation argumentCount requirements binders
      valid arity arguments argumentsInduction
    exact .constructor
      (StructuralSubstitution.DataConstructorInstantiation.Admissible.applyParameters
        catalog contextValid valid)
      (by simp [applyDataConstructorInstantiation, arity])
      argumentsInduction
  · intro instructions rest elementCount elementTypes requirements binders
      arity elements elementsInduction
    simpa [StructuralSubstitution.apply_productMany,
      applyMatchPatternInstruction] using
      (PatternInstructionHasType.tuple
        (context := applyContext substitution context)
        (by simp [arity]) elementsInduction)
  · intro instructions
    exact .nil
  · intro instructions afterHead rest type types headRequirements
      tailRequirements headBinders tailBinders head tail headInduction
      tailInduction
    simpa [List.map_append] using
      (PatternInstructionsHaveTypes.cons headInduction tailInduction)

theorem PatternInstructionsHaveTypes.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {instructions rest : List MatchPatternInstruction} {types : List Ty}
    {requirements : List RequirementId} {binders : List TypedBinder}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : PatternInstructionsHaveTypes context instructions types
      requirements binders rest) :
    PatternInstructionsHaveTypes (applyContext substitution context)
      (instructions.map (applyMatchPatternInstruction substitution))
      (types.map substitution.apply) requirements
      (binders.map (applyBinder substitution))
      (rest.map (applyMatchPatternInstruction substitution)) := by
  refine PatternInstructionsHaveTypes.rec
    (motive_1 := fun instructions type requirements binders rest _ =>
      PatternInstructionHasType (applyContext substitution context)
        (instructions.map (applyMatchPatternInstruction substitution))
        (substitution.apply type) requirements
        (binders.map (applyBinder substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    (motive_2 := fun instructions types requirements binders rest _ =>
      PatternInstructionsHaveTypes (applyContext substitution context)
        (instructions.map (applyMatchPatternInstruction substitution))
        (types.map substitution.apply) requirements
        (binders.map (applyBinder substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ typing
  · intro rest type
    exact .wildcard
  · intro rest source resolution valid
    exact .integerLiteral
      (StructuralSubstitution.IntegerLiteralValid.applyParameters
        contextValid valid)
  · intro rest binder type valid
    exact .binder
      (StructuralSubstitution.PatternBinderValid.applyParameters
        contextValid valid)
  · intro instructions rest instantiation argumentCount requirements binders
      valid arity arguments argumentsInduction
    exact .constructor
      (StructuralSubstitution.DataConstructorInstantiation.Admissible.applyParameters
        catalog contextValid valid)
      (by simp [applyDataConstructorInstantiation, arity])
      argumentsInduction
  · intro instructions rest elementCount elementTypes requirements binders
      arity elements elementsInduction
    simpa [StructuralSubstitution.apply_productMany,
      applyMatchPatternInstruction] using
      (PatternInstructionHasType.tuple
        (context := applyContext substitution context)
        (by simp [arity]) elementsInduction)
  · intro instructions
    exact .nil
  · intro instructions afterHead rest type types headRequirements
      tailRequirements headBinders tailBinders head tail headInduction
      tailInduction
    simpa [List.map_append] using
      (PatternInstructionsHaveTypes.cons headInduction tailInduction)

@[simp] theorem matchPatternResolutionInstructions_applyParameters
    (substitution : ParameterSubstitution)
    (resolution : MatchPatternResolution) (rootArity : Nat) :
    matchPatternResolutionInstructions
        (applyMatchPatternResolution substitution resolution) rootArity =
      (matchPatternResolutionInstructions resolution rootArity).map
        (applyMatchPatternInstruction substitution) := by
  cases resolution <;> simp [applyMatchPatternResolution,
    matchPatternResolutionInstructions, applyMatchPatternInstruction]

theorem ConstructorPatternSpellingValid.applyParameters
    {substitution : ParameterSubstitution} {context : Context} {name : String}
    {instantiation : DataConstructorInstantiation}
    (valid : ConstructorPatternSpellingValid context name instantiation) :
    ConstructorPatternSpellingValid (applyContext substitution context) name
      (applyDataConstructorInstantiation substitution instantiation) := by
  rcases valid with ⟨signature, signatureMem, constructor, constructorMem,
    constructorEq, nameEq⟩
  exact ⟨signature, by simpa [applyContext] using signatureMem,
    constructor, constructorMem, by simpa [applyDataConstructorInstantiation]
      using constructorEq, nameEq⟩

theorem MatchPatternSourceRepresents.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {source : MatchPatternSource} {resolution : MatchPatternResolution}
    {rootArity : Nat}
    (represents : MatchPatternSourceRepresents context source resolution
      rootArity) :
    MatchPatternSourceRepresents (applyContext substitution context) source
      (applyMatchPatternResolution substitution resolution) rootArity := by
  induction represents with
  | wildcard => exact .wildcard
  | integerLiteral sourceEq => exact .integerLiteral sourceEq
  | binder nameEq => exact .binder nameEq
  | constructor spelling =>
      exact .constructor
        (StructuralSubstitution.ConstructorPatternSpellingValid.applyParameters
          spelling)
  | tuple => exact .tuple
  | group inner induction => exact .group induction

theorem PatternInstructionIrrefutable.applyParameters
    {substitution : ParameterSubstitution}
    {instructions rest : List MatchPatternInstruction}
    (irrefutable : PatternInstructionIrrefutable instructions rest) :
    PatternInstructionIrrefutable
      (instructions.map (applyMatchPatternInstruction substitution))
      (rest.map (applyMatchPatternInstruction substitution)) := by
  refine PatternInstructionIrrefutable.rec
    (motive_1 := fun instructions rest _ =>
      PatternInstructionIrrefutable
        (instructions.map (applyMatchPatternInstruction substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    (motive_2 := fun instructions count rest _ =>
      PatternInstructionsIrrefutable
        (instructions.map (applyMatchPatternInstruction substitution)) count
        (rest.map (applyMatchPatternInstruction substitution)))
    ?_ ?_ ?_ ?_ ?_ irrefutable
  · intro rest
    exact .wildcard
  · intro rest binder
    exact .binder
  · intro instructions rest elementCount elements elementsInduction
    exact .tuple elementsInduction
  · intro instructions
    exact .zero
  · intro instructions afterHead rest count head tail headInduction
      tailInduction
    exact .succ headInduction tailInduction

theorem PatternInstructionsIrrefutable.applyParameters
    {substitution : ParameterSubstitution}
    {instructions rest : List MatchPatternInstruction} {count : Nat}
    (irrefutable : PatternInstructionsIrrefutable instructions count rest) :
    PatternInstructionsIrrefutable
      (instructions.map (applyMatchPatternInstruction substitution)) count
      (rest.map (applyMatchPatternInstruction substitution)) := by
  refine PatternInstructionsIrrefutable.rec
    (motive_1 := fun instructions rest _ =>
      PatternInstructionIrrefutable
        (instructions.map (applyMatchPatternInstruction substitution))
        (rest.map (applyMatchPatternInstruction substitution)))
    (motive_2 := fun instructions count rest _ =>
      PatternInstructionsIrrefutable
        (instructions.map (applyMatchPatternInstruction substitution)) count
        (rest.map (applyMatchPatternInstruction substitution)))
    ?_ ?_ ?_ ?_ ?_ irrefutable
  · intro rest
    exact .wildcard
  · intro rest binder
    exact .binder
  · intro instructions rest elementCount elements elementsInduction
    exact .tuple elementsInduction
  · intro instructions
    exact .zero
  · intro instructions afterHead rest count head tail headInduction
      tailInduction
    exact .succ headInduction tailInduction

theorem TypedMatchPatternIrrefutable.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {pattern : TypedMatchPattern}
    (irrefutable : TypedMatchPatternIrrefutable context pattern) :
    TypedMatchPatternIrrefutable (applyContext substitution context)
      (applyTypedMatchPattern substitution pattern) := by
  rcases irrefutable with ⟨rootArity, represents, resolution⟩
  refine ⟨rootArity,
    StructuralSubstitution.MatchPatternSourceRepresents.applyParameters
      represents, ?_⟩
  unfold MatchPatternResolutionIrrefutable at resolution ⊢
  change PatternInstructionIrrefutable
    (matchPatternResolutionInstructions
      (applyMatchPatternResolution substitution pattern.resolution) rootArity) []
  rw [StructuralSubstitution.matchPatternResolutionInstructions_applyParameters]
  exact StructuralSubstitution.PatternInstructionIrrefutable.applyParameters
    resolution

theorem TypedMatchPatternHasType.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {pattern : TypedMatchPattern} {type : Ty}
    {binders : List TypedBinder} {rootArity : Nat}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : TypedMatchPatternHasType context pattern type binders rootArity) :
    TypedMatchPatternHasType (applyContext substitution context)
      (applyTypedMatchPattern substitution pattern) (substitution.apply type)
      (binders.map (applyBinder substitution)) rootArity := by
  refine ⟨by simp [applyTypedMatchPattern, typing.type_eq],
    StructuralSubstitution.MatchPatternSourceRepresents.applyParameters
      typing.source_represents, ?_,
    StructuralSubstitution.PatternBindersDistinct.applyParameters
      typing.binders_distinct⟩
  have resolutionTyping := typing.resolution_type
  unfold MatchPatternResolutionHasType at resolutionTyping ⊢
  change PatternInstructionHasType (applyContext substitution context)
    (matchPatternResolutionInstructions
      (applyMatchPatternResolution substitution pattern.resolution) rootArity)
    (substitution.apply type) pattern.requirements
    (binders.map (applyBinder substitution)) []
  rw [StructuralSubstitution.matchPatternResolutionInstructions_applyParameters]
  simpa [applyTypedMatchPattern] using
    (StructuralSubstitution.PatternInstructionHasType.applyParameters catalog
      contextValid resolutionTyping)

theorem PatternCoversConstructor.applyParameters
    {substitution : ParameterSubstitution} {pattern : TypedMatchPattern}
    {constructor : ProgramDataConstructorId}
    (covers : PatternCoversConstructor pattern constructor) :
    PatternCoversConstructor (applyTypedMatchPattern substitution pattern)
      constructor := by
  rcases covers with ⟨instantiation, instructions, resolutionEq,
    constructorEq, irrefutable⟩
  refine ⟨applyDataConstructorInstantiation substitution instantiation,
    instructions.map (applyMatchPatternInstruction substitution), ?_, ?_, ?_⟩
  · change applyMatchPatternResolution substitution pattern.resolution =
      .constructor (applyDataConstructorInstantiation substitution instantiation)
        (instructions.map (applyMatchPatternInstruction substitution))
    rw [resolutionEq]
    rfl
  · simpa [applyDataConstructorInstantiation] using constructorEq
  · simpa [applyDataConstructorInstantiation] using
      (StructuralSubstitution.PatternInstructionsIrrefutable.applyParameters
        irrefutable)

theorem MatchExhaustive.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {scrutineeType : Ty} {cases : List TypedMatchCase}
    {defaultBody : Option (List StatementId)}
    (exhaustive : MatchExhaustive context scrutineeType cases defaultBody) :
    MatchExhaustive (applyContext substitution context)
      (substitution.apply scrutineeType)
      (cases.map (applyTypedMatchCase substitution)) defaultBody := by
  cases exhaustive with
  | default body => exact .default body
  | catchall member irrefutable =>
      exact .catchall (List.mem_map.mpr ⟨_, member, rfl⟩)
        (StructuralSubstitution.TypedMatchPatternIrrefutable.applyParameters
          irrefutable)
  | constructors dataTypeMem exactInner scrutineeEq covered =>
      rename_i dataType substitutionInner
      refine .constructors
        (by simpa [applyContext] using dataTypeMem)
        (StructuralSubstitution.ParameterSubstitution.Exact.mapRange
          substitution exactInner) ?_ ?_
      · rw [scrutineeEq, StructuralSubstitution.apply_nominal,
          StructuralSubstitution.ParameterSubstitution.orderedArguments_mapRange
            exactInner]
      · intro constructor constructorMem
        rcases covered constructor constructorMem with
          ⟨matchCase, matchCaseMem, covers⟩
        exact ⟨applyTypedMatchCase substitution matchCase,
          List.mem_map.mpr ⟨matchCase, matchCaseMem, rfl⟩,
          StructuralSubstitution.PatternCoversConstructor.applyParameters
            covers⟩

@[simp] theorem localSchemeTemplateIds_applyBinder
    (substitution : ParameterSubstitution) (binder : TypedBinder) :
    localSchemeTemplateIds (applyBinder substitution binder) =
      localSchemeTemplateIds binder := by
  simp [localSchemeTemplateIds, applyBinder,
    LocalSchemeRequirement.applyParameters, List.map_map,
    Function.comp_def]

theorem LocalSchemeRequirementWellFormed.applyParameters
    {context : Context} {binder : TypedBinder}
    {requirement : LocalSchemeRequirement}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : LocalSchemeRequirementWellFormed context binder requirement) :
    LocalSchemeRequirementWellFormed (applyContext substitution context)
      (applyBinder substitution binder)
      (requirement.applyParameters substitution) := by
  have initializerExact :
      SourceSemantics.ParameterSubstitution.Exact substitution
        (localSchemeInitializerContext context binder).typeParameters := by
    simpa [localSchemeInitializerContext, Context.withTypeVariables,
      Context.withAssumptions] using exact
  have initializerRange :
      SourceSemantics.ParameterSubstitution.RangeWellFormed
        (applyContext substitution
          (localSchemeInitializerContext context binder)) substitution := by
    intro parameter replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := applyContext substitution context)
      (target := applyContext substitution
        (localSchemeInitializerContext context binder))
      rfl rfl rfl (range parameter replacement member)
  constructor
  · simpa [StructuralSubstitution.applyContext_localSchemeInitializerContext,
      LocalSchemeRequirement.applyParameters] using
      (StructuralSubstitution.PredicateAdmissible.applyParameters substitution
        initializerExact initializerRange wellFormed.predicate)
  · rcases wellFormed.depends_on_quantified with
      ⟨metavariable, quantified, occurs⟩
    refine ⟨metavariable, ?_, ?_⟩
    · simpa [applyBinder, applyScheme] using quantified
    · simpa [LocalSchemeRequirement.applyParameters,
        StructuralSubstitution.predicateVariables_applyParameters substitution
          range] using occurs
  · rcases wellFormed.template with
      ⟨solved, solvedUnique, idEq, predicateEq, evidenceEq⟩
    refine ⟨applySolvedRequirement substitution solved, ?_, ?_, ?_, ?_⟩
    · have filtered :
          ((context.solvedRequirements.map
              (applySolvedRequirement substitution)).filter fun candidate =>
                candidate.id == requirement.templateRequirement) =
            (context.solvedRequirements.filter fun candidate =>
                candidate.id == requirement.templateRequirement).map
              (applySolvedRequirement substitution) := by
          induction context.solvedRequirements with
          | nil => rfl
          | cons candidate requirements induction =>
              by_cases selected :
                  candidate.id == requirement.templateRequirement
              · simp [applySolvedRequirement, selected, induction]
              · simp [applySolvedRequirement, selected, induction]
      simpa [applyContext, LocalSchemeRequirement.applyParameters, filtered]
        using congrArg
          (List.map (applySolvedRequirement substitution)) solvedUnique
    · exact idEq
    · simp [applySolvedRequirement, LocalSchemeRequirement.applyParameters,
        predicateEq]
    · simp [applySolvedRequirement, applyPredicateEvidence,
        LocalSchemeRequirement.applyParameters, evidenceEq]

theorem LocalSchemeRequirementsWellFormed.applyParameters
    {context : Context} {binder : TypedBinder}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : LocalSchemeRequirementsWellFormed context binder) :
    LocalSchemeRequirementsWellFormed (applyContext substitution context)
      (applyBinder substitution binder) := by
  constructor
  · simpa using wellFormed.ids_unique
  · intro requirement member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    exact StructuralSubstitution.LocalSchemeRequirementWellFormed.applyParameters
      substitution exact range (wellFormed.entries original originalMem)

/-- Rigid substitution commutes with the ordered predicate instance generated
by one shared flexible local-scheme substitution. -/
theorem instantiateLocalSchemePredicates_applyParameters
    {context : Context} {binder : TypedBinder}
    {inner : TypeSystem.Substitution}
    (outer : ParameterSubstitution)
    (contextValid : ContextSubstitutionValid outer context)
    (formation : LocalSchemeRequirementsWellFormed context binder)
    (innerExact : ExactSubstitution inner binder.scheme.quantified) :
    (instantiateLocalSchemePredicates inner binder).map
        (ProgramPredicate.applyParameters outer) =
      instantiateLocalSchemePredicates (Substitution.mapRange outer inner)
        (applyBinder outer binder) := by
  unfold instantiateLocalSchemePredicates
  simp only [applyBinder, List.map_map]
  apply List.map_congr_left
  intro requirement member
  have initializerValid := contextValid.localSchemeInitializer binder
  exact StructuralSubstitution.PredicateAdmissible.applyMixed_compose outer
    inner initializerValid.exact initializerValid.range innerExact
    (formation.entries requirement member).predicate

theorem LocalSchemeInstantiationValid.applyParameters
    {context : Context} {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    (outer : ParameterSubstitution)
    (contextValid : ContextSubstitutionValid outer context)
    (valid : LocalSchemeInstantiationValid context binder type
      actualRequirements) :
    LocalSchemeInstantiationValid (applyContext outer context)
      (applyBinder outer binder) (outer.apply type) actualRequirements := by
  cases valid with
  | intro formation schemeWellFormed inner innerExact innerRange result
      actualUnique actualDisjoint requirements =>
      refine .intro
        (StructuralSubstitution.LocalSchemeRequirementsWellFormed.applyParameters
          outer contextValid.exact contextValid.range formation)
        (StructuralSubstitution.SchemeWellFormed.applyParameters outer
          contextValid.exact contextValid.range schemeWellFormed)
        (Substitution.mapRange outer inner)
        (StructuralSubstitution.Substitution.ExactSubstitution.mapRange outer
          innerExact)
        ?_ ?_ actualUnique ?_ ?_
      · intro metavariable replacement member
        rcases List.mem_map.mp member with ⟨entry, entryMember, entryEq⟩
        rcases entry with ⟨innerVariable, innerReplacement⟩
        cases entryEq
        exact StructuralSubstitution.TypeAdmissible.applyParameters outer
          contextValid.exact contextValid.range
          (innerRange innerVariable innerReplacement entryMember)
      · change (Substitution.mapRange outer inner).apply
          (outer.apply binder.scheme.body) = outer.apply type
        rw [← result]
        exact (StructuralSubstitution.TypeWellScoped.applyMixed_compose outer
          inner contextValid.exact contextValid.range innerExact
          schemeWellFormed.body).symm
      · intro id actualMember templateMember
        exact actualDisjoint id actualMember (by
          simpa using templateMember)
      · have transported :=
          StructuralSubstitution.RequirementSequenceProves.applyParameters
            contextValid requirements
        rw [StructuralSubstitution.instantiateLocalSchemePredicates_applyParameters
          outer contextValid formation innerExact] at transported
        exact transported

theorem ReferenceUseValid.applyParameters
    {outer : ParameterSubstitution} {context : Context}
    {resolution : ReferenceResolution} {type : Ty}
    {requirements : List RequirementId}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid outer context)
    (valid : ReferenceUseValid context resolution type requirements) :
    ReferenceUseValid (applyContext outer context)
      (applyReferenceResolution outer resolution) (outer.apply type)
      requirements := by
  cases valid with
  | «local» schemeLookup requirementsLookup instantiation =>
      refine .local (binder := applyBinder outer _) ?_ ?_ ?_
      · exact
        (StructuralSubstitution.LocalLookup.applyParameters outer schemeLookup)
      · exact
          (StructuralSubstitution.LocalSchemeRequirementsLookup.applyParameters
          outer requirementsLookup)
      · exact
          (StructuralSubstitution.LocalSchemeInstantiationValid.applyParameters
          outer contextValid instantiation)
  | declaration instantiationValid proves =>
      exact .declaration
        (StructuralSubstitution.DeclarationInstantiation.Admissible.applyParameters
          catalog contextValid instantiationValid)
        (StructuralSubstitution.RequirementSequenceProves.applyParameters
          contextValid proves)
  | builtinFunction function =>
      cases function <;> simp [applyReferenceResolution,
        BuiltinFunctionId.type, BuiltinFunctionId.parameterTypes,
        BuiltinFunctionId.returnType] <;> exact .builtinFunction _
  | builtinBoolean value =>
      simpa [applyReferenceResolution] using
        (ReferenceUseValid.builtinBoolean
          (context := applyContext outer context) value)

theorem BinderWellFormed.applyParameters
    {context : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (wellFormed : BinderWellFormed context owner binder) :
    BinderWellFormed (applyContext substitution context) owner
      (applyBinder substitution binder) := {
  owned := wellFormed.owned
  scheme := StructuralSubstitution.SchemeWellFormed.applyParameters substitution
    exact range wellFormed.scheme
  quantified_fresh := by
    intro metavariable quantified
    have sourceQuantified : metavariable ∈ binder.scheme.quantified := by
      simpa [applyBinder, applyScheme] using quantified
    rcases wellFormed.quantified_fresh metavariable sourceQuantified with
      ⟨ambientFresh, localsFresh⟩
    constructor
    · simpa [applyContext] using ambientFresh
    · intro entry member localQuantified
      rcases List.mem_map.mp member with
        ⟨⟨id, scheme⟩, sourceMember, localEq⟩
      subst entry
      exact localsFresh (id, scheme) sourceMember (by
        simpa [applyScheme] using localQuantified)
  monomorphic_requirements_empty := by
    intro quantifiedEmpty
    have originalQuantifiedEmpty : binder.scheme.quantified = [] := by
      simpa [applyBinder, applyScheme] using quantifiedEmpty
    simp [applyBinder, wellFormed.monomorphic_requirements_empty
      originalQuantifiedEmpty]
}

theorem BinderExtends.applyParameters
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (extension : BinderExtends owner context binder final) :
    BinderExtends owner (applyContext substitution context)
      (applyBinder substitution binder) (applyContext substitution final) := by
  cases extension with
  | intro wellFormed fresh =>
      exact .intro
        (StructuralSubstitution.BinderWellFormed.applyParameters substitution
          exact range wellFormed)
        (StructuralSubstitution.LocalFresh.applyParameters substitution fresh)

theorem BindersExtend.applyParameters
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (extension : BindersExtend owner context binders final) :
    BindersExtend owner (applyContext substitution context)
      (binders.map (applyBinder substitution))
      (applyContext substitution final) := by
  induction extension with
  | nil => exact .nil _
  | @cons context middle final binder binders head tail induction =>
      have fields := head.context_fields
      have exactMiddle :
          SourceSemantics.ParameterSubstitution.Exact substitution
            middle.typeParameters := by
        simpa [fields.2.2.1] using exact
      have rangeMiddle :
          SourceSemantics.ParameterSubstitution.RangeWellFormed
            (applyContext substitution middle) substitution := by
        intro parameter replacement member
        exact StructuralSubstitution.TypeWellFormed.transportContext
          (source := applyContext substitution context)
          (target := applyContext substitution middle)
          fields.1 rfl fields.2.1
          (range parameter replacement member)
      exact .cons
        (StructuralSubstitution.BinderExtends.applyParameters substitution exact
          range head)
        (induction exactMiddle rangeMiddle)

theorem MonoBindersExtend.applyParameters
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution
      context.typeParameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution context) substitution)
    (extension : MonoBindersExtend owner context binders types final) :
    MonoBindersExtend owner (applyContext substitution context)
      (binders.map (applyBinder substitution))
      (types.map substitution.apply) (applyContext substitution final) := by
  induction extension with
  | nil => exact .nil _
  | @cons context middle final binder binders type types schemeEq head tail
      induction =>
      have fields := head.context_fields
      have exactMiddle :
          SourceSemantics.ParameterSubstitution.Exact substitution
            middle.typeParameters := by
        simpa [fields.2.2.1] using exact
      have rangeMiddle :
          SourceSemantics.ParameterSubstitution.RangeWellFormed
            (applyContext substitution middle) substitution := by
        intro parameter replacement member
        exact StructuralSubstitution.TypeWellFormed.transportContext
          (source := applyContext substitution context)
          (target := applyContext substitution middle)
          fields.1 rfl fields.2.1
          (range parameter replacement member)
      refine .cons ?_ ?_ (induction exactMiddle rangeMiddle)
      · simp [applyBinder, applyScheme, schemeEq, TypeSystem.Scheme.mono]
      · exact StructuralSubstitution.BinderExtends.applyParameters substitution
          exact range head

theorem ContextSubstitutionValid.afterBinder
    {substitution : ParameterSubstitution} {owner : Resolved.DeclarationId}
    {context final : Context} {binder : TypedBinder}
    (valid : ContextSubstitutionValid substitution context)
    (extension : BinderExtends owner context binder final) :
    ContextSubstitutionValid substitution final := by
  cases extension
  exact valid.underLocal

theorem ContextSubstitutionValid.afterBinders
    {substitution : ParameterSubstitution} {owner : Resolved.DeclarationId}
    {context final : Context} {binders : List TypedBinder}
    (valid : ContextSubstitutionValid substitution context)
    (extension : BindersExtend owner context binders final) :
    ContextSubstitutionValid substitution final := by
  induction extension with
  | nil => exact valid
  | cons head tail induction =>
      exact induction (valid.afterBinder head)

theorem ContextSubstitutionValid.afterMonoBinders
    {substitution : ParameterSubstitution} {owner : Resolved.DeclarationId}
    {context final : Context} {binders : List TypedBinder} {types : List Ty}
    (valid : ContextSubstitutionValid substitution context)
    (extension : MonoBindersExtend owner context binders types final) :
    ContextSubstitutionValid substitution final := by
  induction extension with
  | nil => exact valid
  | cons _ head tail induction =>
      exact induction (valid.afterBinder head)

theorem BindersExtend.signatures_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder}
    (extension : BindersExtend owner context binders final) :
    final.signatures = context.signatures := by
  induction extension with
  | nil => rfl
  | cons head tail induction =>
      exact induction.trans head.context_fields.1

theorem MonoBindersExtend.signatures_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    final.signatures = context.signatures := by
  induction extension with
  | nil => rfl
  | cons _ head tail induction =>
      exact induction.trans head.context_fields.1

theorem StatementHasType.signatures_eq
    {source : TypedSource} {control : ControlContext}
    {context final : Context} {id : StatementId} {facts : StatementFacts}
    (typing : StatementHasType source control context id final facts) :
    final.signatures = context.signatures := by
  cases typing with
  | letUninitialized _ _ _ _ extension _ => exact extension.context_fields.1
  | letInitialized _ _ _ _ _ extension _ => exact extension.context_fields.1
  | letInitializedGeneralized _ _ _ _ _ _ extension _ =>
      exact extension.context_fields.1
  | returnUnit | returnValue | expressionValue | expressionDiscard |
      assignValue | assignBitNot | ifWithoutElse | ifWithElse | block |
      matchWithoutDefault | matchWithDefault | forLoop | whileLoop |
      breakStmt | continueStmt => rfl

theorem StatementHasType.contextSubstitutionValid
    {substitution : ParameterSubstitution} {source : TypedSource}
    {control : ControlContext} {context final : Context}
    {id : StatementId} {facts : StatementFacts}
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : StatementHasType source control context id final facts) :
    ContextSubstitutionValid substitution final := by
  cases typing with
  | letUninitialized _ _ _ _ extension _ =>
      exact contextValid.afterBinder extension
  | letInitialized _ _ _ _ _ extension _ =>
      exact contextValid.afterBinder extension
  | letInitializedGeneralized _ _ _ _ _ _ extension _ =>
      exact contextValid.afterBinder extension
  | returnUnit | returnValue | expressionValue | expressionDiscard |
      assignValue | assignBitNot | ifWithoutElse | ifWithElse | block |
      matchWithoutDefault | matchWithDefault | forLoop | whileLoop |
      breakStmt | continueStmt => exact contextValid

theorem ForItemHasType.signatures_eq
    {source : TypedSource} {control : ControlContext}
    {context final : Context} {item : ForItemForm}
    (typing : ForItemHasType source control context item final) :
    final.signatures = context.signatures := by
  cases typing with
  | letUninitialized _ _ extension => exact extension.context_fields.1
  | letInitialized _ _ _ extension => exact extension.context_fields.1
  | letInitializedGeneralized _ _ _ _ extension =>
      exact extension.context_fields.1
  | expression | assignValue | assignBitNot => rfl

theorem ForItemHasType.contextSubstitutionValid
    {substitution : ParameterSubstitution} {source : TypedSource}
    {control : ControlContext} {context final : Context}
    {item : ForItemForm}
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : ForItemHasType source control context item final) :
    ContextSubstitutionValid substitution final := by
  cases typing with
  | letUninitialized _ _ extension => exact contextValid.afterBinder extension
  | letInitialized _ _ _ extension => exact contextValid.afterBinder extension
  | letInitializedGeneralized _ _ _ _ extension =>
      exact contextValid.afterBinder extension
  | expression | assignValue | assignBitNot => exact contextValid

theorem ForItemsHaveType.signatures_eq
    {source : TypedSource} {control : ControlContext}
    {context final : Context} {items : List ForItemForm}
    (typing : ForItemsHaveType source control context items final) :
    final.signatures = context.signatures := by
  induction items generalizing context final with
  | nil =>
      cases typing
      rfl
  | cons item items induction =>
      cases typing with
      | cons head tail =>
          exact (induction tail).trans
            (StructuralSubstitution.ForItemHasType.signatures_eq head)

theorem ForItemsHaveType.contextSubstitutionValid
    {substitution : ParameterSubstitution} {source : TypedSource}
    {control : ControlContext} {context final : Context}
    {items : List ForItemForm}
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : ForItemsHaveType source control context items final) :
    ContextSubstitutionValid substitution final := by
  induction items generalizing context final with
  | nil =>
      cases typing
      exact contextValid
  | cons item items induction =>
      cases typing with
      | cons head tail =>
          exact induction
            (StructuralSubstitution.ForItemHasType.contextSubstitutionValid
              contextValid head) tail

theorem ExpressionRequirementPlan.Valid.applyParameters
    {substitution : ParameterSubstitution} {context : Context}
    {rawType finalType : Ty} {plan : ExpressionRequirementPlan}
    {requirements : List RequirementId} {coercions : List CoercionStep}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (valid : ExpressionRequirementPlan.Valid context rawType finalType plan
      requirements coercions) :
    ExpressionRequirementPlan.Valid (applyContext substitution context)
      (substitution.apply rawType) (substitution.apply finalType)
      (applyExpressionRequirementPlan substitution plan) requirements
      (coercions.map (applyCoercionStep substitution)) := by
  cases valid with
  | ordinary ownedValid pathValid requirementsEq =>
      exact .ordinary
        (StructuralSubstitution.RequirementIdsValid.applyParameters contextValid
          ownedValid)
        (StructuralSubstitution.CoercionPathValid.applyParameters catalog
          contextValid pathValid)
        (by simp [requirementsEq,
          StructuralSubstitution.coercionRequirementIds_applyCoercionSteps])

  | directCall valid =>
      exact .directCall
        (StructuralSubstitution.DirectCallRequirementsValid.applyParameters
          catalog contextValid valid)
  | indirectCall argumentsValid outputValid requirementsEq =>
      exact .indirectCall
        (by simpa [StructuralSubstitution.coercionRequirementIds_applyCoercionSteps] using
            (StructuralSubstitution.RequirementIdsValid.applyParameters
              contextValid argumentsValid))
        (StructuralSubstitution.CoercionPathValid.applyParameters catalog
          contextValid outputValid)
        (by simp [requirementsEq,
          StructuralSubstitution.coercionRequirementIds_applyCoercionSteps])

@[simp] theorem flatMap_patternRequirements_applyTypedMatchCases
    (substitution : ParameterSubstitution) (cases : List TypedMatchCase) :
    (cases.map (applyTypedMatchCase substitution)).flatMap
        (fun matchCase => matchCase.pattern.requirements) =
      cases.flatMap (fun matchCase => matchCase.pattern.requirements) := by
  induction cases with
  | nil => rfl
  | cons head tail induction =>
      simp [applyTypedMatchCase, applyTypedMatchPattern, induction]

@[simp] theorem applyControlContext_enterLoop
    (substitution : ParameterSubstitution) (control : ControlContext) :
    applyControlContext substitution control.enterLoop =
      (applyControlContext substitution control).enterLoop := by
  cases control
  rfl

@[simp] theorem applyControlSummary_ordinary
    (substitution : ParameterSubstitution) (type : Ty) :
    applyControlSummary substitution (.ordinary type) =
      .ordinary (substitution.apply type) := by
  rfl

@[simp] theorem applyControlSummary_returned
    (substitution : ParameterSubstitution) :
    applyControlSummary substitution .returned = .returned := by
  rfl

@[simp] theorem applyControlSummary_breaking
    (substitution : ParameterSubstitution) :
    applyControlSummary substitution .breaking = .breaking := by
  rfl

@[simp] theorem applyControlSummary_continuing
    (substitution : ParameterSubstitution) :
    applyControlSummary substitution .continuing = .continuing := by
  rfl

@[simp] theorem applyControlSummary_sequence
    (substitution : ParameterSubstitution)
    (head tail : ControlSummary) :
    applyControlSummary substitution (head.sequence tail) =
      (applyControlSummary substitution head).sequence
        (applyControlSummary substitution tail) := by
  cases head with
  | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;>
        simp [applyControlSummary, ControlSummary.sequence,
          ControlSummary.canFallthrough]

@[simp] theorem applyControlSummary_branches
    (substitution : ParameterSubstitution)
    (left right : ControlSummary) :
    applyControlSummary substitution (left.branches right) =
      (applyControlSummary substitution left).branches
        (applyControlSummary substitution right) := by
  cases left with
  | mk leftFallthrough leftReturn leftBreak leftContinue =>
      cases right with
      | mk rightFallthrough rightReturn rightBreak rightContinue =>
          cases leftFallthrough <;> cases rightFallthrough <;>
            simp [applyControlSummary, ControlSummary.branches,
              ControlSummary.canFallthrough]

@[simp] theorem applyControlSummary_eraseValue
    (substitution : ParameterSubstitution) (summary : ControlSummary) :
    applyControlSummary substitution summary.eraseValue =
      (applyControlSummary substitution summary).eraseValue := by
  cases summary with
  | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;>
        simp [applyControlSummary, ControlSummary.eraseValue]

@[simp] theorem applyControlSummary_loop
    (substitution : ParameterSubstitution) (summary : ControlSummary) :
    applyControlSummary substitution summary.loop =
      (applyControlSummary substitution summary).loop := by
  cases summary
  rfl

@[simp] theorem applyStatementFacts_singleton
    (substitution : ParameterSubstitution) (facts : StatementFacts) :
    applyBodyFacts substitution (.singleton facts) =
      .singleton (applyStatementFacts substitution facts) := by
  rcases facts with ⟨type, hasValue, sawReturn, control⟩
  cases hasValue <;> cases sawReturn <;>
    simp [applyBodyFacts, applyStatementFacts, BodyFacts.singleton]

@[simp] theorem applyBodyFacts_empty (substitution : ParameterSubstitution) :
    applyBodyFacts substitution .empty = .empty := by
  rfl

@[simp] theorem applyBodyFacts_cons
    (substitution : ParameterSubstitution)
    (head : StatementFacts) (tail : BodyFacts) :
    applyBodyFacts substitution (.cons head tail) =
      .cons (applyStatementFacts substitution head)
        (applyBodyFacts substitution tail) := by
  rcases head with ⟨headType, hasValue, headSawReturn, headControl⟩
  rcases tail with ⟨tailType, tailSawReturn, tailControl⟩
  cases headSawReturn <;> cases tailSawReturn <;>
    simp [applyBodyFacts, applyStatementFacts, BodyFacts.cons]

@[simp] theorem allBodiesSawReturn_applyBodyFacts
    (substitution : ParameterSubstitution) (facts : List BodyFacts) :
    allBodiesSawReturn (facts.map (applyBodyFacts substitution)) =
      allBodiesSawReturn facts := by
  induction facts with
  | nil => rfl
  | cons head tail induction =>
      unfold allBodiesSawReturn at induction ⊢
      simp only [List.map_cons, List.all_cons, applyBodyFacts]
      rw [induction]

theorem mergeBodyControls_applyBodyFacts
    (substitution : ParameterSubstitution) (facts : List BodyFacts)
    (fallback : Option BodyFacts) :
    mergeBodyControls (facts.map (applyBodyFacts substitution))
        (fallback.map (applyBodyFacts substitution)) =
      (mergeBodyControls facts fallback).map
        (applyControlSummary substitution) := by
  induction facts with
  | nil =>
      cases fallback <;> rfl
  | cons head tail induction =>
      simp only [List.map_cons, mergeBodyControls]
      rw [induction]
      cases merged : mergeBodyControls tail fallback with
      | none => rfl
      | some summary =>
          simp [applyBodyFacts]

theorem BodyCompletes.applyParameters
    {expected : Ty} {facts : BodyFacts}
    (substitution : ParameterSubstitution)
    (completes : BodyCompletes expected facts) :
    BodyCompletes (substitution.apply expected)
      (applyBodyFacts substitution facts) := by
  rcases completes with ⟨noBreak, noContinue, completion⟩
  refine ⟨noBreak, noContinue, ?_⟩
  rcases completion with ⟨fallthrough, returned⟩ | fallthrough
  · left
    exact ⟨by simp [applyBodyFacts, applyControlSummary, fallthrough], returned⟩
  · right
    simp [applyBodyFacts, applyControlSummary, fallthrough]

/-- Rigid instantiation transports the complete mutually recursive source
typing derivation.  The eliminator is rooted at statement sequences because
that is the boundary needed by declaration bodies; its motives cover every
expression, place, pattern arm, and `for` item recursively reachable from the
body. -/
theorem StatementsHaveType.applyParameters
    {substitution : ParameterSubstitution} {source : TypedSource}
    {control : ControlContext} {context final : Context}
    {statements : List StatementId} {facts : BodyFacts}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : StatementsHaveType source control context statements final facts) :
    StatementsHaveType (applyTypedSource substitution source)
      (applyControlContext substitution control)
      (applyContext substitution context) statements
      (applyContext substitution final) (applyBodyFacts substitution facts) := by
  apply StatementsHaveType.rec
    (motive_1 := fun context id type _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        ExpressionHasType (applyTypedSource substitution source)
          (applyContext substitution context) id (substitution.apply type))
    (motive_2 := fun context form rawType plan _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        ExpressionFormHasRawType (applyTypedSource substitution source)
          (applyContext substitution context)
          (applyExpressionForm substitution form) (substitution.apply rawType)
          (applyExpressionRequirementPlan substitution plan))
    (motive_3 := fun context expressions types _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        ExpressionsHaveTypes (applyTypedSource substitution source)
          (applyContext substitution context) expressions
          (types.map substitution.apply))
    (motive_4 := fun context initial projections result _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        SourceProjectionsHaveType (applyTypedSource substitution source)
          (applyContext substitution context) (substitution.apply initial)
          projections (substitution.apply result))
    (motive_5 := fun context place type _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        SourcePlaceHasType (applyTypedSource substitution source)
          (applyContext substitution context)
          (applyPlaceResolution substitution place) (substitution.apply type))
    (motive_6 := fun context assignment operator value _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        SourceAssignmentHasType (applyTypedSource substitution source)
          (applyContext substitution context)
          (applyAssignmentResolution substitution assignment) operator value)
    (motive_7 := fun context assignment _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        SourceBitNotAssignmentValid (applyTypedSource substitution source)
          (applyContext substitution context)
          (applyAssignmentResolution substitution assignment))
    (motive_8 := fun control context id final facts _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        StatementHasType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context) id
          (applyContext substitution final)
          (applyStatementFacts substitution facts))
    (motive_9 := fun control context statements final facts _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        StatementsHaveType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context) statements
          (applyContext substitution final) (applyBodyFacts substitution facts))
    (motive_10 := fun control context item final _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        ForItemHasType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context)
          (applyForItemForm substitution item) (applyContext substitution final))
    (motive_11 := fun control context items final _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        ForItemsHaveType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context)
          (items.map (applyForItemForm substitution))
          (applyContext substitution final))
    (motive_12 := fun control context scrutineeType matchCase facts _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        MatchCaseHasType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context) (substitution.apply scrutineeType)
          (applyTypedMatchCase substitution matchCase)
          (applyBodyFacts substitution facts))
    (motive_13 := fun control context scrutineeType cases facts _ =>
      ∀ (catalog : SignatureCatalogWellFormed context.signatures),
        ContextSubstitutionValid substitution context →
        MatchCasesHaveType (applyTypedSource substitution source)
          (applyControlContext substitution control)
          (applyContext substitution context) (substitution.apply scrutineeType)
          (cases.map (applyTypedMatchCase substitution))
          (facts.map (applyBodyFacts substitution)))
  · intro context id node rawType plan contains formType rawTypeEq
      rawWellFormed typeWellFormed requirements formInduction catalog contextValid
    exact .intro
      (StructuralSubstitution.ContainsExpression.applyParameters substitution
        contains)
      (formInduction catalog contextValid)
      (by simp [rawTypeEq])
      (StructuralSubstitution.TypeAdmissible.applyParameters substitution
        contextValid.exact contextValid.range rawWellFormed)
      (StructuralSubstitution.TypeAdmissible.applyParameters substitution
        contextValid.exact contextValid.range typeWellFormed)
      (StructuralSubstitution.ExpressionRequirementPlan.Valid.applyParameters
        catalog contextValid requirements)
  · intro context literal valid catalog contextValid
    exact .literal valid
  · intro context literal resolution valid catalog contextValid
    exact .integerLiteral
      (StructuralSubstitution.IntegerLiteralValid.applyParameters contextValid
        valid)
  · intro context name resolution type requirements referenceUse catalog
      contextValid
    exact .reference
      (StructuralSubstitution.ReferenceUseValid.applyParameters catalog
        contextValid referenceUse)
  · intro context inner type innerType innerInduction catalog contextValid
    exact .group (innerInduction catalog contextValid)
  · intro context elements types elementsType elementsInduction catalog
      contextValid
    simpa [applyExpressionForm, applyExpressionRequirementPlan,
      StructuralSubstitution.apply_productMany] using
      (ExpressionFormHasRawType.tuple (elementsInduction catalog contextValid))
  · intro context operator operand operandType resultType requirements
      operandTypeProof operatorType operandInduction catalog contextValid
    exact .unary (operandInduction catalog contextValid)
      (StructuralSubstitution.UnaryOperatorHasType.applyParameters catalog
        contextValid operatorType)
  · intro context operator left right operandType resultType requirements
      leftType rightType operatorType leftInduction rightInduction catalog
      contextValid
    exact .binary (leftInduction catalog contextValid)
      (rightInduction catalog contextValid)
      (StructuralSubstitution.BinaryOperatorHasType.applyParameters catalog
        contextValid operatorType)
  · intro context condition thenBranch elseBranch type conditionType thenType
      elseType conditionInduction thenInduction elseInduction catalog contextValid
    exact .conditional (conditionInduction catalog contextValid)
      (thenInduction catalog contextValid) (elseInduction catalog contextValid)
  · intro context lambdaContext finalContext parameters parameterTypes
      returnType body bodyFacts namesUnique parametersExtend bodyType bodyCompletes
      bodyInduction catalog contextValid
    have lambdaCatalog :
        SignatureCatalogWellFormed lambdaContext.signatures := by
      rw [StructuralSubstitution.MonoBindersExtend.signatures_eq parametersExtend]
      exact catalog
    have lambdaValid := contextValid.afterMonoBinders parametersExtend
    simpa [applyExpressionForm, applyExpressionRequirementPlan,
      StructuralSubstitution.apply_productMany, List.map_map,
      Function.comp_def, applyBinder] using
      (ExpressionFormHasRawType.lambda
        (source := applyTypedSource substitution source)
        (by simpa [List.map_map, Function.comp_def, applyBinder] using namesUnique)
        (StructuralSubstitution.MonoBindersExtend.applyParameters substitution
          contextValid.exact contextValid.range parametersExtend)
        (bodyInduction lambdaCatalog lambdaValid)
        (StructuralSubstitution.BodyCompletes.applyParameters substitution
          bodyCompletes))
  · intro context callee arguments instantiation parameterTypes resultType
      predicates calleeValid application argumentsType argumentsInduction catalog
      contextValid
    exact .directCall
      (StructuralSubstitution.DirectDeclarationCalleeValid.applyParameters
        catalog contextValid calleeValid)
      (StructuralSubstitution.DeclarationApplicationValid.applyParameters catalog
        contextValid application)
      (argumentsInduction catalog contextValid)
  · intro context callee arguments function calleeValid argumentsType
      argumentsInduction catalog contextValid
    have calleeAfter :=
      StructuralSubstitution.DirectBuiltinCalleeValid.applyParameters
        (substitution := substitution) calleeValid
    have argumentsAfter := argumentsInduction catalog contextValid
    cases function <;>
      simpa [BuiltinFunctionId.parameterTypes, BuiltinFunctionId.returnType,
        applyExpressionForm, applyExpressionRequirementPlan,
        applyCallResolution] using
        (ExpressionFormHasRawType.builtinCall calleeAfter argumentsAfter)
  · intro context callee arguments argumentTypes parameterType resultType
      metadata calleeType argumentsType application calleeInduction
      argumentsInduction catalog contextValid
    exact .indirectCall (calleeInduction catalog contextValid)
      (argumentsInduction catalog contextValid)
      (StructuralSubstitution.IndirectApplicationValid.applyParameters catalog
        contextValid application)
  · intro context instantiation arguments valid argumentsType
      argumentsInduction catalog contextValid
    exact .constructor
      (StructuralSubstitution.DataConstructorInstantiation.Admissible.applyParameters
        catalog contextValid valid)
      (argumentsInduction catalog contextValid)
  · intro context base name index baseType memberType baseTypeProof memberTypeProof
      baseInduction catalog contextValid
    exact .member (baseInduction catalog contextValid)
      (StructuralSubstitution.UniformMemberProjection.applyParameters catalog
        contextValid memberTypeProof)
  · intro context inner innerWellFormed catalog contextValid
    exact .proxy
      (StructuralSubstitution.TypeAdmissible.applyParameters substitution
        contextValid.exact contextValid.range innerWellFormed)
  · intro context base key keyType valueType baseType keyTypeProof
      baseInduction keyInduction catalog contextValid
    exact .index (baseInduction catalog contextValid)
      (keyInduction catalog contextValid)
  · intro context catalog contextValid
    exact .nil _
  · intro context expression expressions type types head tail headInduction
      tailInduction catalog contextValid
    exact .cons (headInduction catalog contextValid)
      (tailInduction catalog contextValid)
  · intro context type catalog contextValid
    exact .nil _
  · intro context key keyType valueType finalType rest keyTypeProof restType
      keyInduction restInduction catalog contextValid
    exact .index (keyInduction catalog contextValid)
      (restInduction catalog contextValid)
  · intro context name index baseType memberType finalType rest selected restType
      restInduction catalog contextValid
    exact .member
      (StructuralSubstitution.UniformMemberProjection.applyParameters catalog
        contextValid selected)
      (restInduction catalog contextValid)
  · intro context place rootType finalType rootTypeProof projectionsType
      storedTypeEq projectionsInduction catalog contextValid
    exact .intro
      (StructuralSubstitution.WritableLocal.applyParameters contextValid
        rootTypeProof)
      (projectionsInduction catalog contextValid)
      (by simpa [applyPlaceResolution] using
        (congrArg substitution.apply storedTypeEq))
  · intro context assignment value type targetType valueType requirementsEq
      targetInduction valueInduction catalog contextValid
    exact .equal (targetInduction catalog contextValid)
      (valueInduction catalog contextValid)
      (by simpa [applyAssignmentResolution] using requirementsEq)
  · intro context assignment operator value operatorKind targetType valueType
      requirementsEq targetInduction valueInduction catalog contextValid
    exact .wordCompound operatorKind
      (by simpa [applyAssignmentResolution, applyPlaceResolution] using
        targetInduction catalog contextValid)
      (by simpa using valueInduction catalog contextValid)
      (by simpa [applyAssignmentResolution] using requirementsEq)
  · intro context assignment targetType requirementsEq targetInduction catalog
      contextValid
    exact .intro
      (by simpa [applyAssignmentResolution, applyPlaceResolution] using
        targetInduction catalog contextValid)
      (by simpa [applyAssignmentResolution] using requirementsEq)
  · intro control context final id node binder contains formEq monomorphic
      generalizes extension typeEq catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.letUninitialized
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .letDecl (applyBinder substitution binder) none
          rw [formEq]
          rfl)
        (by simp [applyBinder, applyScheme, monomorphic])
        (StructuralSubstitution.SchemeGeneralizes.applyParameters substitution
          contextValid.range generalizes)
        (StructuralSubstitution.BinderExtends.applyParameters substitution
          contextValid.exact contextValid.range extension)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context final id node binder initializer contains formEq
      initializerType monomorphic generalizes extension typeEq
      initializerInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.letInitialized
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .letDecl (applyBinder substitution binder) (some initializer)
          rw [formEq]
          rfl)
        (initializerInduction catalog contextValid)
        (by simp [applyBinder, applyScheme, monomorphic])
        (StructuralSubstitution.SchemeGeneralizes.applyParameters substitution
          contextValid.range generalizes)
        (StructuralSubstitution.BinderExtends.applyParameters substitution
          contextValid.exact contextValid.range extension)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context final id node binder initializer contains formEq
      polymorphic requirementsWellFormed generalizes initializerType extension typeEq
      initializerInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.letInitializedGeneralized
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .letDecl (applyBinder substitution binder) (some initializer)
          rw [formEq]
          rfl)
        (by simpa [applyBinder, applyScheme] using polymorphic)
        (StructuralSubstitution.LocalSchemeRequirementsWellFormed.applyParameters
          substitution contextValid.exact contextValid.range
          requirementsWellFormed)
        (by
          rw [StructuralSubstitution.localSchemeTemplateIds_applyBinder]
          simpa [applyBinder] using
            (StructuralSubstitution.SchemeGeneralizesExcept.applyParameters
              substitution contextValid.range (localSchemeTemplateIds binder)
              generalizes))
        (by
          simpa [applyBinder, applyScheme] using
            (initializerInduction catalog
              (contextValid.localSchemeInitializer binder)))
        (StructuralSubstitution.BinderExtends.applyParameters substitution
          contextValid.exact contextValid.range extension)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node contains formEq returnTypeEq typeEq catalog
      contextValid
    simpa [applyStatementFacts, applyControlContext] using
      (StatementHasType.returnUnit
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form = .returnStmt none
          rw [formEq]
          rfl)
        (by simpa [applyControlContext] using
          (congrArg substitution.apply returnTypeEq))
        (by simpa [applyStatementNode, applyControlContext] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node value contains formEq valueType typeEq
      valueInduction catalog contextValid
    simpa [applyStatementFacts, applyControlContext] using
      (StatementHasType.returnValue
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .returnStmt (some value)
          rw [formEq]
          rfl)
        (valueInduction catalog contextValid)
        (by simpa [applyStatementNode, applyControlContext] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node expression type contains formEq expressionType
      typeEq expressionInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.expressionValue
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .expression expression false
          rw [formEq]
          rfl)
        (expressionInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node expression type contains formEq expressionType
      typeEq expressionInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.expressionDiscard
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .expression expression true
          rw [formEq]
          rfl)
        (expressionInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node assignment operator value contains formEq
      assignmentType typeEq assignmentInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.assignValue
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .assignValue (applyAssignmentResolution substitution assignment)
              operator value
          rw [formEq]
          rfl)
        (assignmentInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node assignment contains formEq assignmentType
      typeEq assignmentInduction catalog contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.assignBitNot
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .assignBitNot (applyAssignmentResolution substitution assignment)
          rw [formEq]
          rfl)
        (assignmentInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context thenFinal id node condition thenBody thenFacts
      contains formEq conditionType thenType typeEq conditionInduction
      thenInduction catalog contextValid
    simpa [applyStatementFacts, applyBodyFacts] using
      (StatementHasType.ifWithoutElse
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .ifThen condition thenBody none
          rw [formEq]
          rfl)
        (conditionInduction catalog contextValid)
        (thenInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context thenFinal elseFinal id node condition thenBody elseBody
      thenFacts elseFacts contains formEq conditionType thenType elseType typeEq
      conditionInduction thenInduction elseInduction catalog contextValid
    simpa [applyStatementFacts, applyControlContext, applyBodyFacts] using
      (StatementHasType.ifWithElse
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .ifThen condition thenBody (some elseBody)
          rw [formEq]
          rfl)
        (conditionInduction catalog contextValid)
        (thenInduction catalog contextValid)
        (elseInduction catalog contextValid)
        (by simpa [applyStatementNode, applyControlContext, applyBodyFacts] using
          (congrArg substitution.apply typeEq)))
  · intro control context innerFinal id node body bodyFacts contains formEq
      bodyType typeEq bodyInduction catalog contextValid
    simpa [applyStatementFacts, applyBodyFacts] using
      (StatementHasType.block
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form = .block body
          rw [formEq]
          rfl)
        (bodyInduction catalog contextValid)
        (by simpa [applyStatementNode, applyBodyFacts] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node resolution scrutineeType caseFacts summary
      contains formEq defaultEq scrutineeTypeProof casesType requirementsEq
      exhaustive merged typeEq scrutineeInduction casesInduction catalog
      contextValid
    simpa [applyStatementFacts, applyMatchResolution, applyBodyFacts,
      applyControlContext] using
      (StatementHasType.matchWithoutDefault
        (resolution := applyMatchResolution substitution resolution)
        (caseFacts := caseFacts.map (applyBodyFacts substitution))
        (summary := applyControlSummary substitution summary)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .matchWith (applyMatchResolution substitution resolution)
          rw [formEq]
          rfl)
        (by simpa [applyMatchResolution] using defaultEq)
        (scrutineeInduction catalog contextValid)
        (casesInduction catalog contextValid)
        (by simpa [applyMatchResolution,
          StructuralSubstitution.flatMap_patternRequirements_applyTypedMatchCases]
          using requirementsEq)
        (StructuralSubstitution.MatchExhaustive.applyParameters exhaustive)
        (by
          calc
            mergeBodyControls
                (caseFacts.map (applyBodyFacts substitution)) none =
                (mergeBodyControls caseFacts none).map
                  (applyControlSummary substitution) := by
                    simpa using
                      (StructuralSubstitution.mergeBodyControls_applyBodyFacts
                        substitution caseFacts none)
            _ = some (applyControlSummary substitution summary) := by
              rw [merged]
              rfl)
        (by simpa [applyStatementNode, applyControlContext, applyBodyFacts] using
          (congrArg substitution.apply typeEq)))
  · intro control context defaultFinal id node resolution defaultBody
      scrutineeType caseFacts defaultFacts summary contains formEq defaultEq
      scrutineeTypeProof casesType defaultType requirementsEq merged typeEq
      scrutineeInduction casesInduction defaultInduction catalog contextValid
    simpa [applyStatementFacts, applyMatchResolution, applyBodyFacts,
      applyControlContext] using
      (StatementHasType.matchWithDefault
        (resolution := applyMatchResolution substitution resolution)
        (caseFacts := caseFacts.map (applyBodyFacts substitution))
        (defaultFacts := applyBodyFacts substitution defaultFacts)
        (summary := applyControlSummary substitution summary)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .matchWith (applyMatchResolution substitution resolution)
          rw [formEq]
          rfl)
        (by simpa [applyMatchResolution] using defaultEq)
        (scrutineeInduction catalog contextValid)
        (casesInduction catalog contextValid)
        (defaultInduction catalog contextValid)
        (by simpa [applyMatchResolution,
          StructuralSubstitution.flatMap_patternRequirements_applyTypedMatchCases]
          using requirementsEq)
        (by
          calc
            mergeBodyControls
                (caseFacts.map (applyBodyFacts substitution))
                (some (applyBodyFacts substitution defaultFacts)) =
                (mergeBodyControls caseFacts (some defaultFacts)).map
                  (applyControlSummary substitution) := by
                    simpa using
                      (StructuralSubstitution.mergeBodyControls_applyBodyFacts
                        substitution caseFacts (some defaultFacts))
            _ = some (applyControlSummary substitution summary) := by
              rw [merged]
              rfl)
        (by simpa [applyStatementNode, applyControlContext, applyBodyFacts] using
          (congrArg substitution.apply typeEq)))
  · intro control context loopContext postContext bodyFinal id node initializer
      post condition body bodyFacts contains formEq initializerType conditionType
      bodyType postType typeEq initializerInduction conditionInduction
      bodyInduction postInduction catalog contextValid
    have loopCatalog : SignatureCatalogWellFormed loopContext.signatures := by
      rw [StructuralSubstitution.ForItemsHaveType.signatures_eq initializerType]
      exact catalog
    have loopValid :=
      StructuralSubstitution.ForItemsHaveType.contextSubstitutionValid
        contextValid initializerType
    simpa [applyStatementFacts, applyBodyFacts] using
      (StatementHasType.forLoop
        (control := applyControlContext substitution control)
        (bodyFacts := applyBodyFacts substitution bodyFacts)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .forLoop (initializer.map (applyForItemForm substitution)) condition
              (post.map (applyForItemForm substitution)) body
          rw [formEq]
          rfl)
        (initializerInduction catalog contextValid)
        (conditionInduction loopCatalog loopValid)
        (by simpa using bodyInduction loopCatalog loopValid)
        (by simpa using postInduction loopCatalog loopValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context bodyFinal id node condition body bodyFacts contains
      formEq conditionType bodyType typeEq conditionInduction bodyInduction catalog
      contextValid
    simpa [applyStatementFacts, applyBodyFacts] using
      (StatementHasType.whileLoop
        (control := applyControlContext substitution control)
        (bodyFacts := applyBodyFacts substitution bodyFacts)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form =
            .whileLoop condition body
          rw [formEq]
          rfl)
        (conditionInduction catalog contextValid)
        (by simpa using bodyInduction catalog contextValid)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node contains formEq allowed typeEq catalog
      contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.breakStmt
        (control := applyControlContext substitution control)
        (context := applyContext substitution context)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form = .breakStmt
          rw [formEq]
          rfl)
        (by simpa [applyControlContext, ControlContext.loopAllowed] using allowed)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context id node contains formEq allowed typeEq catalog
      contextValid
    simpa [applyStatementFacts] using
      (StatementHasType.continueStmt
        (control := applyControlContext substitution control)
        (context := applyContext substitution context)
        (StructuralSubstitution.ContainsStatement.applyParameters substitution
          contains)
        (by
          change applyStatementForm substitution node.form = .continueStmt
          rw [formEq]
          rfl)
        (by simpa [applyControlContext, ControlContext.loopAllowed] using allowed)
        (by simpa [applyStatementNode] using
          (congrArg substitution.apply typeEq)))
  · intro control context catalog contextValid
    exact .nil _ _
  · intro control context final statement statementFacts head headInduction
      catalog contextValid
    simpa using StatementsHaveType.singleton (headInduction catalog contextValid)
  · intro control context middle final statement next rest headFacts tailFacts
      head tail headInduction tailInduction catalog contextValid
    have middleCatalog : SignatureCatalogWellFormed middle.signatures := by
      rw [StructuralSubstitution.StatementHasType.signatures_eq head]
      exact catalog
    have middleValid :=
      StructuralSubstitution.StatementHasType.contextSubstitutionValid
        contextValid head
    simpa using StatementsHaveType.cons (headInduction catalog contextValid)
      (tailInduction middleCatalog middleValid)
  · intro control context final binder monomorphic generalizes extension catalog
      contextValid
    exact .letUninitialized
      (by simp [applyBinder, applyScheme, monomorphic])
      (StructuralSubstitution.SchemeGeneralizes.applyParameters substitution
        contextValid.range generalizes)
      (StructuralSubstitution.BinderExtends.applyParameters substitution
        contextValid.exact contextValid.range extension)
  · intro control context final binder initializer initializerType monomorphic
      generalizes extension initializerInduction catalog contextValid
    exact .letInitialized (initializerInduction catalog contextValid)
      (by simp [applyBinder, applyScheme, monomorphic])
      (StructuralSubstitution.SchemeGeneralizes.applyParameters substitution
        contextValid.range generalizes)
      (StructuralSubstitution.BinderExtends.applyParameters substitution
        contextValid.exact contextValid.range extension)
  · intro control context final binder initializer polymorphic
      requirementsWellFormed generalizes initializerType extension
      initializerInduction catalog
      contextValid
    exact .letInitializedGeneralized
      (by simpa [applyBinder, applyScheme] using polymorphic)
      (StructuralSubstitution.LocalSchemeRequirementsWellFormed.applyParameters
        substitution contextValid.exact contextValid.range
        requirementsWellFormed)
      (by
        rw [StructuralSubstitution.localSchemeTemplateIds_applyBinder]
        simpa [applyBinder] using
          (StructuralSubstitution.SchemeGeneralizesExcept.applyParameters
            substitution contextValid.range (localSchemeTemplateIds binder)
            generalizes))
      (by
        simpa [applyBinder, applyScheme] using
          (initializerInduction catalog
            (contextValid.localSchemeInitializer binder)))
      (StructuralSubstitution.BinderExtends.applyParameters substitution
        contextValid.exact contextValid.range extension)
  · intro control context expression type expressionType expressionInduction
      catalog contextValid
    exact .expression (expressionInduction catalog contextValid)
  · intro control context assignment operator value assignmentType
      assignmentInduction catalog contextValid
    exact .assignValue (assignmentInduction catalog contextValid)
  · intro control context assignment assignmentType assignmentInduction catalog
      contextValid
    exact .assignBitNot (assignmentInduction catalog contextValid)
  · intro control context catalog contextValid
    exact .nil _ _
  · intro control context middle final item items head tail headInduction
      tailInduction catalog contextValid
    have middleCatalog : SignatureCatalogWellFormed middle.signatures := by
      rw [StructuralSubstitution.ForItemHasType.signatures_eq head]
      exact catalog
    have middleValid :=
      StructuralSubstitution.ForItemHasType.contextSubstitutionValid contextValid
        head
    exact .cons (headInduction catalog contextValid)
      (tailInduction middleCatalog middleValid)
  · intro control context scrutineeType matchCase binders rootArity armContext
      finalContext facts patternType bindersExtend bodyType bodyInduction catalog
      contextValid
    have armCatalog : SignatureCatalogWellFormed armContext.signatures := by
      rw [StructuralSubstitution.BindersExtend.signatures_eq bindersExtend]
      exact catalog
    have armValid := contextValid.afterBinders bindersExtend
    exact .intro
      (StructuralSubstitution.TypedMatchPatternHasType.applyParameters catalog
        contextValid patternType)
      (StructuralSubstitution.BindersExtend.applyParameters substitution
        contextValid.exact contextValid.range bindersExtend)
      (bodyInduction armCatalog armValid)
  · intro control context scrutineeType catalog contextValid
    exact .nil _ _ _
  · intro control context scrutineeType matchCase cases facts caseFacts head tail
      headInduction tailInduction catalog contextValid
    exact .cons (headInduction catalog contextValid)
      (tailInduction catalog contextValid)
  · exact typing
  · exact catalog
  · exact contextValid

/-- Rigid instantiation preserves a complete declaration body, including its
root-shape invariant and completion certificate. -/
theorem BodyHasType.applyParameters
    {substitution : ParameterSubstitution} {source : TypedSource}
    {context : Context} {resultType : Ty} {facts : BodyFacts}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (contextValid : ContextSubstitutionValid substitution context)
    (typing : BodyHasType source context resultType facts) :
    BodyHasType (applyTypedSource substitution source)
      (applyContext substitution context) (substitution.apply resultType)
      (applyBodyFacts substitution facts) := by
  rcases typing with ⟨finalContext, statementsType, noExpressionRoots,
    completes⟩
  refine ⟨applyContext substitution finalContext, ?_, ?_, ?_⟩
  · simpa [applyTypedSource, applyControlContext] using
      (StructuralSubstitution.StatementsHaveType.applyParameters catalog
        contextValid statementsType)
  · intro expression member
    exact noExpressionRoots expression (by
      simpa [applyTypedSource] using member)
  · exact StructuralSubstitution.BodyCompletes.applyParameters substitution
      completes

/-- Static certificate needed by dynamic preservation for an instantiated
declaration body.  It is intentionally independent of the dynamic value and
heap judgments. -/
structure StaticBodyInstanceHasType
    (bodyInstance : Dynamic.BodyInstance) (inputTypes : List Ty)
    (lexicalContext : Context) (facts : BodyFacts) : Prop where
  inputs_extend : MonoBindersExtend bodyInstance.source.owner
    bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext
  body_typed : BodyHasType bodyInstance.source lexicalContext
    bodyInstance.resultType facts

theorem BodyDefinitionHasType.requirementLedger
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    ScopedRequirementLedgerWellFormed
      (declarationContext signatures definition.owner parameters assumptions
        definition.solvedRequirements) definition.source := by
  cases typing
  assumption

theorem BodyDefinitionHasType.sourceOwner
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    definition.source.owner = definition.owner := by
  cases typing
  assumption

theorem BodyDefinitionHasType.callableTypeEq
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    definition.type = .function (Ty.productMany parameterTypes)
      (Ty.productMany returnTypes) := by
  cases typing
  assumption

theorem BodyDefinitionHasType.resultTypeEq
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    definition.resultType = Ty.productMany returnTypes := by
  cases typing
  assumption

theorem BodyDefinitionHasType.graphClosed
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    OccurrenceGraphClosed definition.source := by
  cases typing
  assumption

theorem BodyDefinitionHasType.localIdentityOwnership
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    LocalIdentityOwnership definition.source := by
  cases typing
  assumption

theorem BodyDefinitionHasType.requirementOwnership
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts) :
    RequirementOwnership
      (declarationContext signatures definition.owner parameters assumptions
        definition.solvedRequirements) definition.source := by
  cases typing
  assumption

/-- Conditional declaration-boundary transport.  The only semantic evidence
premise concerns implementation-backed solved requirements; assumption-backed
requirements are transported from their lexical validity at each use.  The
whole-program bridge derives the implementation premise from the declaration's
validated requirement ledger. -/
theorem BodyDefinitionHasType.instantiate_with_context
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (substitution : ParameterSubstitution)
    (catalog : SignatureCatalogWellFormed signatures)
    (contextValid : ContextSubstitutionValid substitution
      (declarationContext signatures definition.owner parameters assumptions
        definition.solvedRequirements))
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
        (applyBodyFacts substitution facts) := by
  cases typing with
  | @intro lexicalContext sourceOwner parameterBinders parameterTypesWellFormed
      returnTypesWellFormed callableTypeEq resultTypeEq returnComptimeEq
      inputNamesEq inputComptimeEq inputsExtend graphClosed localOwnership
      requirementLedger requirementOwnership bodyType bodyAnnotationEq =>
      have lexicalCatalog :
          SignatureCatalogWellFormed lexicalContext.signatures := by
        rw [StructuralSubstitution.MonoBindersExtend.signatures_eq inputsExtend]
        exact catalog
      have lexicalValid := contextValid.afterMonoBinders inputsExtend
      refine ⟨applyContext substitution lexicalContext, ?_, ?_⟩
      · simpa [sourceOwner] using
          (StructuralSubstitution.MonoBindersExtend.applyParameters
            substitution contextValid.exact contextValid.range inputsExtend)
      · rw [resultTypeEq]
        exact StructuralSubstitution.BodyHasType.applyParameters lexicalCatalog
          lexicalValid bodyType

/-- Once the mutually recursive body judgment has been transported, all
declaration-boundary typing data (inputs, lexical context, result and facts)
is transported constructively.  This isolates `BodyHasType` as the sole
remaining high-level obligation. -/
theorem BodyDefinitionHasType.instantiate_of_body
    {signatures : ProgramSignatures}
    {parameters : List TypeParameterId}
    {assumptions : List ProgramPredicate}
    {parameterNames : List String} {parameterTypes : List Ty}
    {parameterComptime : List Bool} {returnTypes : List Ty}
    {returnComptime : Bool} {definition : BodyDefinition} {facts : BodyFacts}
    (substitution : ParameterSubstitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (applyContext substitution
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)) substitution)
    (typing : BodyDefinitionHasType signatures parameters assumptions
      parameterNames parameterTypes parameterComptime returnTypes returnComptime
      definition facts)
    (bodyAfter : ∀ lexicalContext,
      MonoBindersExtend definition.owner
        (declarationContext signatures definition.owner parameters assumptions
          definition.solvedRequirements)
        definition.source.inputs parameterTypes lexicalContext →
      BodyHasType definition.source lexicalContext
        (Ty.productMany returnTypes) facts →
      BodyHasType (applyTypedSource substitution definition.source)
        (applyContext substitution lexicalContext)
        (substitution.apply (Ty.productMany returnTypes))
        (applyBodyFacts substitution facts)) :
    ∃ lexicalContext,
      MonoBindersExtend definition.source.owner
        (applyContext substitution
          (declarationContext signatures definition.owner parameters assumptions
            definition.solvedRequirements))
        (definition.source.inputs.map (applyBinder substitution))
        (parameterTypes.map substitution.apply) lexicalContext ∧
      BodyHasType (applyTypedSource substitution definition.source)
        lexicalContext (substitution.apply definition.resultType)
        (applyBodyFacts substitution facts) := by
  cases typing with
  | @intro lexicalContext sourceOwner parameterBinders parameterTypesWellFormed
      returnTypesWellFormed callableTypeEq resultTypeEq returnComptimeEq
      inputNamesEq inputComptimeEq inputsExtend graphClosed localOwnership
      requirementLedger requirementOwnership bodyType bodyAnnotationEq =>
      refine ⟨applyContext substitution lexicalContext, ?_, ?_⟩
      · simpa [sourceOwner] using
          (StructuralSubstitution.MonoBindersExtend.applyParameters
            substitution exact range inputsExtend)
      · rw [resultTypeEq]
        exact bodyAfter lexicalContext inputsExtend bodyType

end Solcore.SourceSemantics.StructuralSubstitution

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- Flexible substitution on the proof-only control summary retained by the
source typing judgment. -/
def applyControlSummary (substitution : Substitution)
    (summary : ControlSummary) : ControlSummary := {
  fallthrough := summary.fallthrough.map substitution.apply
  mayReturn := summary.mayReturn
  mayBreak := summary.mayBreak
  mayContinue := summary.mayContinue
}

/-- Flexible substitution on the ambient return type of a control context. -/
def applyControlContext (substitution : Substitution)
    (control : ControlContext) : ControlContext := {
  returnType := substitution.apply control.returnType
  loopDepth := control.loopDepth
}

/-- Flexible substitution on the facts produced by one statement. -/
def applyStatementFacts (substitution : Substitution)
    (facts : StatementFacts) : StatementFacts := {
  type := substitution.apply facts.type
  hasValue := facts.hasValue
  sawReturn := facts.sawReturn
  control := applyControlSummary substitution facts.control
}

/-- Flexible substitution on the facts accumulated by a statement body. -/
def applyBodyFacts (substitution : Substitution)
    (facts : BodyFacts) : BodyFacts := {
  type := substitution.apply facts.type
  sawReturn := facts.sawReturn
  control := applyControlSummary substitution facts.control
}

/-- Flexible substitution on the proof-facing expression requirement plan. -/
def applyExpressionRequirementPlan (substitution : Substitution) :
    ExpressionRequirementPlan → ExpressionRequirementPlan
  | .ordinary owned => .ordinary owned
  | .directCall predicates =>
      .directCall (predicates.map
        (TypedTraitResolution.applySubstitution substitution))
  | .indirectCall coercions =>
      .indirectCall (coercions.map
        (CoercionStep.applySubstitution substitution))

/-- Every scheme already retained in a lexical context protects its bound
variables from an outer flexible substitution.  Quantifying over the complete
table keeps the property robust for malformed duplicate scopes as well. -/
def LocalSchemesFreshFor (context : Context)
    (substitution : Substitution) : Prop :=
  ∀ entry, entry ∈ context.locals →
    ∀ metavariable, metavariable ∈ entry.2.quantified →
      metavariable ∉ substitution.domain

namespace LocalSchemesFreshFor

/-- Extend a protected local scope with one more protected scheme. -/
theorem withLocal
    {context : Context} {substitution : Substitution}
    {id : Resolved.LocalId} {scheme : Scheme}
    {requirements : List LocalSchemeRequirement}
    (fresh : LocalSchemesFreshFor context substitution)
    (schemeProtected : ∀ metavariable,
      metavariable ∈ scheme.quantified →
        metavariable ∉ substitution.domain) :
    LocalSchemesFreshFor
      (context.withLocal id scheme requirements) substitution := by
  intro entry member metavariable quantified
  change entry ∈ (id, scheme) :: context.locals at member
  rcases List.mem_cons.mp member with rfl | member
  · exact schemeProtected metavariable quantified
  · exact fresh entry member metavariable quantified

end LocalSchemesFreshFor

/-- Semantic validity of one flexible context closure.  Structural closure
tracks types and context fields; this layer additionally rules out capture by
retained local schemes and supplies the non-structural evidence obligation for
implementation-backed solved requirements. -/
structure ContextSubstitutionValid (substitution : Substitution)
    (closedVariables : List TypeVarId) (source target : Context) : Prop where
  closes : ContextCloses substitution closedVariables source target
  localSchemesFresh : LocalSchemesFreshFor source substitution
  implementationRequirements : ∀ requirement evidence,
    requirement ∈ source.solvedRequirements →
    requirement.evidence = .implementation evidence →
      SolvedRequirementValid target
        (applySolvedRequirement substitution requirement)

@[simp] theorem apply_builtin (substitution : Substitution)
    (builtin : BuiltinType) :
    substitution.apply (.constructor (.builtin builtin)) =
      .constructor (.builtin builtin) := rfl

@[simp] theorem apply_word (substitution : Substitution) :
    substitution.apply Ty.word = Ty.word := rfl

@[simp] theorem apply_integer (substitution : Substitution) :
    substitution.apply Ty.integer = Ty.integer := rfl

@[simp] theorem apply_bool (substitution : Substitution) :
    substitution.apply Ty.bool = Ty.bool := rfl

@[simp] theorem apply_unit (substitution : Substitution) :
    substitution.apply Ty.unit = Ty.unit := rfl

@[simp] theorem apply_function (substitution : Substitution)
    (parameter result : Ty) :
    substitution.apply (.function parameter result) =
      .function (substitution.apply parameter)
        (substitution.apply result) := rfl

@[simp] theorem apply_product (substitution : Substitution)
    (left right : Ty) :
    substitution.apply (.product left right) =
      .product (substitution.apply left) (substitution.apply right) := rfl

@[simp] theorem apply_mapping (substitution : Substitution)
    (key value : Ty) :
    substitution.apply (.mapping key value) =
      .mapping (substitution.apply key) (substitution.apply value) := rfl

@[simp] theorem apply_proxy (substitution : Substitution) (inner : Ty) :
    substitution.apply (.proxy inner) = .proxy (substitution.apply inner) := rfl

@[simp] theorem apply_comptime (substitution : Substitution) (inner : Ty) :
    substitution.apply (.comptime inner) =
      .comptime (substitution.apply inner) := rfl

/-- Flexible substitution distributes through source product spines. -/
theorem apply_productMany (substitution : Substitution) (types : List Ty) :
    substitution.apply (Ty.productMany types) =
      Ty.productMany (types.map substitution.apply) := by
  induction types with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [Ty.productMany, apply_product, List.map_cons]
          rw [induction]
          rfl

/-- Flexible substitution preserves the ordered requirement identities owned
by a coercion path. -/
@[simp] theorem coercionRequirementIds_applySubstitution
    (substitution : Substitution) (steps : List CoercionStep) :
    coercionRequirementIds
        (steps.map (CoercionStep.applySubstitution substitution)) =
      coercionRequirementIds steps := by
  induction steps with
  | nil => rfl
  | cons head tail induction =>
      change (head.applySubstitution substitution).requirements ++
          coercionRequirementIds
            (tail.map (CoercionStep.applySubstitution substitution)) =
        head.requirements ++ coercionRequirementIds tail
      rw [CoercionStep.applySubstitution_requirements, induction]

@[simp] theorem apply_ite (substitution : Substitution)
    (condition : Prop) [Decidable condition] (thenType elseType : Ty) :
    substitution.apply (if condition then thenType else elseType) =
      if condition then substitution.apply thenType
      else substitution.apply elseType := by
  split <;> rfl

@[simp] theorem applyControlContext_enterLoop
    (substitution : Substitution) (control : ControlContext) :
    applyControlContext substitution control.enterLoop =
      (applyControlContext substitution control).enterLoop := by
  cases control
  rfl

@[simp] theorem applyControlSummary_ordinary
    (substitution : Substitution) (type : Ty) :
    applyControlSummary substitution (.ordinary type) =
      .ordinary (substitution.apply type) := by
  rfl

@[simp] theorem applyControlSummary_returned
    (substitution : Substitution) :
    applyControlSummary substitution .returned = .returned := by
  rfl

@[simp] theorem applyControlSummary_breaking
    (substitution : Substitution) :
    applyControlSummary substitution .breaking = .breaking := by
  rfl

@[simp] theorem applyControlSummary_continuing
    (substitution : Substitution) :
    applyControlSummary substitution .continuing = .continuing := by
  rfl

@[simp] theorem applyControlSummary_sequence
    (substitution : Substitution) (head tail : ControlSummary) :
    applyControlSummary substitution (head.sequence tail) =
      (applyControlSummary substitution head).sequence
        (applyControlSummary substitution tail) := by
  cases head with
  | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;>
        simp [applyControlSummary, ControlSummary.sequence,
          ControlSummary.canFallthrough]

@[simp] theorem applyControlSummary_branches
    (substitution : Substitution) (left right : ControlSummary) :
    applyControlSummary substitution (left.branches right) =
      (applyControlSummary substitution left).branches
        (applyControlSummary substitution right) := by
  cases left with
  | mk leftFallthrough leftReturn leftBreak leftContinue =>
      cases right with
      | mk rightFallthrough rightReturn rightBreak rightContinue =>
          cases leftFallthrough <;> cases rightFallthrough <;>
            simp [applyControlSummary, ControlSummary.branches,
              ControlSummary.canFallthrough]

@[simp] theorem applyControlSummary_eraseValue
    (substitution : Substitution) (summary : ControlSummary) :
    applyControlSummary substitution summary.eraseValue =
      (applyControlSummary substitution summary).eraseValue := by
  cases summary with
  | mk fallthrough mayReturn mayBreak mayContinue =>
      cases fallthrough <;>
        simp [applyControlSummary, ControlSummary.eraseValue]

@[simp] theorem applyControlSummary_loop
    (substitution : Substitution) (summary : ControlSummary) :
    applyControlSummary substitution summary.loop =
      (applyControlSummary substitution summary).loop := by
  cases summary
  rfl

@[simp] theorem applyStatementFacts_singleton
    (substitution : Substitution) (facts : StatementFacts) :
    applyBodyFacts substitution (.singleton facts) =
      .singleton (applyStatementFacts substitution facts) := by
  rcases facts with ⟨type, hasValue, sawReturn, control⟩
  cases hasValue <;> cases sawReturn <;>
    simp [applyBodyFacts, applyStatementFacts, BodyFacts.singleton]

@[simp] theorem applyBodyFacts_empty (substitution : Substitution) :
    applyBodyFacts substitution .empty = .empty := by
  rfl

@[simp] theorem applyBodyFacts_cons
    (substitution : Substitution)
    (head : StatementFacts) (tail : BodyFacts) :
    applyBodyFacts substitution (.cons head tail) =
      .cons (applyStatementFacts substitution head)
        (applyBodyFacts substitution tail) := by
  rcases head with ⟨headType, hasValue, headSawReturn, headControl⟩
  rcases tail with ⟨tailType, tailSawReturn, tailControl⟩
  cases headSawReturn <;> cases tailSawReturn <;>
    simp [applyBodyFacts, applyStatementFacts, BodyFacts.cons]

@[simp] theorem allBodiesSawReturn_applyBodyFacts
    (substitution : Substitution) (facts : List BodyFacts) :
    allBodiesSawReturn (facts.map (applyBodyFacts substitution)) =
      allBodiesSawReturn facts := by
  induction facts with
  | nil => rfl
  | cons head tail induction =>
      unfold allBodiesSawReturn at induction ⊢
      simp only [List.map_cons, List.all_cons, applyBodyFacts]
      rw [induction]

theorem mergeBodyControls_applyBodyFacts
    (substitution : Substitution) (facts : List BodyFacts)
    (fallback : Option BodyFacts) :
    mergeBodyControls (facts.map (applyBodyFacts substitution))
        (fallback.map (applyBodyFacts substitution)) =
      (mergeBodyControls facts fallback).map
        (applyControlSummary substitution) := by
  induction facts with
  | nil =>
      cases fallback <;> rfl
  | cons head tail induction =>
      simp only [List.map_cons, mergeBodyControls]
      rw [induction]
      cases merged : mergeBodyControls tail fallback with
      | none => rfl
      | some summary =>
          simp [applyBodyFacts]

theorem BodyCompletes.applySubstitution
    {expected : Ty} {facts : BodyFacts}
    (substitution : Substitution)
    (completes : BodyCompletes expected facts) :
    BodyCompletes (substitution.apply expected)
      (applyBodyFacts substitution facts) := by
  rcases completes with ⟨noBreak, noContinue, completion⟩
  refine ⟨noBreak, noContinue, ?_⟩
  rcases completion with ⟨fallthrough, returned⟩ | fallthrough
  · left
    exact ⟨by simp [applyBodyFacts, applyControlSummary, fallthrough],
      returned⟩
  · right
    simp [applyBodyFacts, applyControlSummary, fallthrough]

@[simp] theorem flatMap_patternRequirements_applySubstitution
    (substitution : Substitution) (cases : List TypedMatchCase) :
    (cases.map (TypedMatchCase.applySubstitution substitution)).flatMap
        (fun matchCase => matchCase.pattern.requirements) =
      cases.flatMap (fun matchCase => matchCase.pattern.requirements) := by
  induction cases with
  | nil => rfl
  | cons head tail induction =>
      simp [TypedMatchCase.applySubstitution,
        TypedMatchPattern.applySubstitution, induction]

@[simp] theorem applySolvedRequirement_id (substitution : Substitution)
    (requirement : SolvedRequirement) :
    (applySolvedRequirement substitution requirement).id = requirement.id := by
  rfl

@[simp] theorem applySolvedRequirement_predicate (substitution : Substitution)
    (requirement : SolvedRequirement) :
    (applySolvedRequirement substitution requirement).predicate =
      TypedTraitResolution.applySubstitution substitution
        requirement.predicate := by
  rfl

theorem applyPredicateEvidence_goal (substitution : Substitution)
    (evidence : PredicateEvidence) :
    (applyPredicateEvidence substitution evidence).goal =
      TypedTraitResolution.applySubstitution substitution evidence.goal := by
  cases evidence with
  | assumption predicate => rfl
  | implementation evidence =>
      cases evidence
      rfl

theorem applySolvedRequirement_goal_alignment (substitution : Substitution)
    (requirement : SolvedRequirement)
    (aligned : requirement.evidence.goal = requirement.predicate) :
    (applySolvedRequirement substitution requirement).evidence.goal =
      (applySolvedRequirement substitution requirement).predicate := by
  change (applyPredicateEvidence substitution requirement.evidence).goal =
    TypedTraitResolution.applySubstitution substitution requirement.predicate
  rw [applyPredicateEvidence_goal, aligned]

/-- A flexible variable outside the substitution domain remains free after
simultaneous substitution. -/
theorem Substitution.mem_freeVariables_apply_of_not_mem_domain
    (substitution : Substitution) {metavariable : TypeVarId} {type : Ty}
    (absent : metavariable ∉ substitution.domain)
    (occurs : metavariable ∈ type.freeVariables) :
    metavariable ∈ (substitution.apply type).freeVariables := by
  induction type with
  | «variable» candidate =>
      simp only [Ty.freeVariables, List.mem_singleton] at occurs
      subst candidate
      have lookup :=
        StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain
          absent
      simp [TypeSystem.Substitution.apply, lookup, Ty.freeVariables]
  | parameter parameter => simp [Ty.freeVariables] at occurs
  | constructor constructor => simp [Ty.freeVariables] at occurs
  | application left right leftInduction rightInduction =>
      simp only [TypeSystem.Substitution.apply]
      rw [mem_freeVariables_application_iff] at occurs ⊢
      rcases occurs with occurs | occurs
      · exact Or.inl (leftInduction occurs)
      · exact Or.inr (rightInduction occurs)
  | function parameter result parameterInduction resultInduction =>
      simp only [TypeSystem.Substitution.apply]
      rw [mem_freeVariables_function_iff] at occurs ⊢
      rcases occurs with occurs | occurs
      · exact Or.inl (parameterInduction occurs)
      · exact Or.inr (resultInduction occurs)
  | product left right leftInduction rightInduction =>
      simp only [TypeSystem.Substitution.apply]
      rw [mem_freeVariables_product_iff] at occurs ⊢
      rcases occurs with occurs | occurs
      · exact Or.inl (leftInduction occurs)
      · exact Or.inr (rightInduction occurs)
  | mapping key value keyInduction valueInduction =>
      simp only [TypeSystem.Substitution.apply]
      rw [mem_freeVariables_mapping_iff] at occurs ⊢
      rcases occurs with occurs | occurs
      · exact Or.inl (keyInduction occurs)
      · exact Or.inr (valueInduction occurs)
  | proxy inner induction =>
      exact induction occurs
  | comptime inner induction =>
      exact induction occurs
  | error => simp [Ty.freeVariables] at occurs

namespace ParameterSubstitution

/-- Apply a flexible substitution to every replacement of a rigid-parameter
substitution while preserving its rigid domain. -/
def mapRange (outer : TypeSystem.Substitution)
    (inner : TypeSystem.ParameterSubstitution) :
    TypeSystem.ParameterSubstitution :=
  inner.map fun entry => (entry.1, outer.apply entry.2)

/-- Flexible range mapping preserves exact rigid-parameter coverage. -/
theorem Exact.mapRange
    {inner : TypeSystem.ParameterSubstitution}
    {parameters : List TypeParameterId}
    (outer : TypeSystem.Substitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact inner parameters) :
    SourceSemantics.ParameterSubstitution.Exact
      (FlexibleSubstitution.ParameterSubstitution.mapRange outer inner)
      parameters := by
  constructor
  · exact exact.parameters_nodup
  · have domainEq :
        SourceSemantics.ParameterSubstitution.domain
            (FlexibleSubstitution.ParameterSubstitution.mapRange outer inner) =
          SourceSemantics.ParameterSubstitution.domain inner := by
      simp [FlexibleSubstitution.ParameterSubstitution.mapRange,
        SourceSemantics.ParameterSubstitution.domain, List.map_map,
        Function.comp_def]
    rw [domainEq]
    exact exact.domain_permutation

end ParameterSubstitution

namespace Substitution

/-- Preserve an inner flexible substitution's exact domain while applying an
outer flexible substitution to every replacement in its range. -/
def mapRange (outer inner : TypeSystem.Substitution) :
    TypeSystem.Substitution :=
  inner.map fun entry => (entry.1, outer.apply entry.2)

/-- Mapping only the range preserves exact ordered domain coverage. -/
theorem ExactSubstitution.mapRange
    {inner : TypeSystem.Substitution} {variables : List TypeVarId}
    (outer : TypeSystem.Substitution)
    (exact : ExactSubstitution inner variables) :
    ExactSubstitution
      (FlexibleSubstitution.Substitution.mapRange outer inner) variables := by
  constructor
  · exact exact.variables_nodup
  · have domainEq :
        (FlexibleSubstitution.Substitution.mapRange outer inner).domain =
          inner.domain := by
      simp [FlexibleSubstitution.Substitution.mapRange,
        TypeSystem.Substitution.domain]
    rw [domainEq]
    exact exact.domain_permutation

private theorem mem_of_lookup?_eq_some
    {substitution : TypeSystem.Substitution}
    {metavariable : TypeVarId} {replacement : Ty}
    (found : substitution.lookup? metavariable = some replacement) :
    (metavariable, replacement) ∈ substitution := by
  induction substitution with
  | nil => simp [TypeSystem.Substitution.lookup?] at found
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      by_cases same : candidate = metavariable
      · subst candidate
        simp [TypeSystem.Substitution.lookup?] at found
        cases found
        simp
      · have tailFound :
            TypeSystem.Substitution.lookup? rest metavariable =
              some replacement := by
          simpa [TypeSystem.Substitution.lookup?, same] using found
        exact List.mem_cons_of_mem _ (induction tailFound)

private theorem exists_lookup?_eq_some_of_mem_domain
    {substitution : TypeSystem.Substitution} {metavariable : TypeVarId}
    (member : metavariable ∈ substitution.domain) :
    ∃ replacement, substitution.lookup? metavariable = some replacement := by
  induction substitution with
  | nil => simp [TypeSystem.Substitution.domain] at member
  | cons entry rest induction =>
      rcases entry with ⟨candidate, candidateReplacement⟩
      simp only [TypeSystem.Substitution.domain, List.map_cons,
        List.mem_cons] at member
      by_cases same : candidate = metavariable
      · exact ⟨candidateReplacement, by
          simp [TypeSystem.Substitution.lookup?, same]⟩
      · rcases member with member | member
        · exact (same member.symm).elim
        · rcases induction member with ⟨replacement, found⟩
          exact ⟨replacement, by
            simpa [TypeSystem.Substitution.lookup?, same] using found⟩

private theorem lookup?_eq_none_iff_not_mem_domain
    (substitution : TypeSystem.Substitution) (metavariable : TypeVarId) :
    substitution.lookup? metavariable = none ↔
      metavariable ∉ substitution.domain := by
  constructor
  · intro missing member
    rcases exists_lookup?_eq_some_of_mem_domain member with ⟨actual, present⟩
    rw [missing] at present
    cases present
  · exact StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain

private def mergeVariables (left right : List TypeVarId) : List TypeVarId :=
  right.foldl (fun variables metavariable =>
    if metavariable ∈ variables then variables
    else variables ++ [metavariable]) left

private theorem filter_mergeVariables (keep : TypeVarId → Bool)
    (left right : List TypeVarId) :
    (mergeVariables left right).filter keep =
      mergeVariables (left.filter keep) (right.filter keep) := by
  induction right generalizing left with
  | nil => simp [mergeVariables]
  | cons head tail induction =>
      change (mergeVariables
          (if head ∈ left then left else left ++ [head]) tail).filter keep =
        mergeVariables (left.filter keep) ((head :: tail).filter keep)
      rw [induction]
      by_cases kept : keep head
      · by_cases present : head ∈ left
        · simp [mergeVariables, kept, present, List.mem_filter.mpr ⟨present, kept⟩]
        · have absent : head ∉ left.filter keep := by
            simp [present]
          simp [mergeVariables, kept, present, absent, List.filter_append]
      · have absent : head ∉ left.filter keep := by
          simp [kept]
        by_cases present : head ∈ left
        · simp [mergeVariables, kept, present]
        · simp [mergeVariables, kept, present, List.filter_append]

private theorem mem_mergeVariables_iff (metavariable : TypeVarId)
    (left right : List TypeVarId) :
    metavariable ∈ mergeVariables left right ↔
      metavariable ∈ left ∨ metavariable ∈ right := by
  induction right generalizing left with
  | nil => simp [mergeVariables]
  | cons head tail induction =>
      change metavariable ∈ mergeVariables
          (if head ∈ left then left else left ++ [head]) tail ↔
        metavariable ∈ left ∨ metavariable ∈ head :: tail
      rw [induction]
      by_cases present : head ∈ left
      · simp only [if_pos present, List.mem_cons]
        constructor
        · rintro (member | member)
          · exact Or.inl member
          · exact Or.inr (Or.inr member)
        · rintro (member | same | member)
          · exact Or.inl member
          · exact Or.inl (by simpa [same] using present)
          · exact Or.inr member
      · simp [present, or_assoc]

private theorem mem_foldl_mergeVariables_iff (metavariable : TypeVarId)
    (initial : List TypeVarId) (types : List Ty) :
    metavariable ∈ types.foldl
        (fun variables type =>
          mergeVariables variables type.freeVariables) initial ↔
      metavariable ∈ initial ∨
        ∃ type, type ∈ types ∧ metavariable ∈ type.freeVariables := by
  induction types generalizing initial with
  | nil => simp
  | cons head tail induction =>
      rw [List.foldl_cons, induction,
        mem_mergeVariables_iff metavariable initial head.freeVariables]
      simp only [List.mem_cons]
      constructor
      · rintro ((member | occurs) | ⟨type, typeMember, typeOccurs⟩)
        · exact Or.inl member
        · exact Or.inr ⟨head, Or.inl rfl, occurs⟩
        · exact Or.inr ⟨type, Or.inr typeMember, typeOccurs⟩
      · rintro (member | ⟨type, typeMember, typeOccurs⟩)
        · exact Or.inl (Or.inl member)
        · rcases typeMember with rfl | typeMember
          · exact Or.inl (Or.inr typeOccurs)
          · exact Or.inr ⟨type, typeMember, typeOccurs⟩

private theorem mem_predicateVariables_iff
    (metavariable : TypeVarId) (predicate : ProgramPredicate) :
    metavariable ∈
        Frontend.TypedTraitResolution.predicateVariables predicate ↔
      metavariable ∈ predicate.subject.freeVariables ∨
        ∃ argument, argument ∈ predicate.arguments ∧
          metavariable ∈ argument.freeVariables := by
  cases predicate with
  | mk trait subject arguments =>
      change metavariable ∈ arguments.foldl
          (fun variables type =>
            mergeVariables variables type.freeVariables)
          subject.freeVariables ↔ _
      exact mem_foldl_mergeVariables_iff metavariable
        subject.freeVariables arguments

/-- A flexible variable outside the substitution domain remains in the
subject/argument collector of a substituted trait predicate. -/
theorem mem_predicateVariables_applySubstitution_of_not_mem_domain
    (substitution : Substitution) {metavariable : TypeVarId}
    {predicate : ProgramPredicate}
    (absent : metavariable ∉ substitution.domain)
    (occurs : metavariable ∈
      Frontend.TypedTraitResolution.predicateVariables predicate) :
    metavariable ∈ Frontend.TypedTraitResolution.predicateVariables
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  rw [mem_predicateVariables_iff] at occurs ⊢
  rcases occurs with subject | ⟨argument, argumentMember, argumentOccurs⟩
  · exact Or.inl
      (Substitution.mem_freeVariables_apply_of_not_mem_domain substitution
        absent subject)
  · exact Or.inr ⟨substitution.apply argument,
      List.mem_map.mpr ⟨argument, argumentMember, rfl⟩,
      Substitution.mem_freeVariables_apply_of_not_mem_domain substitution
        absent argumentOccurs⟩

/-- A ground flexible substitution removes exactly its domain variables while
retaining the stable left-to-right order of every surviving source variable. -/
theorem freeVariables_apply
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (type : Ty) :
    (substitution.apply type).freeVariables =
      type.freeVariables.filter fun metavariable =>
        !(substitution.domain.contains metavariable) := by
  let keep := fun metavariable : TypeVarId =>
    !(substitution.domain.contains metavariable)
  induction type with
  | «variable» candidate =>
      cases found : substitution.lookup? candidate with
      | none =>
          have absent :=
            (lookup?_eq_none_iff_not_mem_domain substitution candidate).mp found
          simp [TypeSystem.Substitution.apply, found, Ty.freeVariables, absent]
      | some replacement =>
          have member := mem_of_lookup?_eq_some found
          have closed :=
            StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil
              (range candidate replacement member)
          have present : candidate ∈ substitution.domain :=
            List.mem_map.mpr ⟨(candidate, replacement), member, rfl⟩
          simp [TypeSystem.Substitution.apply, found, closed, Ty.freeVariables,
            present]
  | parameter parameter => simp [TypeSystem.Substitution.apply, Ty.freeVariables]
  | constructor constructor =>
      simp [TypeSystem.Substitution.apply, Ty.freeVariables]
  | application left right leftInduction rightInduction =>
      simp only [TypeSystem.Substitution.apply]
      change mergeVariables
          (substitution.apply left).freeVariables
          (substitution.apply right).freeVariables =
        (mergeVariables left.freeVariables right.freeVariables).filter keep
      rw [leftInduction, rightInduction, filter_mergeVariables]
  | function parameter result parameterInduction resultInduction =>
      simp only [TypeSystem.Substitution.apply]
      change mergeVariables
          (substitution.apply parameter).freeVariables
          (substitution.apply result).freeVariables =
        (mergeVariables parameter.freeVariables result.freeVariables).filter keep
      rw [parameterInduction, resultInduction, filter_mergeVariables]
  | product left right leftInduction rightInduction =>
      simp only [TypeSystem.Substitution.apply]
      change mergeVariables
          (substitution.apply left).freeVariables
          (substitution.apply right).freeVariables =
        (mergeVariables left.freeVariables right.freeVariables).filter keep
      rw [leftInduction, rightInduction, filter_mergeVariables]
  | mapping key value keyInduction valueInduction =>
      simp only [TypeSystem.Substitution.apply]
      change mergeVariables
          (substitution.apply key).freeVariables
          (substitution.apply value).freeVariables =
        (mergeVariables key.freeVariables value.freeVariables).filter keep
      rw [keyInduction, valueInduction, filter_mergeVariables]
  | proxy inner induction => exact induction
  | comptime inner induction => exact induction
  | error => rfl

/-- Membership form of `freeVariables_apply`: a ground substitution cannot
create a fresh flexible-variable occurrence. -/
theorem mem_freeVariables_apply_iff
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (metavariable : TypeVarId) (type : Ty) :
    metavariable ∈ (substitution.apply type).freeVariables ↔
      metavariable ∈ type.freeVariables ∧
        metavariable ∉ substitution.domain := by
  rw [freeVariables_apply range]
  simp

private theorem foldl_mergeVariables_apply
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (initial : List TypeVarId) (types : List Ty) :
    (types.map substitution.apply).foldl
        (fun variables type => mergeVariables variables type.freeVariables)
        (initial.filter fun metavariable =>
          !(substitution.domain.contains metavariable)) =
      (types.foldl
        (fun variables type => mergeVariables variables type.freeVariables)
        initial).filter fun metavariable =>
          !(substitution.domain.contains metavariable) := by
  induction types generalizing initial with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.foldl_cons]
      rw [freeVariables_apply range, ← filter_mergeVariables]
      exact induction (mergeVariables initial head.freeVariables)

private theorem predicateVariables_apply
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (predicate : ProgramPredicate) :
    Frontend.TypedTraitResolution.predicateVariables
        (TypedTraitResolution.applySubstitution substitution predicate) =
      (Frontend.TypedTraitResolution.predicateVariables predicate).filter
        fun metavariable =>
          !(substitution.domain.contains metavariable) := by
  cases predicate with
  | mk trait subject arguments =>
      change (arguments.map substitution.apply).foldl
          (fun variables type => mergeVariables variables type.freeVariables)
          (substitution.apply subject).freeVariables =
        (arguments.foldl
          (fun variables type => mergeVariables variables type.freeVariables)
          subject.freeVariables).filter fun metavariable =>
            !(substitution.domain.contains metavariable)
      rw [freeVariables_apply range]
      exact foldl_mergeVariables_apply range subject.freeVariables arguments

private theorem without_sublist (substitution : TypeSystem.Substitution)
    (variables : List TypeVarId) :
    List.Sublist (substitution.without variables) substitution := by
  induction variables generalizing substitution with
  | nil => simp [TypeSystem.Substitution.without]
  | cons erasedVariable restVariables ih =>
      change List.Sublist
        ((substitution.erase erasedVariable).without restVariables)
          substitution
      have tailSublist := ih (substitution.erase erasedVariable)
      have erasedSublist :
          List.Sublist (substitution.erase erasedVariable) substitution := by
        change List.Sublist
          (substitution.filter fun entry => entry.1 != erasedVariable)
          substitution
        exact List.filter_sublist
      exact tailSublist.trans erasedSublist

/-- Removing binders preserves lookup at every variable not being removed. -/
theorem lookup?_without_of_not_mem (substitution : TypeSystem.Substitution)
    {variables : List TypeVarId} {metavariable : TypeVarId}
    (absent : metavariable ∉ variables) :
    (substitution.without variables).lookup? metavariable =
      substitution.lookup? metavariable := by
  induction variables generalizing substitution with
  | nil => simp [TypeSystem.Substitution.without]
  | cons erasedVariable restVariables ih =>
      simp only [List.mem_cons, not_or] at absent
      change ((substitution.erase erasedVariable).without restVariables).lookup?
          metavariable = substitution.lookup? metavariable
      rw [ih (substitution.erase erasedVariable) absent.2,
        TypeSystem.Substitution.lookup?_erase_of_ne substitution absent.1]

private theorem erase_eq_self_of_not_mem_domain
    (substitution : TypeSystem.Substitution) (metavariable : TypeVarId)
    (absent : metavariable ∉ substitution.domain) :
    substitution.erase metavariable = substitution := by
  induction substitution with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨candidate, replacement⟩
      simp only [TypeSystem.Substitution.domain, List.map_cons,
        List.mem_cons, not_or] at absent
      have different : candidate ≠ metavariable := fun same =>
        absent.1 same.symm
      have tailEq := induction absent.2
      unfold TypeSystem.Substitution.erase at tailEq ⊢
      simp [different, tailEq]

/-- Restriction by variables disjoint from the domain is the identity. -/
theorem without_eq_self_of_disjoint_domain
    (substitution : TypeSystem.Substitution) (variables : List TypeVarId)
    (disjoint : ∀ metavariable, metavariable ∈ variables →
      metavariable ∉ substitution.domain) :
    substitution.without variables = substitution := by
  induction variables generalizing substitution with
  | nil => rfl
  | cons erasedVariable restVariables ih =>
      have variableAbsent := disjoint erasedVariable (by simp)
      rw [TypeSystem.Substitution.without, List.foldl_cons,
        erase_eq_self_of_not_mem_domain substitution erasedVariable
          variableAbsent]
      apply ih
      intro metavariable member
      exact disjoint metavariable
        (List.mem_cons_of_mem erasedVariable member)

/-- Removing binders filters exactly those binders from the substitution
domain, independently of replacement types and substitution order. -/
theorem mem_domain_without_iff (substitution : TypeSystem.Substitution)
    (variables : List TypeVarId) (metavariable : TypeVarId) :
    metavariable ∈ (substitution.without variables).domain ↔
      metavariable ∈ substitution.domain ∧ metavariable ∉ variables := by
  constructor
  · intro member
    have originalSublist := without_sublist substitution variables
    have domainSublist :
        List.Sublist (substitution.without variables).domain
          substitution.domain := by
      simpa [TypeSystem.Substitution.domain] using
        originalSublist.map Prod.fst
    refine ⟨domainSublist.subset member, ?_⟩
    intro removed
    have lookupMissing :=
      TypeSystem.Substitution.lookup?_without_of_mem substitution removed
    exact ((lookup?_eq_none_iff_not_mem_domain
      (substitution.without variables) metavariable).mp lookupMissing) member
  · rintro ⟨member, absent⟩
    rcases exists_lookup?_eq_some_of_mem_domain member with
      ⟨replacement, found⟩
    have restrictedFound :
        (substitution.without variables).lookup? metavariable =
          some replacement := by
      rw [lookup?_without_of_not_mem substitution absent]
      exact found
    have restrictedMember := mem_of_lookup?_eq_some restrictedFound
    exact List.mem_map.mpr
      ⟨(metavariable, replacement), restrictedMember, rfl⟩

/-- Restriction cannot introduce duplicate substitution-domain binders. -/
theorem domain_without_nodup (substitution : TypeSystem.Substitution)
    (variables : List TypeVarId) (unique : substitution.domain.Nodup) :
    (substitution.without variables).domain.Nodup := by
  have substitutionSublist := without_sublist substitution variables
  have domainSublist :
      List.Sublist (substitution.without variables).domain
        substitution.domain := by
    simpa [TypeSystem.Substitution.domain] using
      substitutionSublist.map Prod.fst
  exact unique.sublist domainSublist

end Substitution

/-- Capture-avoiding restriction preserves ground range well-formedness. -/
theorem SubstitutionRangeWellFormed.without
    {context : Context} {substitution : TypeSystem.Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (variables : List TypeVarId) :
    SubstitutionRangeWellFormed context (substitution.without variables) := by
  intro metavariable replacement member
  apply range metavariable replacement
  exact (Substitution.without_sublist substitution variables).subset member

/-- A flexible substitution may be pushed through the range of an exact
rigid-parameter substitution when the source type has no free flexible
variables. -/
theorem TypeWellScoped.applyFlexible_composeParameters
    {context : Context} {type : Ty}
    (outer : Substitution) (inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellScoped : TypeWellScoped context [] type) :
    outer.apply (inner.apply type) =
      (ParameterSubstitution.mapRange outer inner).apply type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (ParameterSubstitution.mapRange outer inner).apply type)
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        types.map (ParameterSubstitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    simp at bound
  · intro parameter bound _
    obtain ⟨replacement, member, innerLookup⟩ :=
      StructuralSubstitution.ParameterSubstitution.exists_lookup?_eq_some
        innerExact bound
    have mappedMember :
        (parameter, outer.apply replacement) ∈
          ParameterSubstitution.mapRange outer inner :=
      List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
    have mappedLookup :=
      StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
        (ParameterSubstitution.Exact.mapRange outer innerExact).domain_nodup
        mappedMember
    simp [TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [StructuralSubstitution.apply_nominal,
      StructuralSubstitution.applyFlexible_nominal,
      StructuralSubstitution.apply_nominal]
    exact congrArg (fun mapped => Ty.nominal dataType.id mapped)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem TypesWellScoped.applyFlexible_composeParameters
    {context : Context} {types : List Ty}
    (outer : Substitution) (inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellScoped : TypesWellScoped context [] types) :
    (types.map inner.apply).map outer.apply =
      types.map (ParameterSubstitution.mapRange outer inner).apply := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (ParameterSubstitution.mapRange outer inner).apply type)
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        types.map (ParameterSubstitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    simp at bound
  · intro parameter bound _
    obtain ⟨replacement, member, innerLookup⟩ :=
      StructuralSubstitution.ParameterSubstitution.exists_lookup?_eq_some
        innerExact bound
    have mappedMember :
        (parameter, outer.apply replacement) ∈
          ParameterSubstitution.mapRange outer inner :=
      List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
    have mappedLookup :=
      StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
        (ParameterSubstitution.Exact.mapRange outer innerExact).domain_nodup
        mappedMember
    simp [TypeSystem.ParameterSubstitution.apply, innerLookup, mappedLookup]
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    rw [StructuralSubstitution.apply_nominal,
      StructuralSubstitution.applyFlexible_nominal,
      StructuralSubstitution.apply_nominal]
    exact congrArg (fun mapped => Ty.nominal dataType.id mapped)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply,
      TypeSystem.ParameterSubstitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

theorem PredicateWellFormed.applyFlexible_composeParameters
    {context : Context} {predicate : ProgramPredicate}
    (outer : Substitution) (inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellFormed : PredicateWellFormed context predicate) :
    TypedTraitResolution.applySubstitution outer
        (ProgramPredicate.applyParameters inner predicate) =
      ProgramPredicate.applyParameters
        (ParameterSubstitution.mapRange outer inner) predicate := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [TypedTraitResolution.applySubstitution,
        ProgramPredicate.applyParameters]
      congr 1
      · exact TypeWellScoped.applyFlexible_composeParameters outer inner
          innerExact wellFormed.subject.typeWellScoped
      · rw [List.map_map]
        apply List.map_congr_left
        intro argument member
        exact TypeWellScoped.applyFlexible_composeParameters outer inner
          innerExact (wellFormed.arguments argument member).typeWellScoped

theorem PredicatesWellFormed.applyFlexible_composeParameters
    {context : Context} {predicates : List ProgramPredicate}
    (outer : Substitution) (inner : ParameterSubstitution)
    (innerExact : SourceSemantics.ParameterSubstitution.Exact inner
      context.typeParameters)
    (wellFormed : PredicatesWellFormed context predicates) :
    (predicates.map (ProgramPredicate.applyParameters inner)).map
        (TypedTraitResolution.applySubstitution outer) =
      predicates.map (ProgramPredicate.applyParameters
        (ParameterSubstitution.mapRange outer inner)) := by
  induction predicates with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact PredicateWellFormed.applyFlexible_composeParameters outer inner
          innerExact (wellFormed head (by simp))
      · exact induction (fun predicate member =>
          wellFormed predicate (by simp [member]))

theorem ParameterSubstitution.orderedArguments_mapRange
    {inner : ParameterSubstitution} {parameters : List TypeParameterId}
    (outer : Substitution)
    (exact : SourceSemantics.ParameterSubstitution.Exact inner parameters) :
    SourceSemantics.ParameterSubstitution.orderedArguments
        (ParameterSubstitution.mapRange outer inner) parameters =
      (SourceSemantics.ParameterSubstitution.orderedArguments inner
        parameters).map outer.apply := by
  unfold SourceSemantics.ParameterSubstitution.orderedArguments
  rw [List.map_map]
  apply List.map_congr_left
  intro parameter member
  obtain ⟨replacement, pairMember, innerLookup⟩ :=
    StructuralSubstitution.ParameterSubstitution.exists_lookup?_eq_some exact
      member
  have mappedMember :
      (parameter, outer.apply replacement) ∈
        ParameterSubstitution.mapRange outer inner :=
    List.mem_map.mpr ⟨(parameter, replacement), pairMember, rfl⟩
  have mappedLookup :=
    StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
      (ParameterSubstitution.Exact.mapRange outer exact).domain_nodup
      mappedMember
  simp [innerLookup, mappedLookup]

/-- Applying an outer flexible substitution after an exact inner one is
equivalent to mapping the outer action over the inner range and then applying
that mapped substitution to the outer image.  Freshness prevents the outer
substitution from consuming inner binders; ground outer ranges prevent the
inner substitution from capturing variables introduced by an outer
replacement. -/
theorem TypeWellScoped.applyFlexible_compose
    {source target : Context}
    {flexibleVariables substitutedVariables : List TypeVarId}
    {type : Ty}
    (outer inner : Substitution)
    (outerRange : SubstitutionRangeWellFormed target outer)
    (innerExact : ExactSubstitution inner substitutedVariables)
    (outerFresh : ∀ metavariable,
      metavariable ∈ substitutedVariables →
        metavariable ∉ outer.domain)
    (wellScoped : TypeWellScoped source flexibleVariables type) :
    outer.apply (inner.apply type) =
      (Substitution.mapRange outer inner).apply (outer.apply type) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      outer.apply (inner.apply type) =
        (Substitution.mapRange outer inner).apply (outer.apply type))
    (motive_2 := fun types _ =>
      (types.map inner.apply).map outer.apply =
        (types.map outer.apply).map
          (Substitution.mapRange outer inner).apply)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable _
    by_cases substituted : metavariable ∈ substitutedVariables
    · obtain ⟨replacement, member, innerLookup⟩ :=
        StructuralSubstitution.Substitution.exists_lookup?_eq_some innerExact
          substituted
      have mappedMember :
          (metavariable, outer.apply replacement) ∈
            Substitution.mapRange outer inner :=
        List.mem_map.mpr ⟨(metavariable, replacement), member, rfl⟩
      have mappedLookup :=
        StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
          (Substitution.ExactSubstitution.mapRange outer innerExact).domain_nodup
          mappedMember
      have outerLookup :=
        StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain
          (outerFresh metavariable substituted)
      simp [TypeSystem.Substitution.apply, innerLookup, mappedLookup,
        outerLookup]
    · have innerAbsent : metavariable ∉ inner.domain := by
        intro member
        exact substituted ((innerExact.mem_domain_iff metavariable).mp member)
      have mappedExact :=
        Substitution.ExactSubstitution.mapRange outer innerExact
      have mappedAbsent :
          metavariable ∉ (Substitution.mapRange outer inner).domain := by
        intro member
        exact substituted ((mappedExact.mem_domain_iff metavariable).mp member)
      have innerLookup :=
        StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain
          innerAbsent
      have mappedLookup :=
        StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain
          mappedAbsent
      cases outerLookup : outer.lookup? metavariable with
      | none =>
          simp [TypeSystem.Substitution.apply, innerLookup, mappedLookup,
            outerLookup]
      | some replacement =>
          have outerMember := Substitution.mem_of_lookup?_eq_some outerLookup
          have replacementFixed :=
            StructuralSubstitution.TypeWellScoped.applySubstitution_eq_self
              (Substitution.mapRange outer inner)
              (outerRange metavariable replacement outerMember).typeWellScoped
          simp [TypeSystem.Substitution.apply, innerLookup, outerLookup,
            replacementFixed]
  · intro parameter _ _
    rfl
  · intro builtin
    rfl
  · intro dataType arguments _ _ _ argumentsInduction
    simp only [StructuralSubstitution.applyFlexible_nominal]
    exact congrArg (fun mapped => Ty.nominal dataType.id mapped)
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    simp only [TypeSystem.Substitution.apply]
    rw [parameterInduction, resultInduction]
  · intro left right _ _ leftInduction rightInduction
    simp only [TypeSystem.Substitution.apply]
    rw [leftInduction, rightInduction]
  · intro key value _ _ keyInduction valueInduction
    simp only [TypeSystem.Substitution.apply]
    rw [keyInduction, valueInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · intro innerType _ innerInduction
    simp only [TypeSystem.Substitution.apply]
    rw [innerInduction]
  · rfl
  · intro head tail _ _ headInduction tailInduction
    simp only [List.map_cons]
    rw [headInduction, tailInduction]

/-- Flexible range mapping commutes with substitution of every type carried by
an admissible trait predicate. -/
theorem PredicateAdmissible.applyFlexible_compose
    {source target : Context} {predicate : ProgramPredicate}
    {substitutedVariables : List TypeVarId}
    (outer inner : Substitution)
    (outerRange : SubstitutionRangeWellFormed target outer)
    (innerExact : ExactSubstitution inner substitutedVariables)
    (outerFresh : ∀ metavariable,
      metavariable ∈ substitutedVariables →
        metavariable ∉ outer.domain)
    (admissible : PredicateAdmissible source predicate) :
    TypedTraitResolution.applySubstitution outer
        (TypedTraitResolution.applySubstitution inner predicate) =
      TypedTraitResolution.applySubstitution
        (Substitution.mapRange outer inner)
        (TypedTraitResolution.applySubstitution outer predicate) := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [TypedTraitResolution.applySubstitution]
      congr 1
      · exact TypeWellScoped.applyFlexible_compose outer inner outerRange
          innerExact outerFresh admissible.subject.typeWellScoped
      · simp only [List.map_map]
        apply List.map_congr_left
        intro argument member
        exact TypeWellScoped.applyFlexible_compose outer inner outerRange
          innerExact outerFresh
          (admissible.arguments argument member).typeWellScoped

private theorem Scheme.freeVariables_apply
    {context : Context} {substitution : Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (scheme : Scheme) :
    (scheme.apply substitution).freeVariables =
      scheme.freeVariables.filter fun metavariable =>
        !(substitution.domain.contains metavariable) := by
  simp only [Scheme.apply, Scheme.freeVariables]
  rw [Substitution.freeVariables_apply
    (SubstitutionRangeWellFormed.without range scheme.quantified)]
  simp only [List.filter_filter]
  apply List.filter_congr
  intro metavariable _
  by_cases quantified : metavariable ∈ scheme.quantified <;>
    by_cases substituted : metavariable ∈ substitution.domain <;>
      simp [quantified, substituted, Substitution.mem_domain_without_iff]

private theorem localSchemeVariables_apply
    {context : Context} {substitution : Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (locals : Resolved.LocalScope Scheme) :
    (applyLocals substitution locals).flatMap
        (fun entry => entry.2.freeVariables) =
      (locals.flatMap (fun entry => entry.2.freeVariables)).filter
        fun metavariable =>
          !(substitution.domain.contains metavariable) := by
  induction locals with
  | nil => rfl
  | cons entry rest induction =>
      rcases entry with ⟨id, scheme⟩
      change (scheme.apply substitution).freeVariables ++
          (applyLocals substitution rest).flatMap
            (fun entry => entry.2.freeVariables) =
        (scheme.freeVariables ++
          rest.flatMap (fun entry => entry.2.freeVariables)).filter
            fun metavariable =>
              !(substitution.domain.contains metavariable)
      rw [Scheme.freeVariables_apply range, induction, List.filter_append]

private theorem solvedRequirementVariables_apply
    {context : Context} {substitution : Substitution}
    (range : SubstitutionRangeWellFormed context substitution)
    (exemptRequirements : List RequirementId)
    (requirements : List SolvedRequirement) :
    ((requirements.map (applySolvedRequirement substitution)).filter
        fun requirement =>
          !exemptRequirements.contains requirement.id).flatMap
        (fun requirement =>
          TypedTraitResolution.predicateVariables requirement.predicate) =
      ((requirements.filter fun requirement =>
        !exemptRequirements.contains requirement.id).flatMap
          (fun requirement =>
            TypedTraitResolution.predicateVariables
              requirement.predicate)).filter fun metavariable =>
                !(substitution.domain.contains metavariable) := by
  induction requirements with
  | nil => rfl
  | cons requirement rest induction =>
      by_cases exempt : exemptRequirements.contains requirement.id
      · simp [applySolvedRequirement, exempt, induction]
      · simp [applySolvedRequirement, exempt, induction,
          Substitution.predicateVariables_apply range, List.filter_append]

private theorem targetTypeVariables_eq_filter
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context}
    (closes : ContextCloses substitution closedVariables source target) :
    target.typeVariables =
      source.typeVariables.filter fun metavariable =>
        !(substitution.domain.contains metavariable) := by
  have closed_eq :
      closedVariables.filter (fun metavariable =>
        !(substitution.domain.contains metavariable)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro metavariable member
    simp [((closes.exact.mem_domain_iff metavariable).mpr member)]
  have retained_eq :
      target.typeVariables.filter (fun metavariable =>
        !(substitution.domain.contains metavariable)) =
        target.typeVariables := by
    apply List.filter_eq_self.mpr
    intro metavariable member
    simp [closes.retained_fresh metavariable member]
  rw [closes.variables_eq, List.filter_append, closed_eq, retained_eq]
  rfl

private theorem generalizationBlockedVariablesExcept_applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (exemptRequirements : List RequirementId) :
    GeneralizationBlockedVariablesExcept target exemptRequirements =
      (GeneralizationBlockedVariablesExcept source exemptRequirements).filter
        fun metavariable =>
          !(substitution.domain.contains metavariable) := by
  have locals_eq : target.locals =
      applyLocals substitution source.locals := by
    rw [← closes.target_eq]
    rfl
  have solvedRequirements_eq : target.solvedRequirements =
      source.solvedRequirements.map
        (applySolvedRequirement substitution) := by
    rw [← closes.target_eq]
    rfl
  unfold GeneralizationBlockedVariablesExcept
  rw [targetTypeVariables_eq_filter closes, locals_eq,
    solvedRequirements_eq, localSchemeVariables_apply closes.range,
    solvedRequirementVariables_apply closes.range]
  simp [List.filter_append]

private theorem filter_unblocked_after_domain
    (variables blocked domain : List TypeVarId)
    (domain_blocked : ∀ metavariable, metavariable ∈ domain →
      metavariable ∈ blocked) :
    (variables.filter fun metavariable =>
        !(domain.contains metavariable)).filter (fun metavariable =>
          !((blocked.filter fun candidate =>
            !(domain.contains candidate)).contains metavariable)) =
      variables.filter fun metavariable =>
        !(blocked.contains metavariable) := by
  simp only [List.filter_filter]
  apply List.filter_congr
  intro metavariable _
  by_cases substituted : metavariable ∈ domain
  · have blockedMember := domain_blocked metavariable substituted
    simp [substituted, blockedMember]
  · simp [substituted]

/-- Simultaneous flexible substitution transports a scoped type when every
replacement is closed in the target context and every untouched source
variable remains in the target scope. -/
theorem TypeWellScoped.applySubstitution
    {substitution : Substitution} {source target : Context}
    {sourceVariables targetVariables : List TypeVarId} {type : Ty}
    (domain_nodup : substitution.domain.Nodup)
    (range : SubstitutionRangeWellFormed target substitution)
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq :
      target.currentDeclaration = source.currentDeclaration)
    (kept : ∀ metavariable, metavariable ∈ sourceVariables →
      metavariable ∉ substitution.domain →
        metavariable ∈ targetVariables)
    (wellScoped : TypeWellScoped source sourceVariables type) :
    TypeWellScoped target targetVariables (substitution.apply type) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ =>
      TypeWellScoped target targetVariables (substitution.apply type))
    (motive_2 := fun types _ =>
      TypesWellScoped target targetVariables
        (types.map substitution.apply))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    by_cases member : metavariable ∈ substitution.domain
    · rcases List.mem_map.mp member with ⟨entry, entryMember, keyEq⟩
      rcases entry with ⟨candidate, replacement⟩
      simp only at keyEq
      subst candidate
      have lookup :=
        StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
          domain_nodup entryMember
      simp only [TypeSystem.Substitution.apply, lookup, Option.getD_some]
      exact StructuralSubstitution.TypeWellScoped.weakenFlexible
        (fun candidateVariable impossible => by simp at impossible)
        (range metavariable replacement entryMember).typeWellScoped
    · have lookup :=
        StructuralSubstitution.Substitution.lookup?_eq_none_of_not_mem_domain
          member
      simp only [TypeSystem.Substitution.apply, lookup, Option.getD_none]
      exact .variable (kept metavariable bound member)
  · intro parameter bound owned
    exact .parameter (by simpa [parameters_eq] using bound)
      (by simpa [declaration_eq] using owned)
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    rw [StructuralSubstitution.applyFlexible_nominal]
    exact .nominal dataType (arguments.map substitution.apply)
      (by simpa [signatures_eq] using cataloged)
      (by simpa using arity) argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

/-- List-valued companion to `TypeWellScoped.applySubstitution`. -/
theorem TypesWellScoped.applySubstitution
    {substitution : Substitution} {source target : Context}
    {sourceVariables targetVariables : List TypeVarId} {types : List Ty}
    (domain_nodup : substitution.domain.Nodup)
    (range : SubstitutionRangeWellFormed target substitution)
    (signatures_eq : target.signatures = source.signatures)
    (parameters_eq : target.typeParameters = source.typeParameters)
    (declaration_eq :
      target.currentDeclaration = source.currentDeclaration)
    (kept : ∀ metavariable, metavariable ∈ sourceVariables →
      metavariable ∉ substitution.domain →
        metavariable ∈ targetVariables)
    (wellScoped : TypesWellScoped source sourceVariables types) :
    TypesWellScoped target targetVariables (types.map substitution.apply) := by
  let rec go {types : List Ty}
      (wellScoped : TypesWellScoped source sourceVariables types) :
      TypesWellScoped target targetVariables
        (types.map substitution.apply) :=
    match wellScoped with
    | .nil => .nil
    | .cons headWellScoped tailWellScoped =>
        .cons
          (TypeWellScoped.applySubstitution domain_nodup range signatures_eq
            parameters_eq declaration_eq kept headWellScoped)
          (go tailWellScoped)
  exact go wellScoped

/-- Restricting a substitution before applying a scheme is idempotent because
`Scheme.apply` itself protects the same quantified variables. -/
@[simp] theorem Scheme.apply_without_quantified
    (substitution : Substitution) (scheme : Scheme) :
    scheme.apply (substitution.without scheme.quantified) =
      scheme.apply substitution := by
  have disjoint : ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∉ (substitution.without scheme.quantified).domain := by
    intro metavariable quantified domainMember
    have retained := (Substitution.mem_domain_without_iff substitution
      scheme.quantified metavariable).mp domainMember
    exact retained.2 quantified
  have idempotent := Substitution.without_eq_self_of_disjoint_domain
    (substitution.without scheme.quantified) scheme.quantified disjoint
  simp only [TypeSystem.Scheme.apply]
  rw [idempotent]

@[simp] theorem applyTypedBinder_id (substitution : Substitution)
    (binder : TypedBinder) :
    (binder.applySubstitution substitution).id = binder.id := by
  rfl

@[simp] theorem applyLocalSchemeRequirement_templateRequirement
    (substitution : Substitution) (requirement : LocalSchemeRequirement) :
    (requirement.applySubstitution substitution).templateRequirement =
      requirement.templateRequirement := by
  rfl

@[simp] theorem applyTypedBinder_scheme (substitution : Substitution)
    (binder : TypedBinder) :
    (binder.applySubstitution substitution).scheme =
      binder.scheme.apply substitution := by
  simp [TypedBinder.applySubstitution]

@[simp] theorem applyTypedBinder_scheme_quantified
    (substitution : Substitution) (binder : TypedBinder) :
    (binder.applySubstitution substitution).scheme.quantified =
      binder.scheme.quantified := by
  simp

@[simp] theorem applyTypedBinder_schemeRequirements
    (substitution : Substitution) (binder : TypedBinder) :
    (binder.applySubstitution substitution).schemeRequirements =
      binder.schemeRequirements.map
        (LocalSchemeRequirement.applySubstitution
          (substitution.without binder.scheme.quantified)) := by
  rfl

/-- Flexible substitution changes qualified predicates but preserves their
stable template requirement identities. -/
@[simp] theorem localSchemeTemplateIds_applySubstitution
    (substitution : Substitution) (binder : TypedBinder) :
    localSchemeTemplateIds (binder.applySubstitution substitution) =
      localSchemeTemplateIds binder := by
  simp [localSchemeTemplateIds, TypedBinder.applySubstitution,
    LocalSchemeRequirement.applySubstitution, List.map_map,
    Function.comp_def]

@[simp] theorem patternInstructionBinderIds_applySubstitution
    (substitution : Substitution)
    (instructions : List MatchPatternInstruction) :
    patternInstructionBinderIds
        (instructions.map
          (MatchPatternInstruction.applySubstitution substitution)) =
      patternInstructionBinderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest induction =>
      cases instruction <;>
        simpa [patternInstructionBinderIds,
          MatchPatternInstruction.applySubstitution,
          TypedBinder.applySubstitution] using induction

@[simp] theorem patternBinderIds_applySubstitution
    (substitution : Substitution) (pattern : TypedMatchPattern) :
    patternBinderIds (pattern.applySubstitution substitution) =
      patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
      cases resolution <;>
        simp [patternBinderIds, TypedMatchPattern.applySubstitution,
          MatchPatternResolution.applySubstitution,
          TypedBinder.applySubstitution]

@[simp] theorem forItemDefinedLocalIds_applySubstitution
    (substitution : Substitution) (item : ForItemForm) :
    forItemDefinedLocalIds (item.applySubstitution substitution) =
      forItemDefinedLocalIds item := by
  cases item <;> rfl

@[simp] theorem expressionDefinedLocalIds_applySubstitution
    (substitution : Substitution) (form : ExpressionForm) :
    expressionDefinedLocalIds (form.applySubstitution substitution) =
      expressionDefinedLocalIds form := by
  cases form <;>
    simp [expressionDefinedLocalIds, ExpressionForm.applySubstitution,
      TypedBinder.applySubstitution, List.map_map, Function.comp_def]

@[simp] theorem statementDefinedLocalIds_applySubstitution
    (substitution : Substitution) (form : StatementForm) :
    statementDefinedLocalIds (form.applySubstitution substitution) =
      statementDefinedLocalIds form := by
  cases form <;>
    simp [statementDefinedLocalIds, StatementForm.applySubstitution,
      MatchResolution.applySubstitution, TypedMatchCase.applySubstitution,
      TypedBinder.applySubstitution, List.flatMap_map]

@[simp] theorem nodeDefinedLocalIds_applySubstitution
    (substitution : Substitution) (node : Node) :
    (match node.applySubstitution substitution with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) =
    (match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) := by
  cases node <;>
    simp [Node.applySubstitution, ExpressionNode.applySubstitution,
      StatementNode.applySubstitution]

@[simp] theorem flatMap_definedLocalIds_applySubstitution
    (substitution : Substitution) (nodes : List Node) :
    (nodes.map (Node.applySubstitution substitution)).flatMap (fun node =>
      match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) =
    nodes.flatMap (fun node =>
      match node with
      | .expression expression => expressionDefinedLocalIds expression.form
      | .statement statement => statementDefinedLocalIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction => simp [induction]

/-- Closing flexible types preserves every source-owned local identity. -/
@[simp] theorem definedLocalIds_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    definedLocalIds (source.applySubstitution substitution) =
      definedLocalIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      change
        ((inputs.map (TypedBinder.applySubstitution substitution)).map
            (fun binder => binder.id)) ++
            ((nodes.map (Node.applySubstitution substitution)).flatMap fun node =>
              match node with
              | .expression expression =>
                  expressionDefinedLocalIds expression.form
              | .statement statement =>
                  statementDefinedLocalIds statement.form) =
          (inputs.map (fun binder => binder.id)) ++
            (nodes.flatMap fun node =>
              match node with
              | .expression expression =>
                  expressionDefinedLocalIds expression.form
              | .statement statement =>
                  statementDefinedLocalIds statement.form)
      rw [flatMap_definedLocalIds_applySubstitution]
      simp [List.map_map, Function.comp_def]

/-- Flexible type closure cannot change declaration ownership or uniqueness
of stable local identities. -/
theorem LocalIdentityOwnership.applySubstitution
    (substitution : Substitution) {source : TypedSource}
    (ownership : LocalIdentityOwnership source) :
    LocalIdentityOwnership (source.applySubstitution substitution) := by
  constructor
  · simpa using ownership.unique
  · intro id member
    simpa using ownership.owned id (by simpa using member)

/-- Flexible substitution acts on one initialized local while retaining its
initializer occurrence. -/
def applyInitializedLetBinding (substitution : Substitution)
    (binding : InitializedLetBinding) : InitializedLetBinding := {
  binder := binding.binder.applySubstitution substitution
  initializer := binding.initializer
}

/-- Apply the capture-avoiding substitution of a generalized binder to one
of its exact qualified-requirement owners. -/
def applyLocalSchemeTemplateOwner (substitution : Substitution)
    (owner : LocalSchemeTemplateOwner) : LocalSchemeTemplateOwner := {
  binder := owner.binder.applySubstitution substitution
  initializer := owner.initializer
  requirement := owner.requirement.applySubstitution
    (substitution.without owner.binder.scheme.quantified)
}

/-- A template ledger row uses the same binder-local restriction as its
source owner. -/
def applyLocalSchemeTemplateRow (substitution : Substitution)
    (owner : LocalSchemeTemplateOwner)
    (row : SolvedRequirement) : SolvedRequirement :=
  applySolvedRequirement
    (substitution.without owner.binder.scheme.quantified) row

@[simp] theorem forItemInitializedLetBindings_applySubstitution
    (substitution : Substitution) (item : ForItemForm) :
    forItemInitializedLetBindings (item.applySubstitution substitution) =
      (forItemInitializedLetBindings item).map
        (applyInitializedLetBinding substitution) := by
  cases item with
  | letDecl binder initializer => cases initializer <;> rfl
  | expression expression => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl

@[simp] theorem statementInitializedLetBindings_applySubstitution
    (substitution : Substitution) (form : StatementForm) :
    statementInitializedLetBindings (form.applySubstitution substitution) =
      (statementInitializedLetBindings form).map
        (applyInitializedLetBinding substitution) := by
  cases form with
  | letDecl binder initializer => cases initializer <;> rfl
  | returnStmt value => rfl
  | expression expression trailingSemicolon => rfl
  | assignValue assignment operator value => rfl
  | assignBitNot assignment => rfl
  | ifThen condition thenBody elseBody => rfl
  | block body => rfl
  | matchWith resolution => rfl
  | forLoop initializer condition post body =>
      simp [statementInitializedLetBindings, StatementForm.applySubstitution,
        List.flatMap_map, List.map_flatMap]
  | whileLoop condition body => rfl
  | breakStmt => rfl
  | continueStmt => rfl

@[simp] theorem nodeInitializedLetBindings_applySubstitution
    (substitution : Substitution) (node : Node) :
    (match node.applySubstitution substitution with
      | .expression _ => []
      | .statement statement =>
          statementInitializedLetBindings statement.form) =
    (match node with
      | .expression _ => []
      | .statement statement =>
          statementInitializedLetBindings statement.form).map
        (applyInitializedLetBinding substitution) := by
  cases node <;>
    simp [Node.applySubstitution, StatementNode.applySubstitution]

@[simp] theorem initializedLetBindings_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    initializedLetBindings (source.applySubstitution substitution) =
      (initializedLetBindings source).map
        (applyInitializedLetBinding substitution) := by
  cases source with
  | mk owner inputs roots nodes =>
      simp only [initializedLetBindings, TypedSource.applySubstitution,
        List.flatMap_map, List.map_flatMap]
      induction nodes with
      | nil => rfl
      | cons node nodes induction =>
          simp only [List.flatMap_cons]
          calc
            _ = (match node with
                  | .expression _ => []
                  | .statement statement =>
                      statementInitializedLetBindings statement.form).map
                    (applyInitializedLetBinding substitution) ++
                List.flatMap
                  (fun node =>
                    match node.applySubstitution substitution with
                    | .expression _ => []
                    | .statement statement =>
                        statementInitializedLetBindings statement.form)
                  nodes := congrArg
                    (fun head => head ++ List.flatMap
                      (fun node =>
                        match node.applySubstitution substitution with
                        | .expression _ => []
                        | .statement statement =>
                            statementInitializedLetBindings statement.form)
                      nodes)
                    (nodeInitializedLetBindings_applySubstitution
                      substitution node)
            _ = _ := congrArg
              (fun tail =>
                (match node with
                  | .expression _ => []
                  | .statement statement =>
                      statementInitializedLetBindings statement.form).map
                    (applyInitializedLetBinding substitution) ++ tail)
              induction

@[simp] theorem templateOwners_applyInitializedLetBinding
    (substitution : Substitution) (binding : InitializedLetBinding) :
    InitializedLetBinding.templateOwners
        (applyInitializedLetBinding substitution binding) =
      binding.templateOwners.map
        (applyLocalSchemeTemplateOwner substitution) := by
  simp [InitializedLetBinding.templateOwners, applyInitializedLetBinding,
    applyLocalSchemeTemplateOwner, TypedBinder.applySubstitution,
    List.map_map, Function.comp_def]

@[simp] theorem localSchemeTemplateOwners_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    localSchemeTemplateOwners (source.applySubstitution substitution) =
      (localSchemeTemplateOwners source).map
        (applyLocalSchemeTemplateOwner substitution) := by
  simp [localSchemeTemplateOwners, List.flatMap_map, List.map_flatMap]

@[simp] theorem applyLocalSchemeTemplateOwner_templateRequirement
    (substitution : Substitution) (owner : LocalSchemeTemplateOwner) :
    (applyLocalSchemeTemplateOwner substitution owner).requirement.templateRequirement =
      owner.requirement.templateRequirement := by
  rfl

/-- Flexible substitution preserves the ordered inventory of qualified-local
template identities. -/
@[simp] theorem sourceLocalSchemeTemplateIds_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    sourceLocalSchemeTemplateIds (source.applySubstitution substitution) =
      sourceLocalSchemeTemplateIds source := by
  simp [sourceLocalSchemeTemplateIds, List.map_map, Function.comp_def]

theorem ContainsLocalSchemeTemplate.applySubstitution
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    (substitution : Substitution)
    (contains : ContainsLocalSchemeTemplate source owner) :
    ContainsLocalSchemeTemplate (source.applySubstitution substitution)
      (applyLocalSchemeTemplateOwner substitution owner) := by
  unfold ContainsLocalSchemeTemplate at contains ⊢
  rw [localSchemeTemplateOwners_applySubstitution]
  exact List.mem_map.mpr ⟨owner, contains, rfl⟩

theorem LocalSchemeTemplateOwnership.applySubstitution
    (substitution : Substitution) {source : TypedSource}
    (ownership : LocalSchemeTemplateOwnership source) :
    LocalSchemeTemplateOwnership
      (source.applySubstitution substitution) := by
  constructor
  simpa using ownership.ids_unique

theorem InReflexiveSubtree.applySubstitution
    {source : TypedSource} {root occurrence : NodeId}
    (substitution : Substitution)
    (scope : InReflexiveSubtree source root occurrence) :
    InReflexiveSubtree (source.applySubstitution substitution)
      root occurrence := by
  rcases scope with rootEq | descends
  · exact Or.inl rootEq
  · exact Or.inr
      (FlexibleSubstitution.descends_applySubstitution substitution descends)

theorem InInitializedLetSubtree.applySubstitution
    {source : TypedSource} {binding : InitializedLetBinding}
    {occurrence : NodeId} (substitution : Substitution)
    (scope : InInitializedLetSubtree source binding occurrence) :
    InInitializedLetSubtree (source.applySubstitution substitution)
      (applyInitializedLetBinding substitution binding) occurrence := by
  exact ⟨by
    rw [initializedLetBindings_applySubstitution]
    exact List.mem_map.mpr ⟨binding, scope.1, rfl⟩,
    FlexibleSubstitution.InReflexiveSubtree.applySubstitution substitution
      scope.2⟩

theorem LocalSchemeTemplateOwner.Scopes.applySubstitution
    {source : TypedSource} {owner : LocalSchemeTemplateOwner}
    {occurrence : NodeId} (substitution : Substitution)
    (scope : owner.Scopes source occurrence) :
    (applyLocalSchemeTemplateOwner substitution owner).Scopes
      (source.applySubstitution substitution) occurrence := by
  exact ⟨FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      substitution scope.1,
    FlexibleSubstitution.InReflexiveSubtree.applySubstitution substitution
      scope.2⟩

/-- Exact template-row ownership transports with the capture-avoiding
substitution selected by its source owner. -/
theorem LocalSchemeTemplateRowOwned.applySubstitutionForOwner
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : Substitution) (owner : LocalSchemeTemplateOwner)
    (contains : ContainsLocalSchemeTemplate source owner)
    (idEq : row.id = owner.requirement.templateRequirement)
    (predicateEq : row.predicate = owner.requirement.predicate)
    (evidenceEq : row.evidence =
      .assumption owner.requirement.predicate) :
    LocalSchemeTemplateRowOwned (source.applySubstitution substitution)
      (applyLocalSchemeTemplateRow substitution owner row) := by
  refine .intro (applyLocalSchemeTemplateOwner substitution owner)
    (FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      substitution contains) ?_ ?_ ?_
  · simpa [applyLocalSchemeTemplateRow] using idEq
  · simpa [applyLocalSchemeTemplateRow, applySolvedRequirement,
      applyLocalSchemeTemplateOwner,
      LocalSchemeRequirement.applySubstitution] using congrArg
        (TypedTraitResolution.applySubstitution
          (substitution.without owner.binder.scheme.quantified)) predicateEq
  · simpa [applyLocalSchemeTemplateRow, applySolvedRequirement,
      applyLocalSchemeTemplateOwner,
      LocalSchemeRequirement.applySubstitution, applyPredicateEvidence] using
        congrArg (applyPredicateEvidence
          (substitution.without owner.binder.scheme.quantified)) evidenceEq

/-- Every owned template row has a uniquely determined owner-local transport;
the existential exposes that owner because capture avoidance depends on its
quantified variables. -/
theorem LocalSchemeTemplateRowOwned.applySubstitution
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : Substitution)
    (owned : LocalSchemeTemplateRowOwned source row) :
    ∃ owner, ContainsLocalSchemeTemplate source owner ∧
      LocalSchemeTemplateRowOwned (source.applySubstitution substitution)
        (applyLocalSchemeTemplateRow substitution owner row) := by
  cases owned with
  | intro owner contains idEq predicateEq evidenceEq =>
      exact ⟨owner, contains,
        LocalSchemeTemplateRowOwned.applySubstitutionForOwner substitution
          owner contains idEq predicateEq evidenceEq⟩

@[simp] theorem forItemPrimaryRequirementIds_applySubstitution
    (substitution : Substitution) (item : ForItemForm) :
    forItemPrimaryRequirementIds (item.applySubstitution substitution) =
      forItemPrimaryRequirementIds item := by
  cases item <;>
    simp [forItemPrimaryRequirementIds, ForItemForm.applySubstitution,
      AssignmentResolution.applySubstitution]

@[simp] theorem statementPrimaryRequirementIds_applySubstitution
    (substitution : Substitution) (form : StatementForm) :
    statementPrimaryRequirementIds (form.applySubstitution substitution) =
      statementPrimaryRequirementIds form := by
  cases form <;>
    simp [statementPrimaryRequirementIds, StatementForm.applySubstitution,
      AssignmentResolution.applySubstitution, MatchResolution.applySubstitution,
      TypedMatchCase.applySubstitution, TypedMatchPattern.applySubstitution,
      List.flatMap_map]

@[simp] theorem nodePrimaryRequirementIds_applySubstitution
    (substitution : Substitution) (node : Node) :
    (match node.applySubstitution substitution with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) =
    (match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) := by
  cases node <;>
    simp [Node.applySubstitution, ExpressionNode.applySubstitution,
      StatementNode.applySubstitution]

@[simp] theorem flatMap_primaryRequirementIds_applySubstitution
    (substitution : Substitution) (nodes : List Node) :
    (nodes.map (Node.applySubstitution substitution)).flatMap (fun node =>
      match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) =
    nodes.flatMap (fun node =>
      match node with
      | .expression expression => expression.requirements
      | .statement statement => statementPrimaryRequirementIds statement.form) := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction => simp [induction]

/-- Flexible substitution preserves the ordered primary requirement ledger
attached to the source graph. -/
@[simp] theorem primaryRequirementIds_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    primaryRequirementIds (source.applySubstitution substitution) =
      primaryRequirementIds source := by
  cases source with
  | mk owner inputs roots nodes =>
      exact flatMap_primaryRequirementIds_applySubstitution substitution nodes

@[simp] theorem expressionPrimaryRequirementOccurrences_applySubstitution
    (substitution : Substitution) (expression : ExpressionNode) :
    expressionPrimaryRequirementOccurrences
        (expression.applySubstitution substitution) =
      expressionPrimaryRequirementOccurrences expression := by
  simp [expressionPrimaryRequirementOccurrences,
    ExpressionNode.applySubstitution]

@[simp] theorem statementPrimaryRequirementOccurrences_applySubstitution
    (substitution : Substitution) (statement : StatementNode) :
    statementPrimaryRequirementOccurrences
        (statement.applySubstitution substitution) =
      statementPrimaryRequirementOccurrences statement := by
  simp [statementPrimaryRequirementOccurrences,
    StatementNode.applySubstitution]

@[simp] theorem nodePrimaryRequirementOccurrences_applySubstitution
    (substitution : Substitution) (node : Node) :
    nodePrimaryRequirementOccurrences (node.applySubstitution substitution) =
      nodePrimaryRequirementOccurrences node := by
  cases node <;>
    simp [nodePrimaryRequirementOccurrences, Node.applySubstitution]

@[simp] theorem flatMap_primaryRequirementOccurrences_applySubstitution
    (substitution : Substitution) (nodes : List Node) :
    (nodes.map (Node.applySubstitution substitution)).flatMap
        nodePrimaryRequirementOccurrences =
      nodes.flatMap nodePrimaryRequirementOccurrences := by
  induction nodes with
  | nil => rfl
  | cons node nodes induction => simp [induction]

/-- Flexible substitution preserves each requirement's exact primary source
occurrence. -/
@[simp] theorem primaryRequirementOccurrences_applySubstitution
    (substitution : Substitution) (source : TypedSource) :
    primaryRequirementOccurrences (source.applySubstitution substitution) =
      primaryRequirementOccurrences source := by
  cases source with
  | mk owner inputs roots nodes =>
      exact flatMap_primaryRequirementOccurrences_applySubstitution
        substitution nodes

@[simp] theorem primaryRequirementOccursAt_applySubstitution
    (substitution : Substitution) (source : TypedSource)
    (occurrence : NodeId) (requirement : RequirementId) :
    PrimaryRequirementOccursAt (source.applySubstitution substitution)
        occurrence requirement ↔
      PrimaryRequirementOccursAt source occurrence requirement := by
  simp [PrimaryRequirementOccursAt]

/-- Exact template-row scope transports with the capture-avoiding
substitution selected by its source owner. -/
theorem LocalSchemeTemplateRowScoped.applySubstitutionForOwner
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : Substitution) (owner : LocalSchemeTemplateOwner)
    (contains : ContainsLocalSchemeTemplate source owner)
    (idEq : row.id = owner.requirement.templateRequirement)
    (predicateEq : row.predicate = owner.requirement.predicate)
    (evidenceEq : row.evidence =
      .assumption owner.requirement.predicate)
    (occurrence : NodeId)
    (occurs : PrimaryRequirementOccursAt source occurrence row.id)
    (scope : owner.Scopes source occurrence) :
    LocalSchemeTemplateRowScoped (source.applySubstitution substitution)
      (applyLocalSchemeTemplateRow substitution owner row) := by
  refine .intro (applyLocalSchemeTemplateOwner substitution owner)
    (FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
      substitution contains) ?_ ?_ ?_ occurrence ?_ ?_
  · simpa [applyLocalSchemeTemplateRow] using idEq
  · simpa [applyLocalSchemeTemplateRow, applySolvedRequirement,
      applyLocalSchemeTemplateOwner,
      LocalSchemeRequirement.applySubstitution] using congrArg
        (TypedTraitResolution.applySubstitution
          (substitution.without owner.binder.scheme.quantified)) predicateEq
  · simpa [applyLocalSchemeTemplateRow, applySolvedRequirement,
      applyLocalSchemeTemplateOwner,
      LocalSchemeRequirement.applySubstitution, applyPredicateEvidence] using
        congrArg (applyPredicateEvidence
          (substitution.without owner.binder.scheme.quantified)) evidenceEq
  · simpa [applyLocalSchemeTemplateRow] using
      (primaryRequirementOccursAt_applySubstitution substitution source
        occurrence row.id).mpr occurs
  · exact LocalSchemeTemplateOwner.Scopes.applySubstitution substitution scope

/-- Every scoped template row has an owner-local transport with the same
primary occurrence and initializer subtree. -/
theorem LocalSchemeTemplateRowScoped.applySubstitution
    {source : TypedSource} {row : SolvedRequirement}
    (substitution : Substitution)
    (rowScoped : LocalSchemeTemplateRowScoped source row) :
    ∃ owner, ContainsLocalSchemeTemplate source owner ∧
      LocalSchemeTemplateRowScoped (source.applySubstitution substitution)
        (applyLocalSchemeTemplateRow substitution owner row) := by
  cases rowScoped with
  | intro owner contains idEq predicateEq evidenceEq occurrence occurs scope =>
      exact ⟨owner, contains,
        LocalSchemeTemplateRowScoped.applySubstitutionForOwner substitution
          owner contains idEq predicateEq evidenceEq occurrence occurs scope⟩

/-- Closing flexible types preserves exact primary-to-ledger requirement
ownership because neither side changes stable requirement identities. -/
theorem RequirementOwnership.applySubstitution
    (substitution : Substitution) {context : Context}
    {source : TypedSource}
    (ownership : RequirementOwnership context source) :
    RequirementOwnership (closeContext substitution context)
      (source.applySubstitution substitution) := by
  constructor
  · simpa using ownership.primary_unique
  · simpa [closeContext, applyContext, applySolvedRequirement, List.map_map,
      Function.comp_def] using ownership.ledger_exact

@[simp] theorem applyContext_signatures (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).signatures =
      context.signatures := by
  rfl

@[simp] theorem applyContext_currentDeclaration (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).currentDeclaration =
      context.currentDeclaration := by
  rfl

@[simp] theorem applyContext_typeParameters (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).typeParameters =
      context.typeParameters := by
  rfl

@[simp] theorem applyContext_typeVariables (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).typeVariables =
      retainedVariables := by
  rfl

@[simp] theorem applyContext_residualTypeVariables
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) :
    (applyContext substitution retainedVariables context).residualTypeVariables =
      context.residualTypeVariables := by
  rfl

@[simp] theorem applyContext_locals (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).locals =
      applyLocals substitution context.locals := by
  rfl

@[simp] theorem applyContext_localSchemeRequirements
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) :
    (applyContext substitution retainedVariables context).localSchemeRequirements =
      applyLocalSchemeRequirements substitution context.locals
        context.localSchemeRequirements := by
  rfl

@[simp] theorem applyContext_assumptions (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).assumptions =
      context.assumptions.map
        (TypedTraitResolution.applySubstitution substitution) := by
  rfl

@[simp] theorem applyContext_solvedRequirements (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context) :
    (applyContext substitution retainedVariables context).solvedRequirements =
      context.solvedRequirements.map (applySolvedRequirement substitution) := by
  rfl

/-- Extending a paired local scope commutes with capture-avoiding flexible
substitution when the stable local identity is fresh for the old metadata
scope. -/
@[simp] theorem applyLocalSchemeRequirements_cons
    (substitution : Substitution) (locals : Resolved.LocalScope Scheme)
    (metadata : Resolved.LocalScope (List LocalSchemeRequirement))
    (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement)
    (fresh : id ∉ metadata.map Prod.fst) :
    applyLocalSchemeRequirements substitution ((id, scheme) :: locals)
        ((id, requirements) :: metadata) =
      (id, requirements.map (LocalSchemeRequirement.applySubstitution
        (substitution.without scheme.quantified))) ::
        applyLocalSchemeRequirements substitution locals metadata := by
  simp only [applyLocalSchemeRequirements, List.map_cons]
  congr 1
  · simp [forLocal, Resolved.LocalScope.lookup?]
  · apply List.map_congr_left
    intro entry member
    rcases entry with ⟨candidate, predicates⟩
    have different : id ≠ candidate := by
      intro same
      apply fresh
      rw [same]
      exact List.mem_map.mpr ⟨(candidate, predicates), member, rfl⟩
    simp [forLocal, Resolved.LocalScope.lookup?, different]

@[simp] theorem applyContext_withLocal
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement := [])
    (fresh : id ∉ context.localSchemeRequirements.map Prod.fst) :
    applyContext substitution retainedVariables
        (context.withLocal id scheme requirements) =
      (applyContext substitution retainedVariables context).withLocal id
        (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified))) := by
  cases context
  simp [Context.withLocal, applyContext, applyLocals, fresh]

@[simp] theorem applyContext_withTypeVariables (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context)
    (variables : List TypeVarId) :
    applyContext substitution retainedVariables
        (context.withTypeVariables variables) =
      applyContext substitution retainedVariables context := by
  rfl

@[simp] theorem applyContext_withTypeVariables_append
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) (variables : List TypeVarId) :
    applyContext substitution (retainedVariables ++ variables)
        (context.withTypeVariables variables) =
      (applyContext substitution retainedVariables context).withTypeVariables
        variables := by
  rfl

@[simp] theorem applyContext_withResidualTypeVariables
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) :
    applyContext substitution retainedVariables
        context.withResidualTypeVariables =
      (applyContext substitution retainedVariables context).withResidualTypeVariables := by
  rfl

@[simp] theorem applyContext_withAssumptions (substitution : Substitution)
    (retainedVariables : List TypeVarId) (context : Context)
    (predicates : List ProgramPredicate) :
    applyContext substitution retainedVariables
        (context.withAssumptions predicates) =
      (applyContext substitution retainedVariables context).withAssumptions
        (predicates.map
          (TypedTraitResolution.applySubstitution substitution)) := by
  rfl

@[simp] theorem applyContext_withSolvedRequirements
    (substitution : Substitution) (retainedVariables : List TypeVarId)
    (context : Context) (requirements : List SolvedRequirement) :
    applyContext substitution retainedVariables
        (context.withSolvedRequirements requirements) =
      (applyContext substitution retainedVariables context).withSolvedRequirements
        (requirements.map (applySolvedRequirement substitution)) := by
  rfl

namespace ContextCloses

/-- Closing the complete lexical metavariable scope is the empty-suffix case
of structural context closure. -/
theorem close {substitution : Substitution} {context : Context}
    (exact : SourceSemantics.ExactSubstitution substitution
      context.typeVariables)
    (range : SourceSemantics.SubstitutionRangeWellFormed
      (closeContext substitution context) substitution) :
    ContextCloses substitution context.typeVariables context
      (closeContext substitution context) := {
  variables_eq := by
    change context.typeVariables = context.typeVariables ++ []
    simp
  exact := exact
  retained_fresh := by
    intro metavariable member
    change metavariable ∈ ([] : List TypeVarId) at member
    simp at member
  range := range
  target_eq := rfl
}

/-- Extend both sides with one fresh stable local identity.  The installed
target scheme and qualified requirements are the capture-avoiding images of
their source counterparts. -/
theorem withLocal {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement := [])
    (fresh : id ∉ source.localSchemeRequirements.map Prod.fst) :
    ContextCloses substitution closedVariables
      (source.withLocal id scheme requirements)
      (target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified)))) := {
  variables_eq := closes.variables_eq
  exact := closes.exact
  retained_fresh := closes.retained_fresh
  range := by
    intro metavariable replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := target)
      (target := target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified))))
      rfl rfl rfl (closes.range metavariable replacement member)
  target_eq := by
    change applyContext substitution target.typeVariables
        (source.withLocal id scheme requirements) =
      target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified)))
    rw [applyContext_withLocal substitution target.typeVariables source id
      scheme requirements fresh, closes.target_eq]
}

/-- Replacing the available predicate assumptions commutes with structural
context closure. -/
theorem withAssumptions {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (predicates : List ProgramPredicate) :
    ContextCloses substitution closedVariables
      (source.withAssumptions predicates)
      (target.withAssumptions (predicates.map
        (TypedTraitResolution.applySubstitution substitution))) := {
  variables_eq := closes.variables_eq
  exact := closes.exact
  retained_fresh := closes.retained_fresh
  range := by
    intro metavariable replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := target)
      (target := target.withAssumptions (predicates.map
        (TypedTraitResolution.applySubstitution substitution)))
      rfl rfl rfl (closes.range metavariable replacement member)
  target_eq := by
    change applyContext substitution target.typeVariables
        (source.withAssumptions predicates) =
      target.withAssumptions (predicates.map
        (TypedTraitResolution.applySubstitution substitution))
    rw [applyContext_withAssumptions, closes.target_eq]
}

/-- Replacing the solved-requirement ledger commutes with structural context
closure.  This is only a structural statement; it does not assert evidence
validity for the replacement rows. -/
theorem withSolvedRequirements {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (requirements : List SolvedRequirement) :
    ContextCloses substitution closedVariables
      (source.withSolvedRequirements requirements)
      (target.withSolvedRequirements
        (requirements.map (applySolvedRequirement substitution))) := {
  variables_eq := closes.variables_eq
  exact := closes.exact
  retained_fresh := closes.retained_fresh
  range := by
    intro metavariable replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := target)
      (target := target.withSolvedRequirements
        (requirements.map (applySolvedRequirement substitution)))
      rfl rfl rfl (closes.range metavariable replacement member)
  target_eq := by
    change applyContext substitution target.typeVariables
        (source.withSolvedRequirements requirements) =
      target.withSolvedRequirements
        (requirements.map (applySolvedRequirement substitution))
    rw [applyContext_withSolvedRequirements, closes.target_eq]
}

/-- Residual-variable admission is independent of lexical-variable closure. -/
theorem withResidualTypeVariables {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target) :
    ContextCloses substitution closedVariables
      source.withResidualTypeVariables target.withResidualTypeVariables := {
  variables_eq := closes.variables_eq
  exact := closes.exact
  retained_fresh := closes.retained_fresh
  range := by
    intro metavariable replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := target) (target := target.withResidualTypeVariables)
      rfl rfl rfl (closes.range metavariable replacement member)
  target_eq := by
    change applyContext substitution target.typeVariables
        source.withResidualTypeVariables =
      target.withResidualTypeVariables
    rw [applyContext_withResidualTypeVariables, closes.target_eq]
}

/-- A fresh inner metavariable suffix remains available on both sides of an
outer context closure. -/
theorem withTypeVariables {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (variables : List TypeVarId)
    (fresh : ∀ metavariable, metavariable ∈ variables →
      metavariable ∉ substitution.domain) :
    ContextCloses substitution closedVariables
      (source.withTypeVariables variables)
      (target.withTypeVariables variables) := {
  variables_eq := by
    change source.typeVariables ++ variables =
      closedVariables ++ (target.typeVariables ++ variables)
    rw [closes.variables_eq, List.append_assoc]
  exact := closes.exact
  retained_fresh := by
    intro metavariable member
    change metavariable ∈ target.typeVariables ++ variables at member
    rcases List.mem_append.mp member with member | member
    · exact closes.retained_fresh metavariable member
    · exact fresh metavariable member
  range := by
    intro metavariable replacement member
    exact StructuralSubstitution.TypeWellFormed.transportContext
      (source := target) (target := target.withTypeVariables variables)
      rfl rfl rfl (closes.range metavariable replacement member)
  target_eq := by
    change applyContext substitution (target.typeVariables ++ variables)
        (source.withTypeVariables variables) =
      target.withTypeVariables variables
    rw [applyContext_withTypeVariables_append, closes.target_eq]
}

/-- Entering a generalized initializer preserves an outer context closure
when its quantified variables are fresh for the outer substitution domain. -/
theorem localSchemeInitializer {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (binder : TypedBinder)
    (fresh : ∀ metavariable, metavariable ∈ binder.scheme.quantified →
      metavariable ∉ substitution.domain) :
    ContextCloses substitution closedVariables
      (localSchemeInitializerContext source binder)
      (localSchemeInitializerContext target
        (binder.applySubstitution substitution)) := by
  have restricted_eq :
      substitution.without binder.scheme.quantified = substitution :=
    Substitution.without_eq_self_of_disjoint_domain substitution
      binder.scheme.quantified fresh
  have assumptions_eq :
      target.assumptions = source.assumptions.map
        (TypedTraitResolution.applySubstitution substitution) := by
    rw [← closes.target_eq]
    rfl
  have extended :=
    (closes.withTypeVariables binder.scheme.quantified fresh).withAssumptions
      (source.assumptions ++ binder.schemeRequirements.map
        (fun requirement => requirement.predicate))
  simpa [localSchemeInitializerContext, assumptions_eq, restricted_eq,
    TypedBinder.applySubstitution, LocalSchemeRequirement.applySubstitution,
    List.map_append, List.map_map, Function.comp_def] using extended

/-- Thread a flexible context closure through one lexical binder extension. -/
theorem afterBinder {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target final : Context}
    {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BinderExtends owner source binder final) :
    ContextCloses substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  cases extension with
  | intro wellFormed fresh =>
      have extended := closes.withLocal binder.id binder.scheme
        binder.schemeRequirements fresh.2
      rw [applyContext_withLocal substitution target.typeVariables source
        binder.id binder.scheme binder.schemeRequirements fresh.2,
        closes.target_eq]
      exact extended

/-- Thread a flexible context closure through a source-ordered binder list. -/
theorem afterBinders {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target final : Context}
    {owner : Resolved.DeclarationId} {binders : List TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BindersExtend owner source binders final) :
    ContextCloses substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [closes.target_eq]
      exact closes
  | cons head tail induction =>
      have middleCloses := closes.afterBinder head
      simpa using induction middleCloses

/-- Thread a flexible context closure through a monomorphic binder list. -/
theorem afterMonoBinders {substitution : Substitution}
    {closedVariables : List TypeVarId} {source target final : Context}
    {owner : Resolved.DeclarationId} {binders : List TypedBinder}
    {types : List Ty}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : MonoBindersExtend owner source binders types final) :
    ContextCloses substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [closes.target_eq]
      exact closes
  | cons _ head tail induction =>
      have middleCloses := closes.afterBinder head
      simpa using induction middleCloses

end ContextCloses

namespace LocalSchemesFreshFor

/-- The mapped target local scope retains the source schemes' protected
quantifiers because flexible substitution never changes a scheme's binder
list. -/
theorem target
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context}
    (closes : ContextCloses substitution closedVariables source target)
    (fresh : LocalSchemesFreshFor source substitution) :
    LocalSchemesFreshFor target substitution := by
  intro entry member metavariable quantified
  rw [← closes.target_eq] at member
  change entry ∈ applyLocals substitution source.locals at member
  rcases List.mem_map.mp member with
    ⟨⟨id, scheme⟩, sourceMember, entryEq⟩
  subst entry
  exact fresh (id, scheme) sourceMember metavariable (by
    simpa using quantified)

/-- The schemes preceding a well-formed binder are protected from an exact
instantiation of that binder's own quantified variables. -/
theorem ofBinderWellFormed
    {context : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder} {substitution : Substitution}
    (wellFormed : BinderWellFormed context owner binder)
    (exact : ExactSubstitution substitution binder.scheme.quantified) :
    LocalSchemesFreshFor context substitution := by
  intro entry member metavariable quantified domainMember
  have binderQuantified :=
    (exact.mem_domain_iff metavariable).mp domainMember
  exact (wellFormed.quantified_fresh metavariable binderQuantified).2
    entry member quantified

/-- A well-formed binder added under a context closure remains protected from
the closing substitution, and preserves protection of every older scheme. -/
theorem afterBinder
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder}
    (schemesFresh : LocalSchemesFreshFor source substitution)
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BinderExtends owner source binder final) :
    LocalSchemesFreshFor final substitution := by
  cases extension with
  | intro wellFormed fresh =>
      apply schemesFresh.withLocal
      intro metavariable quantified domainMember
      have closed := (closes.exact.mem_domain_iff metavariable).mp domainMember
      have ambient : metavariable ∈ source.typeVariables := by
        rw [closes.variables_eq]
        exact List.mem_append.mpr (Or.inl closed)
      exact (wellFormed.quantified_fresh metavariable quantified).1 ambient

/-- Thread local-scheme protection through a binder sequence. -/
theorem afterBinders
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder}
    (schemesFresh : LocalSchemesFreshFor source substitution)
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BindersExtend owner source binders final) :
    LocalSchemesFreshFor final substitution := by
  induction extension generalizing target with
  | nil => exact schemesFresh
  | cons head tail induction =>
      exact induction (schemesFresh.afterBinder closes head)
        (closes.afterBinder head)

/-- Thread local-scheme protection through a monomorphic binder sequence. -/
theorem afterMonoBinders
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder} {types : List Ty}
    (schemesFresh : LocalSchemesFreshFor source substitution)
    (closes : ContextCloses substitution closedVariables source target)
    (extension : MonoBindersExtend owner source binders types final) :
    LocalSchemesFreshFor final substitution := by
  induction extension generalizing target with
  | nil => exact schemesFresh
  | cons _ head tail induction =>
      exact induction (schemesFresh.afterBinder closes head)
        (closes.afterBinder head)

end LocalSchemesFreshFor

/-- A semantically valid flexible closure transports one exact solved
requirement.  Assumption evidence is reconstructed structurally; the validity
object supplies the genuinely non-structural implementation case. -/
theorem RequirementProves.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : RequirementId}
    {predicate : ProgramPredicate}
    (valid : ContextSubstitutionValid substitution closedVariables source
      target)
    (proves : RequirementProves source id predicate) :
    RequirementProves target id
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  rcases proves with ⟨requirement, contains, predicateEq, evidenceValid⟩
  rcases contains with ⟨member, idEq⟩
  refine ⟨applySolvedRequirement substitution requirement, ?_, ?_, ?_⟩
  · constructor
    · rw [← valid.closes.target_eq]
      change applySolvedRequirement substitution requirement ∈
        source.solvedRequirements.map (applySolvedRequirement substitution)
      exact List.mem_map.mpr ⟨requirement, member, rfl⟩
    · exact idEq
  · simp [applySolvedRequirement, predicateEq]
  · cases evidenceEq : requirement.evidence with
    | assumption assumption =>
        cases evidenceValid with
        | intro retainedValid =>
            rw [evidenceEq] at retainedValid
            cases retainedValid with
            | intro represents semanticValid =>
                cases represents with
                | assumption =>
                    cases semanticValid with
                    | assumption goalMem =>
                        apply SolvedRequirementValid.intro
                        simp only [applySolvedRequirement, evidenceEq,
                          applyPredicateEvidence]
                        exact .intro (.assumption _) (.assumption (by
                          rw [← valid.closes.target_eq]
                          exact List.mem_map.mpr
                            ⟨requirement.predicate, goalMem, rfl⟩))
    | implementation evidence =>
        exact valid.implementationRequirements requirement evidence member
          evidenceEq

theorem RequirementValid.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : RequirementId}
    (valid : ContextSubstitutionValid substitution closedVariables source
      target)
    (requirement : RequirementValid source id) :
    RequirementValid target id := by
  rcases requirement with ⟨predicate, proves⟩
  exact ⟨TypedTraitResolution.applySubstitution substitution predicate,
    FlexibleSubstitution.RequirementProves.applySubstitution valid proves⟩

theorem RequirementIdsValid.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {ids : List RequirementId}
    (valid : ContextSubstitutionValid substitution closedVariables source
      target)
    (requirements : RequirementIdsValid source ids) :
    RequirementIdsValid target ids := by
  intro id member
  exact FlexibleSubstitution.RequirementValid.applySubstitution valid
    (requirements id member)

theorem RequirementSequenceProves.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {ids : List RequirementId}
    {predicates : List ProgramPredicate}
    (valid : ContextSubstitutionValid substitution closedVariables source
      target)
    (proves : RequirementSequenceProves source ids predicates) :
    RequirementSequenceProves target ids
      (predicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  induction proves with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (FlexibleSubstitution.RequirementProves.applySubstitution valid head)
        induction

/-- Flexible context closure preserves either retained interpretation of an
integer literal and its exact trait requirement. -/
theorem IntegerLiteralValid.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (contextValid :
      ContextSubstitutionValid substitution closedVariables source target)
    (valid : IntegerLiteralValid source literal resolution) :
    IntegerLiteralValid target literal
      (resolution.applySubstitution substitution) := by
  cases valid with
  | word meaning targetEq evidence =>
      refine .word meaning ?_ ?_
      · simp [targetEq]
      · simpa [ProgramSignatures.builtinIntPredicate,
          TypedTraitResolution.applySubstitution] using
          (RequirementProves.applySubstitution contextValid evidence)
  | integer meaning targetEq evidence =>
      refine .integer meaning ?_ ?_
      · simp [targetEq]
      · simpa [ProgramSignatures.builtinIntPredicate,
          TypedTraitResolution.applySubstitution] using
          (RequirementProves.applySubstitution contextValid evidence)

/-- Structural context closure transports every admissible retained type.
Variables in the closed prefix are replaced by the ground range, while fresh
variables in the retained suffix and residual body variables remain scoped. -/
theorem TypeAdmissible.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {type : Ty}
    (closes : ContextCloses substitution closedVariables source target)
    (admissible : TypeAdmissible source type) :
    TypeAdmissible target (substitution.apply type) := by
  have signatures_eq : target.signatures = source.signatures := by
    rw [← closes.target_eq]
    rfl
  have parameters_eq : target.typeParameters = source.typeParameters := by
    rw [← closes.target_eq]
    rfl
  have declaration_eq :
      target.currentDeclaration = source.currentDeclaration := by
    rw [← closes.target_eq]
    rfl
  have residual_eq :
      target.residualTypeVariables = source.residualTypeVariables := by
    rw [← closes.target_eq]
    rfl
  refine {
    binders :=
      StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
        parameters_eq declaration_eq admissible.binders
    typeWellScoped := ?_
  }
  apply TypeWellScoped.applySubstitution
    (sourceVariables := admissibleTypeVariables source type)
    (targetVariables :=
      admissibleTypeVariables target (substitution.apply type))
    closes.exact.domain_nodup closes.range signatures_eq parameters_eq
    declaration_eq
  · intro metavariable member absent
    unfold admissibleTypeVariables at member ⊢
    rw [residual_eq]
    rcases List.mem_append.mp member with lexical | residual
    · rw [closes.variables_eq] at lexical
      rcases List.mem_append.mp lexical with closed | retained
      · exact (absent ((closes.exact.mem_domain_iff metavariable).mpr
          closed)).elim
      · exact List.mem_append.mpr (Or.inl retained)
    · cases openVariables : source.residualTypeVariables with
      | false => simp [openVariables] at residual
      | true =>
          apply List.mem_append.mpr
          apply Or.inr
          apply Substitution.mem_freeVariables_apply_of_not_mem_domain
            substitution absent
          simpa [openVariables] using residual
  · exact admissible.typeWellScoped

/-- The ground special case of flexible context closure.  A source type with
no flexible variables remains well formed after any structurally valid
closure. -/
theorem TypeWellFormed.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {type : Ty}
    (closes : ContextCloses substitution closedVariables source target)
    (wellFormed : TypeWellFormed source type) :
    TypeWellFormed target (substitution.apply type) := by
  have signatures_eq : target.signatures = source.signatures := by
    rw [← closes.target_eq]
    rfl
  have parameters_eq : target.typeParameters = source.typeParameters := by
    rw [← closes.target_eq]
    rfl
  have declaration_eq :
      target.currentDeclaration = source.currentDeclaration := by
    rw [← closes.target_eq]
    rfl
  refine {
    binders :=
      StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
        parameters_eq declaration_eq wellFormed.binders
    typeWellScoped := ?_
  }
  apply TypeWellScoped.applySubstitution
    (sourceVariables := []) (targetVariables := [])
    closes.exact.domain_nodup closes.range signatures_eq parameters_eq
    declaration_eq
  · intro metavariable member
    simp at member
  · exact wellFormed.typeWellScoped

/-- Flexible closure transports every closed rigid-parameter replacement
while preserving the parameter domain. -/
theorem ParameterSubstitution.RangeWellFormed.applyFlexible
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {inner : ParameterSubstitution}
    (closes : ContextCloses substitution closedVariables source target)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed source
      inner) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed target
      (ParameterSubstitution.mapRange substitution inner) := by
  intro parameter replacement member
  rcases List.mem_map.mp member with
    ⟨⟨sourceParameter, sourceReplacement⟩, sourceMember, entryEq⟩
  cases entryEq
  exact TypeWellFormed.applySubstitution closes
    (range sourceParameter sourceReplacement sourceMember)

/-- Flexible closure transports admissible rigid-parameter replacements,
including lexical and residual metavariables. -/
theorem ParameterSubstitution.RangeAdmissible.applyFlexible
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {inner : ParameterSubstitution}
    (closes : ContextCloses substitution closedVariables source target)
    (range : SourceSemantics.ParameterSubstitution.RangeAdmissible source
      inner) :
    SourceSemantics.ParameterSubstitution.RangeAdmissible target
      (ParameterSubstitution.mapRange substitution inner) := by
  intro parameter replacement member
  rcases List.mem_map.mp member with
    ⟨⟨sourceParameter, sourceReplacement⟩, sourceMember, entryEq⟩
  cases entryEq
  exact TypeAdmissible.applySubstitution closes
    (range sourceParameter sourceReplacement sourceMember)

/-- Capture-avoiding flexible substitution preserves rank-1 scheme
well-formedness across a structural context closure. -/
theorem SchemeWellFormed.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {scheme : Scheme}
    (closes : ContextCloses substitution closedVariables source target)
    (wellFormed : SchemeWellFormed source scheme) :
    SchemeWellFormed target (scheme.apply substitution) := by
  let restricted := substitution.without scheme.quantified
  have signatures_eq : target.signatures = source.signatures := by
    rw [← closes.target_eq]
    rfl
  have parameters_eq : target.typeParameters = source.typeParameters := by
    rw [← closes.target_eq]
    rfl
  have declaration_eq :
      target.currentDeclaration = source.currentDeclaration := by
    rw [← closes.target_eq]
    rfl
  have residual_eq :
      target.residualTypeVariables = source.residualTypeVariables := by
    rw [← closes.target_eq]
    rfl
  refine {
    binders :=
      StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
        parameters_eq declaration_eq wellFormed.binders
    quantified_nodup := by
      simpa [TypeSystem.Scheme.apply] using wellFormed.quantified_nodup
    body := ?_
  }
  change TypeWellScoped target
    (admissibleTypeVariables target (restricted.apply scheme.body) ++
      scheme.quantified)
    (restricted.apply scheme.body)
  apply TypeWellScoped.applySubstitution
    (sourceVariables :=
      admissibleTypeVariables source scheme.body ++ scheme.quantified)
    (targetVariables :=
      admissibleTypeVariables target (restricted.apply scheme.body) ++
        scheme.quantified)
    (Substitution.domain_without_nodup substitution scheme.quantified
      closes.exact.domain_nodup)
    (SubstitutionRangeWellFormed.without closes.range scheme.quantified)
    signatures_eq parameters_eq
    declaration_eq
  · intro metavariable member absent
    rcases List.mem_append.mp member with ambient | quantified
    · unfold admissibleTypeVariables at ambient ⊢
      rw [residual_eq]
      rcases List.mem_append.mp ambient with lexical | residual
      · rw [closes.variables_eq] at lexical
        rcases List.mem_append.mp lexical with closed | retained
        · by_cases quantified : metavariable ∈ scheme.quantified
          · exact List.mem_append.mpr (Or.inr quantified)
          · have originalDomain : metavariable ∈ substitution.domain :=
              (closes.exact.mem_domain_iff metavariable).mpr closed
            have restrictedDomain : metavariable ∈ restricted.domain :=
              (Substitution.mem_domain_without_iff substitution
                scheme.quantified metavariable).mpr
                ⟨originalDomain, quantified⟩
            exact (absent restrictedDomain).elim
        · apply List.mem_append.mpr
          apply Or.inl
          exact List.mem_append.mpr (Or.inl retained)
      · cases openVariables : source.residualTypeVariables with
        | false => simp [openVariables] at residual
        | true =>
            apply List.mem_append.mpr
            apply Or.inl
            apply List.mem_append.mpr
            apply Or.inr
            apply (Substitution.mem_freeVariables_apply_iff
              (SubstitutionRangeWellFormed.without closes.range
                scheme.quantified) metavariable
              scheme.body).mpr
            exact ⟨by simpa [openVariables] using residual, absent⟩
    · exact List.mem_append.mpr (Or.inr quantified)
  · exact wellFormed.body

/-- Flexible context closure preserves admissible trait predicates pointwise
while retaining the resolved trait identity and arity. -/
theorem PredicateAdmissible.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {predicate : ProgramPredicate}
    (closes : ContextCloses substitution closedVariables source target)
    (admissible : PredicateAdmissible source predicate) :
    PredicateAdmissible target
      (TypedTraitResolution.applySubstitution substitution predicate) := by
  constructor
  · exact TypeAdmissible.applySubstitution closes admissible.subject
  · intro argument member
    rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
    exact TypeAdmissible.applySubstitution closes
      (admissible.arguments original originalMember)
  · have signatures_eq : target.signatures = source.signatures := by
      rw [← closes.target_eq]
      rfl
    cases traitEq : predicate.trait with
    | builtin builtin =>
        cases builtin with
        | int =>
            have traitValid := admissible.trait
            rw [traitEq] at traitValid
            simpa [TypedTraitResolution.applySubstitution, traitEq] using
              traitValid
    | declaration id =>
        have traitValid := admissible.trait
        rw [traitEq] at traitValid
        rcases traitValid with ⟨signature, member, idEq, arity⟩
        simp only [TypedTraitResolution.applySubstitution, traitEq]
        exact ⟨signature, by simpa [signatures_eq] using member, idEq,
          by simpa [TypedTraitResolution.applySubstitution] using arity⟩

/-- Variables selected for generalization are fresh for the ambient lexical
flexible-variable scope. -/
theorem SchemeGeneralizesExcept.quantified_fresh
    {context : Context} {exemptRequirements : List RequirementId}
    {scheme : Scheme}
    (generalizes : SchemeGeneralizesExcept context exemptRequirements scheme) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∉ context.typeVariables := by
  intro metavariable quantified ambient
  rw [generalizes] at quantified
  have selected := (List.mem_filter.mp quantified).2
  have blocked : metavariable ∈
      GeneralizationBlockedVariablesExcept context exemptRequirements := by
    simp [GeneralizationBlockedVariablesExcept, ambient]
  have notBlocked : metavariable ∉
      GeneralizationBlockedVariablesExcept context exemptRequirements := by
    simpa using selected
  exact notBlocked blocked

private theorem quantified_fresh_for_closure
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {exemptRequirements : List RequirementId}
    {scheme : Scheme}
    (closes : ContextCloses substitution closedVariables source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements scheme) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∉ substitution.domain := by
  intro metavariable quantified domainMember
  apply SchemeGeneralizesExcept.quantified_fresh generalizes metavariable
    quantified
  rw [closes.variables_eq]
  exact List.mem_append.mpr (Or.inl
    ((closes.exact.mem_domain_iff metavariable).mp domainMember))

/-- Closing an outer flexible scope preserves the exact qualified
generalization frontier of a capture-avoiding rank-1 scheme. -/
theorem SchemeGeneralizesExcept.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {exemptRequirements : List RequirementId}
    {scheme : Scheme}
    (closes : ContextCloses substitution closedVariables source target)
    (generalizes :
      SchemeGeneralizesExcept source exemptRequirements scheme) :
    SchemeGeneralizesExcept target exemptRequirements
      (scheme.apply substitution) := by
  have fresh := quantified_fresh_for_closure closes generalizes
  have restricted_eq :
      substitution.without scheme.quantified = substitution :=
    Substitution.without_eq_self_of_disjoint_domain substitution
      scheme.quantified fresh
  have domain_blocked : ∀ metavariable,
      metavariable ∈ substitution.domain →
        metavariable ∈
          GeneralizationBlockedVariablesExcept source exemptRequirements := by
    intro metavariable member
    have closed := (closes.exact.mem_domain_iff metavariable).mp member
    have ambient : metavariable ∈ source.typeVariables := by
      rw [closes.variables_eq]
      exact List.mem_append.mpr (Or.inl closed)
    simp [GeneralizationBlockedVariablesExcept, ambient]
  unfold SchemeGeneralizesExcept at generalizes ⊢
  change scheme.quantified =
    ((substitution.without scheme.quantified).apply
      scheme.body).freeVariables.filter (fun metavariable =>
        !(GeneralizationBlockedVariablesExcept target exemptRequirements).contains
          metavariable)
  rw [restricted_eq, Substitution.freeVariables_apply closes.range,
    generalizationBlockedVariablesExcept_applySubstitution closes,
    filter_unblocked_after_domain scheme.body.freeVariables
      (GeneralizationBlockedVariablesExcept source exemptRequirements)
      substitution.domain domain_blocked]
  exact generalizes

/-- Ordinary rank-1 generalization is the empty-exemption instance of
qualified generalization transport. -/
theorem SchemeGeneralizes.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {scheme : Scheme}
    (closes : ContextCloses substitution closedVariables source target)
    (generalizes : SchemeGeneralizes source scheme) :
    SchemeGeneralizes target (scheme.apply substitution) := by
  exact SchemeGeneralizesExcept.applySubstitution closes generalizes

/-- Flexible closure preserves one qualified local-scheme requirement when
the protected scheme variables are explicitly fresh for the outer
substitution. -/
theorem LocalSchemeRequirementWellFormed.applySubstitution_of_fresh
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder}
    {requirement : LocalSchemeRequirement}
    (closes : ContextCloses substitution closedVariables source target)
    (fresh : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ substitution.domain)
    (wellFormed : LocalSchemeRequirementWellFormed source binder requirement) :
    LocalSchemeRequirementWellFormed target
      (binder.applySubstitution substitution)
      (requirement.applySubstitution
        (substitution.without binder.scheme.quantified)) := by
  have restricted_eq :
      substitution.without binder.scheme.quantified = substitution :=
    Substitution.without_eq_self_of_disjoint_domain substitution
      binder.scheme.quantified fresh
  have initializerCloses :=
    closes.localSchemeInitializer binder fresh
  constructor
  · simpa [LocalSchemeRequirement.applySubstitution, restricted_eq] using
      (PredicateAdmissible.applySubstitution initializerCloses
        wellFormed.predicate)
  · rcases wellFormed.depends_on_quantified with
      ⟨metavariable, quantified, occurs⟩
    refine ⟨metavariable, by simpa using quantified, ?_⟩
    simpa [LocalSchemeRequirement.applySubstitution, restricted_eq] using
      (Substitution.mem_predicateVariables_applySubstitution_of_not_mem_domain
        substitution (fresh metavariable quantified) occurs)
  · rcases wellFormed.template with
      ⟨solved, solvedUnique, idEq, predicateEq, evidenceEq⟩
    have solvedRequirements_eq :
        target.solvedRequirements =
          source.solvedRequirements.map
            (applySolvedRequirement substitution) := by
      rw [← closes.target_eq]
      rfl
    have filtered :
        ((source.solvedRequirements.map
            (applySolvedRequirement substitution)).filter fun candidate =>
              candidate.id == requirement.templateRequirement) =
          (source.solvedRequirements.filter fun candidate =>
              candidate.id == requirement.templateRequirement).map
            (applySolvedRequirement substitution) := by
      induction source.solvedRequirements with
      | nil => rfl
      | cons candidate requirements induction =>
          by_cases selected :
              candidate.id == requirement.templateRequirement
          · simp [applySolvedRequirement, selected, induction]
          · simp [applySolvedRequirement, selected, induction]
    refine ⟨applySolvedRequirement substitution solved, ?_, ?_, ?_, ?_⟩
    · rw [solvedRequirements_eq]
      simpa [LocalSchemeRequirement.applySubstitution, filtered] using congrArg
        (List.map (applySolvedRequirement substitution)) solvedUnique
    · exact idEq
    · simp [applySolvedRequirement, LocalSchemeRequirement.applySubstitution,
        restricted_eq, predicateEq]
    · simp [applySolvedRequirement, applyPredicateEvidence,
        LocalSchemeRequirement.applySubstitution, restricted_eq, evidenceEq]

/-- Exact local generalization supplies the freshness needed by the explicit
qualified-requirement transport theorem. -/
theorem LocalSchemeRequirementWellFormed.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder}
    {requirement : LocalSchemeRequirement}
    {exemptRequirements : List RequirementId}
    (closes : ContextCloses substitution closedVariables source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements
      binder.scheme)
    (wellFormed : LocalSchemeRequirementWellFormed source binder requirement) :
    LocalSchemeRequirementWellFormed target
      (binder.applySubstitution substitution)
      (requirement.applySubstitution
        (substitution.without binder.scheme.quantified)) := by
  exact LocalSchemeRequirementWellFormed.applySubstitution_of_fresh closes
    (quantified_fresh_for_closure closes generalizes) wellFormed

/-- Explicit freshness transports the complete ordered, uniquely identified
qualified-requirement spine of a local scheme. -/
theorem LocalSchemeRequirementsWellFormed.applySubstitution_of_fresh
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (fresh : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ substitution.domain)
    (wellFormed : LocalSchemeRequirementsWellFormed source binder) :
    LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution substitution) := by
  constructor
  · simpa [localSchemeTemplateIds, TypedBinder.applySubstitution,
      LocalSchemeRequirement.applySubstitution, List.map_map,
      Function.comp_def] using wellFormed.ids_unique
  · intro requirement member
    rw [applyTypedBinder_schemeRequirements] at member
    rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
    exact LocalSchemeRequirementWellFormed.applySubstitution_of_fresh closes
      fresh (wellFormed.entries original originalMember)

/-- Flexible closure preserves the qualified-requirement spine of an exactly
generalized local scheme. -/
theorem LocalSchemeRequirementsWellFormed.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder}
    {exemptRequirements : List RequirementId}
    (closes : ContextCloses substitution closedVariables source target)
    (generalizes : SchemeGeneralizesExcept source exemptRequirements
      binder.scheme)
    (wellFormed : LocalSchemeRequirementsWellFormed source binder) :
    LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution substitution) := by
  exact LocalSchemeRequirementsWellFormed.applySubstitution_of_fresh closes
    (quantified_fresh_for_closure closes generalizes) wellFormed

/-- Mapping an outer flexible substitution over a shared local-scheme
instantiation commutes with its ordered qualified-predicate spine. -/
theorem instantiateLocalSchemePredicates_applySubstitution
    {outer : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder} {inner : Substitution}
    (closes : ContextCloses outer closedVariables source target)
    (fresh : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ outer.domain)
    (formation : LocalSchemeRequirementsWellFormed source binder)
    (innerExact : ExactSubstitution inner binder.scheme.quantified) :
    (instantiateLocalSchemePredicates inner binder).map
        (TypedTraitResolution.applySubstitution outer) =
      instantiateLocalSchemePredicates (Substitution.mapRange outer inner)
        (binder.applySubstitution outer) := by
  have restricted_eq : outer.without binder.scheme.quantified = outer :=
    Substitution.without_eq_self_of_disjoint_domain outer
      binder.scheme.quantified fresh
  unfold instantiateLocalSchemePredicates
  simp only [applyTypedBinder_schemeRequirements, restricted_eq, List.map_map]
  apply List.map_congr_left
  intro requirement member
  exact PredicateAdmissible.applyFlexible_compose outer inner closes.range
    innerExact fresh (formation.entries requirement member).predicate

/-- Explicit scheme-binder freshness transports one complete local reference
instantiation, including its shared type substitution and requirement spine. -/
theorem LocalSchemeInstantiationValid.applySubstitution_of_fresh
    {outer : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    (contextValid : ContextSubstitutionValid outer closedVariables source target)
    (fresh : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ outer.domain)
    (valid : LocalSchemeInstantiationValid source binder type
      actualRequirements) :
    LocalSchemeInstantiationValid target
      (binder.applySubstitution outer) (outer.apply type)
      actualRequirements := by
  cases valid with
  | intro formation schemeWellFormed inner innerExact innerRange result
      actualUnique actualDisjoint requirements =>
      have restricted_eq : outer.without binder.scheme.quantified = outer :=
        Substitution.without_eq_self_of_disjoint_domain outer
          binder.scheme.quantified fresh
      refine .intro
        (LocalSchemeRequirementsWellFormed.applySubstitution_of_fresh
          contextValid.closes fresh formation)
        (by simpa using (SchemeWellFormed.applySubstitution
          contextValid.closes schemeWellFormed))
        (Substitution.mapRange outer inner)
        (Substitution.ExactSubstitution.mapRange outer innerExact)
        ?_ ?_ actualUnique ?_ ?_
      · intro metavariable replacement member
        rcases List.mem_map.mp member with
          ⟨⟨innerVariable, innerReplacement⟩, innerMember, entryEq⟩
        cases entryEq
        exact TypeAdmissible.applySubstitution contextValid.closes
          (innerRange innerVariable innerReplacement innerMember)
      · change (Substitution.mapRange outer inner).apply
          (binder.applySubstitution outer).scheme.body = outer.apply type
        rw [applyTypedBinder_scheme]
        change (Substitution.mapRange outer inner).apply
            ((outer.without binder.scheme.quantified).apply binder.scheme.body) =
          outer.apply type
        rw [restricted_eq, ← result]
        exact (TypeWellScoped.applyFlexible_compose outer inner
          contextValid.closes.range innerExact fresh schemeWellFormed.body).symm
      · intro id actualMember templateMember
        exact actualDisjoint id actualMember (by
          simpa [localSchemeTemplateIds, TypedBinder.applySubstitution,
            LocalSchemeRequirement.applySubstitution, List.map_map,
            Function.comp_def] using templateMember)
      · have transported :=
          RequirementSequenceProves.applySubstitution contextValid requirements
        rw [instantiateLocalSchemePredicates_applySubstitution
          contextValid.closes fresh formation innerExact] at transported
        exact transported

/-- Flexible context closure preserves the common retained-binder formation
judgment; scheme quantifiers protect themselves from the outer substitution. -/
theorem BinderWellFormed.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (wellFormed : BinderWellFormed source owner binder) :
    BinderWellFormed target owner
      (binder.applySubstitution substitution) := {
  owned := by simpa using wellFormed.owned
  scheme := by
    simpa using SchemeWellFormed.applySubstitution closes wellFormed.scheme
  quantified_fresh := by
    intro metavariable quantified
    have sourceQuantified : metavariable ∈ binder.scheme.quantified := by
      simpa using quantified
    rcases wellFormed.quantified_fresh metavariable sourceQuantified with
      ⟨ambientFresh, localsFresh⟩
    constructor
    · intro targetMember
      apply ambientFresh
      rw [closes.variables_eq]
      exact List.mem_append.mpr (Or.inr targetMember)
    · intro entry member localQuantified
      rw [← closes.target_eq] at member
      change entry ∈ applyLocals substitution source.locals at member
      rcases List.mem_map.mp member with
        ⟨⟨id, scheme⟩, sourceMember, localEq⟩
      subst entry
      exact localsFresh (id, scheme) sourceMember (by
        simpa using localQuantified)
  monomorphic_requirements_empty := by
    intro quantifiedEmpty
    have originalQuantifiedEmpty : binder.scheme.quantified = [] := by
      simpa using quantifiedEmpty
    simp [TypedBinder.applySubstitution,
      wellFormed.monomorphic_requirements_empty originalQuantifiedEmpty]
}

/-- Flexible context closure preserves freshness in both paired local scopes;
the substitution changes only schemes and predicates, never stable local
identities. -/
theorem LocalFresh.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : Resolved.LocalId}
    (closes : ContextCloses substitution closedVariables source target)
    (fresh : LocalFresh source id) :
    LocalFresh target id := by
  rw [← closes.target_eq]
  simpa [LocalFresh, applyContext, applyLocals,
    applyLocalSchemeRequirements, List.map_map, Function.comp_def] using fresh

/-- Closing an outer flexible scope commutes with one retained lexical-binder
extension, including its paired qualified-requirement metadata. -/
theorem BinderExtends.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BinderExtends owner source binder final) :
    BinderExtends owner target (binder.applySubstitution substitution)
      (applyContext substitution target.typeVariables final) := by
  cases extension with
  | intro wellFormed fresh =>
      rw [applyContext_withLocal substitution target.typeVariables source
        binder.id binder.scheme binder.schemeRequirements fresh.2,
        closes.target_eq]
      simpa using BinderExtends.intro
        (BinderWellFormed.applySubstitution closes wellFormed)
        (LocalFresh.applySubstitution closes fresh)

/-- Flexible context closure transports a source-ordered binder extension and
threads the resulting context closure through every newly installed binder. -/
theorem BindersExtend.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : BindersExtend owner source binders final) :
    BindersExtend owner target
      (binders.map (TypedBinder.applySubstitution substitution))
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [closes.target_eq]
      exact .nil _
  | @cons context middle final binder binders head tail induction =>
      cases head with
      | intro wellFormed fresh =>
          have middleCloses := closes.withLocal binder.id binder.scheme
            binder.schemeRequirements fresh.2
          have transportedHead : BinderExtends owner target
              (binder.applySubstitution substitution)
              (target.withLocal binder.id (binder.scheme.apply substitution)
                (binder.schemeRequirements.map
                  (LocalSchemeRequirement.applySubstitution
                    (substitution.without binder.scheme.quantified)))) := by
            simpa using BinderExtends.intro
              (BinderWellFormed.applySubstitution closes wellFormed)
              (LocalFresh.applySubstitution closes fresh)
          have transportedTail := induction middleCloses
          refine .cons transportedHead ?_
          simpa [Context.withLocal] using transportedTail

/-- The monomorphic specialization of flexible binder transport preserves the
source-order type spine alongside the transported binders. -/
theorem MonoBindersExtend.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder} {types : List Ty}
    (closes : ContextCloses substitution closedVariables source target)
    (extension : MonoBindersExtend owner source binders types final) :
    MonoBindersExtend owner target
      (binders.map (TypedBinder.applySubstitution substitution))
      (types.map substitution.apply)
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [closes.target_eq]
      exact .nil _
  | @cons context middle final binder binders type types schemeEq head tail
      induction =>
      cases head with
      | intro wellFormed fresh =>
          have middleCloses := closes.withLocal binder.id binder.scheme
            binder.schemeRequirements fresh.2
          have transportedHead : BinderExtends owner target
              (binder.applySubstitution substitution)
              (target.withLocal binder.id (binder.scheme.apply substitution)
                (binder.schemeRequirements.map
                  (LocalSchemeRequirement.applySubstitution
                    (substitution.without binder.scheme.quantified)))) := by
            simpa using BinderExtends.intro
              (BinderWellFormed.applySubstitution closes wellFormed)
              (LocalFresh.applySubstitution closes fresh)
          have transportedTail := induction middleCloses
          refine .cons ?_ transportedHead ?_
          · simp [schemeEq]
          · simpa [Context.withLocal] using transportedTail

/-- A typed statement changes its lexical context only through the binder
extensions already recorded by its typing constructor. -/
theorem StatementHasType.contextCloses
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {sourceContext targetContext final : Context}
    {source : TypedSource} {control : ControlContext}
    {id : StatementId} {facts : StatementFacts}
    (closes : ContextCloses substitution closedVariables sourceContext
      targetContext)
    (typing : StatementHasType source control sourceContext id final facts) :
    ContextCloses substitution closedVariables final
      (applyContext substitution targetContext.typeVariables final) := by
  cases typing with
  | letUninitialized _ _ _ _ extension _ => exact closes.afterBinder extension
  | letInitialized _ _ _ _ _ extension _ => exact closes.afterBinder extension
  | letInitializedGeneralized _ _ _ _ _ _ extension _ =>
      exact closes.afterBinder extension
  | returnUnit | returnValue | expressionValue | expressionDiscard |
      assignValue | assignBitNot | ifWithoutElse | ifWithElse | block |
      matchWithoutDefault | matchWithDefault | forLoop | whileLoop |
      breakStmt | continueStmt =>
      rw [closes.target_eq]
      exact closes

/-- A typed statement sequence threads flexible context closure through every
statement-local extension. -/
theorem StatementsHaveType.contextCloses
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {sourceContext targetContext final : Context}
    {source : TypedSource} {control : ControlContext}
    {statements : List StatementId} {facts : BodyFacts}
    (closes : ContextCloses substitution closedVariables sourceContext
      targetContext)
    (typing : StatementsHaveType source control sourceContext statements final
      facts) :
    ContextCloses substitution closedVariables final
      (applyContext substitution targetContext.typeVariables final) := by
  induction statements generalizing sourceContext targetContext final facts with
  | nil =>
      cases typing
      rw [closes.target_eq]
      exact closes
  | cons statement statements induction =>
      cases statements with
      | nil =>
          cases typing with
          | singleton head =>
              exact FlexibleSubstitution.StatementHasType.contextCloses
                closes head
      | cons next rest =>
          cases typing with
          | cons head tail =>
              have middleCloses :=
                FlexibleSubstitution.StatementHasType.contextCloses closes head
              simpa using induction middleCloses tail

/-- A typed `for` item changes its lexical context only through its recorded
binder extension. -/
theorem ForItemHasType.contextCloses
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {sourceContext targetContext final : Context}
    {source : TypedSource} {control : ControlContext} {item : ForItemForm}
    (closes : ContextCloses substitution closedVariables sourceContext
      targetContext)
    (typing : ForItemHasType source control sourceContext item final) :
    ContextCloses substitution closedVariables final
      (applyContext substitution targetContext.typeVariables final) := by
  cases typing with
  | letUninitialized _ _ extension => exact closes.afterBinder extension
  | letInitialized _ _ _ extension => exact closes.afterBinder extension
  | letInitializedGeneralized _ _ _ _ extension =>
      exact closes.afterBinder extension
  | expression | assignValue | assignBitNot =>
      rw [closes.target_eq]
      exact closes

/-- A typed `for` item sequence threads flexible context closure through every
item-local extension. -/
theorem ForItemsHaveType.contextCloses
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {sourceContext targetContext final : Context}
    {source : TypedSource} {control : ControlContext}
    {items : List ForItemForm}
    (closes : ContextCloses substitution closedVariables sourceContext
      targetContext)
    (typing : ForItemsHaveType source control sourceContext items final) :
    ContextCloses substitution closedVariables final
      (applyContext substitution targetContext.typeVariables final) := by
  induction items generalizing sourceContext targetContext final with
  | nil =>
      cases typing
      rw [closes.target_eq]
      exact closes
  | cons item items induction =>
      cases typing with
      | cons head tail =>
          have middleCloses :=
            FlexibleSubstitution.ForItemHasType.contextCloses closes head
          simpa using induction middleCloses tail

@[simp] theorem closeContext_signatures (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).signatures = context.signatures := by
  rfl

@[simp] theorem closeContext_currentDeclaration (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).currentDeclaration =
      context.currentDeclaration := by
  rfl

@[simp] theorem closeContext_typeParameters (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).typeParameters =
      context.typeParameters := by
  rfl

@[simp] theorem closeContext_typeVariables (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).typeVariables = [] := by
  rfl

@[simp] theorem closeContext_residualTypeVariables
    (substitution : Substitution) (context : Context) :
    (closeContext substitution context).residualTypeVariables =
      context.residualTypeVariables := by
  rfl

@[simp] theorem closeContext_locals (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).locals =
      applyLocals substitution context.locals := by
  rfl

@[simp] theorem closeContext_localSchemeRequirements
    (substitution : Substitution) (context : Context) :
    (closeContext substitution context).localSchemeRequirements =
      applyLocalSchemeRequirements substitution context.locals
        context.localSchemeRequirements := by
  rfl

@[simp] theorem closeContext_assumptions (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).assumptions =
      context.assumptions.map
        (TypedTraitResolution.applySubstitution substitution) := by
  rfl

@[simp] theorem closeContext_solvedRequirements (substitution : Substitution)
    (context : Context) :
    (closeContext substitution context).solvedRequirements =
      context.solvedRequirements.map (applySolvedRequirement substitution) := by
  rfl

/-- Flexible closing changes the predicates and evidence carried by solved
rows, but never their stable requirement identities or source order. -/
@[simp] theorem closeContext_solvedRequirementIds
    (substitution : Substitution) (context : Context) :
    (closeContext substitution context).solvedRequirements.map
        (fun requirement => requirement.id) =
      context.solvedRequirements.map (fun requirement => requirement.id) := by
  simp [closeContext, List.map_map, Function.comp_def]

@[simp] theorem forLocal_cons_self (substitution : Substitution)
    (locals : Resolved.LocalScope Scheme) (id : Resolved.LocalId)
    (scheme : Scheme) :
    forLocal substitution ((id, scheme) :: locals) id =
      substitution.without scheme.quantified := by
  simp [forLocal, Resolved.LocalScope.lookup?]

theorem forLocal_eq_without_of_lookup?
    {substitution : Substitution} {locals : Resolved.LocalScope Scheme}
    {id : Resolved.LocalId} {scheme : Scheme}
    (found : locals.lookup? id = some scheme) :
    forLocal substitution locals id =
      substitution.without scheme.quantified := by
  simp [forLocal, found]

theorem forLocal_eq_without_of_lookup
    {substitution : Substitution} {locals : Resolved.LocalScope Scheme}
    {id : Resolved.LocalId} {scheme : Scheme}
    (found : Resolved.LocalScope.Lookup locals id scheme) :
    forLocal substitution locals id =
      substitution.without scheme.quantified := by
  exact forLocal_eq_without_of_lookup?
    (Resolved.LocalScope.lookup?_iff.mpr found)

private theorem lookup_applyLocals
    {locals : Resolved.LocalScope Scheme} {id : Resolved.LocalId}
    {scheme : Scheme} (substitution : Substitution)
    (lookup : Resolved.LocalScope.Lookup locals id scheme) :
    Resolved.LocalScope.Lookup (applyLocals substitution locals) id
      (scheme.apply substitution) := by
  induction lookup with
  | head => exact .head
  | tail different _ induction => exact .tail different induction

private theorem lookup_applyLocalSchemeRequirements
    {locals : Resolved.LocalScope Scheme}
    {requirements : Resolved.LocalScope (List LocalSchemeRequirement)}
    {id : Resolved.LocalId} {scheme : Scheme}
    {localRequirements : List LocalSchemeRequirement}
    (substitution : Substitution)
    (schemeLookup : Resolved.LocalScope.Lookup locals id scheme)
    (lookup : Resolved.LocalScope.Lookup requirements id localRequirements) :
    Resolved.LocalScope.Lookup
      (applyLocalSchemeRequirements substitution locals requirements) id
      (localRequirements.map
        (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified))) := by
  induction lookup with
  | head =>
      simp only [applyLocalSchemeRequirements, List.map_cons]
      rw [forLocal_eq_without_of_lookup schemeLookup]
      exact .head
  | tail different _ induction =>
      exact .tail different (induction schemeLookup)

/-- Structural closure transports first-match lookup of a local scheme. -/
theorem LocalLookup.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : Resolved.LocalId} {scheme : Scheme}
    (closes : ContextCloses substitution closedVariables source target)
    (lookup : source.LocalLookup id scheme) :
    target.LocalLookup id (scheme.apply substitution) := by
  rw [← closes.target_eq]
  exact lookup_applyLocals substitution lookup

/-- Qualified metadata follows its scheme lookup and therefore uses the same
capture-avoiding restriction of the outer substitution. -/
theorem LocalSchemeRequirementsLookup.applySubstitution
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : Resolved.LocalId} {scheme : Scheme}
    {requirements : List LocalSchemeRequirement}
    (closes : ContextCloses substitution closedVariables source target)
    (schemeLookup : source.LocalLookup id scheme)
    (lookup : source.LocalSchemeRequirementsLookup id requirements) :
    target.LocalSchemeRequirementsLookup id
      (requirements.map
        (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified))) := by
  rw [← closes.target_eq]
  exact lookup_applyLocalSchemeRequirements substitution schemeLookup lookup

/-- A looked-up scheme inherits the capture protection carried by a valid
flexible context substitution. -/
theorem ContextSubstitutionValid.localSchemeFresh
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {id : Resolved.LocalId} {scheme : Scheme}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (lookup : source.LocalLookup id scheme) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∉ substitution.domain := by
  intro metavariable quantified
  exact valid.localSchemesFresh (id, scheme) lookup.mem metavariable quantified

/-- Extend a valid flexible context substitution with one protected local on
both sides.  Local extension does not change signatures, assumptions, or the
solved-requirement ledger. -/
theorem ContextSubstitutionValid.withLocal
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (id : Resolved.LocalId) (scheme : Scheme)
    (requirements : List LocalSchemeRequirement := [])
    (fresh : id ∉ source.localSchemeRequirements.map Prod.fst)
    (schemeProtected : ∀ metavariable,
      metavariable ∈ scheme.quantified →
        metavariable ∉ substitution.domain) :
    ContextSubstitutionValid substitution closedVariables
      (source.withLocal id scheme requirements)
      (target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified)))) := {
  closes := valid.closes.withLocal id scheme requirements fresh
  localSchemesFresh := valid.localSchemesFresh.withLocal schemeProtected
  implementationRequirements := by
    intro requirement evidence member evidenceEq
    have sourceMember : requirement ∈ source.solvedRequirements := by
      simpa [Context.withLocal] using member
    exact StructuralSubstitution.SolvedRequirementValid.transportContext
      (source := target)
      (target := target.withLocal id (scheme.apply substitution)
        (requirements.map (LocalSchemeRequirement.applySubstitution
          (substitution.without scheme.quantified))))
      rfl rfl
      (valid.implementationRequirements requirement evidence sourceMember
        evidenceEq)
}

/-- Thread semantic flexible-substitution validity through one lexical binder
extension. -/
theorem ContextSubstitutionValid.afterBinder
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binder : TypedBinder}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (extension : BinderExtends owner source binder final) :
    ContextSubstitutionValid substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  cases extension with
  | intro wellFormed fresh =>
      have schemeProtected : ∀ metavariable,
          metavariable ∈ binder.scheme.quantified →
            metavariable ∉ substitution.domain := by
        intro metavariable quantified domainMember
        have closed :=
          (valid.closes.exact.mem_domain_iff metavariable).mp domainMember
        have ambient : metavariable ∈ source.typeVariables := by
          rw [valid.closes.variables_eq]
          exact List.mem_append.mpr (Or.inl closed)
        exact (wellFormed.quantified_fresh metavariable quantified).1 ambient
      have extended := valid.withLocal binder.id binder.scheme
        binder.schemeRequirements fresh.2 schemeProtected
      rw [applyContext_withLocal substitution target.typeVariables source
        binder.id binder.scheme binder.schemeRequirements fresh.2,
        valid.closes.target_eq]
      exact extended

/-- Thread semantic flexible-substitution validity through a source-ordered
binder sequence. -/
theorem ContextSubstitutionValid.afterBinders
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (extension : BindersExtend owner source binders final) :
    ContextSubstitutionValid substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [valid.closes.target_eq]
      exact valid
  | cons head tail induction =>
      have middleValid := valid.afterBinder head
      simpa using induction middleValid

/-- Thread semantic flexible-substitution validity through a monomorphic
binder sequence. -/
theorem ContextSubstitutionValid.afterMonoBinders
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target final : Context} {owner : Resolved.DeclarationId}
    {binders : List TypedBinder} {types : List Ty}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (extension : MonoBindersExtend owner source binders types final) :
    ContextSubstitutionValid substitution closedVariables final
      (applyContext substitution target.typeVariables final) := by
  induction extension generalizing target with
  | nil =>
      rw [valid.closes.target_eq]
      exact valid
  | cons _ head tail induction =>
      have middleValid := valid.afterBinder head
      simpa using induction middleValid

/-- Enter a generalized initializer while preserving semantic substitution
validity.  Its scheme variables stay protected and its qualified predicates
only enlarge the available assumption set. -/
theorem ContextSubstitutionValid.localSchemeInitializer
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context}
    (valid : ContextSubstitutionValid substitution closedVariables source target)
    (binder : TypedBinder)
    (fresh : ∀ metavariable, metavariable ∈ binder.scheme.quantified →
      metavariable ∉ substitution.domain) :
    ContextSubstitutionValid substitution closedVariables
      (localSchemeInitializerContext source binder)
      (localSchemeInitializerContext target
        (binder.applySubstitution substitution)) := {
  closes := valid.closes.localSchemeInitializer binder fresh
  localSchemesFresh := by
    simpa [LocalSchemesFreshFor, localSchemeInitializerContext,
      Context.withTypeVariables, Context.withAssumptions] using
        valid.localSchemesFresh
  implementationRequirements := by
    intro requirement evidence member evidenceEq
    have sourceMember : requirement ∈ source.solvedRequirements := by
      simpa [localSchemeInitializerContext, Context.withTypeVariables,
        Context.withAssumptions] using member
    cases valid.implementationRequirements requirement evidence sourceMember
        evidenceEq with
    | intro evidenceValid =>
        exact .intro (evidenceValid.weakenAssumptions (by
          intro predicate predicateMem
          change predicate ∈ target.assumptions ++ _
          exact List.mem_append_left _ predicateMem))
}

/-- The local-reference case of flexible static transport.  The source
lookup determines one shared mapped binder, and the same composed inner
substitution validates both its raw type and its qualified requirements. -/
theorem ReferenceUseValid.applySubstitution_local
    {substitution : Substitution} {closedVariables : List TypeVarId}
    {source target : Context} {binder : TypedBinder} {type : Ty}
    {actualRequirements : List RequirementId}
    (contextValid :
      ContextSubstitutionValid substitution closedVariables source target)
    (schemeLookup : source.LocalLookup binder.id binder.scheme)
    (requirementsLookup : source.LocalSchemeRequirementsLookup binder.id
      binder.schemeRequirements)
    (instantiation : LocalSchemeInstantiationValid source binder type
      actualRequirements) :
    ReferenceUseValid target (.local binder.id) (substitution.apply type)
      actualRequirements := by
  apply ReferenceUseValid.local (binder := binder.applySubstitution substitution)
  · simpa using LocalLookup.applySubstitution contextValid.closes schemeLookup
  · simpa using LocalSchemeRequirementsLookup.applySubstitution
      contextValid.closes schemeLookup requirementsLookup
  · exact LocalSchemeInstantiationValid.applySubstitution_of_fresh
      contextValid (contextValid.localSchemeFresh schemeLookup) instantiation

/-- A direct builtin callee retains its occurrence identity, empty evidence
spine, and fixed closed function type under flexible substitution. -/
theorem DirectBuiltinCalleeValid.applySubstitution
    {substitution : Substitution} {source : TypedSource}
    {callee : ExpressionId} {function : BuiltinFunctionId}
    (valid : DirectBuiltinCalleeValid source callee function) :
    DirectBuiltinCalleeValid (source.applySubstitution substitution) callee
      function := by
  cases valid with
  | @intro node name _ contains formEq typeEq requirementsEq coercionsEq =>
      refine .intro
        (ContainsExpression.applySubstitution substitution contains)
        (by
          change node.form.applySubstitution substitution =
            .reference name (.builtinFunction function)
          rw [formEq]
          rfl) ?_
        (by simp [requirementsEq])
        (by simp [ExpressionNode.applySubstitution, coercionsEq])
      change substitution.apply node.type = function.type
      rw [typeEq]
      unfold BuiltinFunctionId.type
      rw [apply_function, apply_productMany]
      cases function <;> rfl

@[simp] theorem closeContext_withTypeVariables (substitution : Substitution)
    (context : Context) (variables : List TypeVarId) :
    closeContext substitution (context.withTypeVariables variables) =
      closeContext substitution context := by
  rfl

@[simp] theorem closeContext_withResidualTypeVariables
    (substitution : Substitution) (context : Context) :
    closeContext substitution context.withResidualTypeVariables =
      (closeContext substitution context).withResidualTypeVariables := by
  rfl

@[simp] theorem closeContext_withAssumptions (substitution : Substitution)
    (context : Context) (predicates : List ProgramPredicate) :
    closeContext substitution (context.withAssumptions predicates) =
      (closeContext substitution context).withAssumptions
        (predicates.map
          (TypedTraitResolution.applySubstitution substitution)) := by
  rfl

/-- Closing a generalized initializer removes its temporary flexible binders
and instantiates its local predicate assumptions with the same substitution.
The surrounding assumptions undergo the ordinary context action. -/
@[simp] theorem closeContext_localSchemeInitializerContext
    (substitution : Substitution) (context : Context)
    (binder : TypedBinder) :
    closeContext substitution (localSchemeInitializerContext context binder) =
      (closeContext substitution context).withAssumptions
        ((closeContext substitution context).assumptions ++
          instantiateLocalSchemePredicates substitution binder) := by
  cases context
  simp [localSchemeInitializerContext, Context.withTypeVariables,
    Context.withAssumptions, closeContext, applyContext,
    instantiateLocalSchemePredicates]

/-- In a runtime context with no ambient lexical metavariables, an exact
scheme substitution is exact for the complete generalized-initializer scope. -/
theorem ExactSubstitution.localSchemeInitializerContext
    {substitution : Substitution} {context : Context} {binder : TypedBinder}
    (outerVariablesClosed : context.typeVariables = [])
    (exact : SourceSemantics.ExactSubstitution substitution
      binder.scheme.quantified) :
    SourceSemantics.ExactSubstitution substitution
      (localSchemeInitializerContext context binder).typeVariables := by
  change SourceSemantics.ExactSubstitution substitution
    (context.typeVariables ++ binder.scheme.quantified)
  rw [outerVariablesClosed]
  simpa using exact

end Solcore.SourceSemantics.FlexibleSubstitution
