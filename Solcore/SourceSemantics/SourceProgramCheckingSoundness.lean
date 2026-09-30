import Solcore.SourceSemantics.SourceInferenceBodyTypingBridge

/-!
Downstream bridge from successful source checking to complete declarative
program validity.  The lower-level checker bridge intentionally does not
import inference soundness, so body proofs are assembled here.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend Frontend.SourceInference

private theorem eq_of_mem_of_nodup_map
    {α β : Type} {items : List α} {project : α → β}
    (unique : (items.map project).Nodup)
    {left right : α} (leftMember : left ∈ items)
    (rightMember : right ∈ items)
    (projectEq : project left = project right) : left = right := by
  induction items generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (headFresh (projectEq ▸
            List.mem_map_of_mem rightMember))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (headFresh (projectEq.symm ▸
            List.mem_map_of_mem leftMember))
        · exact induction tailUnique leftMember rightMember projectEq

private theorem predicateWellFormed_applySubstitution_eq_self
    {context : Context} {predicate : ProgramPredicate}
    (formed : PredicateWellFormed context predicate)
    (substitution : TypeSystem.Substitution) :
    TypedTraitResolution.applySubstitution substitution predicate =
      predicate := by
  have subjectFixed : substitution.apply predicate.subject =
      predicate.subject :=
    StructuralSubstitution.TypeWellScoped.applySubstitution_eq_self
      substitution formed.subject.typeWellScoped
  have argumentsFixed : predicate.arguments.map substitution.apply =
      predicate.arguments := by
    calc
      predicate.arguments.map substitution.apply =
          predicate.arguments.map id := by
        apply List.map_congr_left
        intro argument member
        exact StructuralSubstitution.TypeWellScoped.applySubstitution_eq_self
          substitution (formed.arguments argument member).typeWellScoped
      _ = predicate.arguments := by simp
  cases predicate with
  | mk trait subject arguments =>
      simp [TypedTraitResolution.applySubstitution, subjectFixed,
        argumentsFixed]

private theorem predicatesWellFormed_applySubstitution_eq_self
    {context : Context} {predicates : List ProgramPredicate}
    (formed : PredicatesWellFormed context predicates)
    (substitution : TypeSystem.Substitution) :
    predicates.map (TypedTraitResolution.applySubstitution substitution) =
      predicates := by
  induction predicates with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · exact predicateWellFormed_applySubstitution_eq_self
          (formed predicate (by simp)) substitution
      · exact induction (fun candidate member =>
          formed candidate (by simp [member]))

/-- All assumptions of a cataloged implementation method are closed under
flexible inference substitution, including the trait predicates instantiated
at the implementation head. -/
private theorem methodAssumptions_applySubstitution_eq_self
    {signatures : ProgramSignatures}
    {implementation : ProgramImplementationSignature}
    {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature}
    (catalog : SignatureCatalogWellFormed signatures)
    (implementationMember : implementation ∈ signatures.implementations)
    (methodMember : method ∈ implementation.methods)
    (traitMember : trait ∈ signatures.traits)
    (headTrait : implementation.head.trait = .declaration trait.id)
    (substitution : TypeSystem.Substitution) :
    (implementation.methodAssumptions trait method).map
      (TypedTraitResolution.applySubstitution substitution) =
        implementation.methodAssumptions trait method := by
  have implementationWellFormed :=
    catalog.implementations_semantic implementation implementationMember
  have methodWellFormed :=
    implementationWellFormed.methods method methodMember
  obtain ⟨catalogTrait, catalogTraitMember, catalogHeadTrait, _, _,
    requiredPredicates⟩ := implementationWellFormed.trait_catalog
  have catalogTraitId : catalogTrait.id = trait.id := by
    have equal := catalogHeadTrait.symm.trans headTrait
    injection equal
  have catalogTraitEq : catalogTrait = trait :=
    Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids
      catalogTraitMember traitMember catalogTraitId
  subst catalogTrait
  let instantiated :=
    trait.wherePredicates.map (ProgramPredicate.applyParameters
      (trait.parameters.zip
        (implementation.head.subject :: implementation.head.arguments)))
  have instantiatedFormed : PredicatesWellFormed
      (signatureContext signatures implementation.id implementation.parameters
        implementation.wherePredicates) instantiated := by
    intro predicate member
    exact implementationWellFormed.predicates predicate
      (requiredPredicates predicate member)
  have instantiatedFixed :=
    predicatesWellFormed_applySubstitution_eq_self instantiatedFormed
      substitution
  have implementationFixed :=
    predicatesWellFormed_applySubstitution_eq_self
      implementationWellFormed.predicates substitution
  have methodFixed :=
    predicatesWellFormed_applySubstitution_eq_self
      methodWellFormed.predicates substitution
  simp only [ProgramImplementationSignature.methodAssumptions,
    List.map_append]
  change instantiated.map
      (TypedTraitResolution.applySubstitution substitution) ++
        implementation.wherePredicates.map
          (TypedTraitResolution.applySubstitution substitution) ++
        method.wherePredicates.map
          (TypedTraitResolution.applySubstitution substitution) =
      instantiated ++ implementation.wherePredicates ++ method.wherePredicates
  rw [instantiatedFixed, implementationFixed, methodFixed]

/-- The deep result still to be reconstructed from recursive executable
statement inference.  The lexical context is quantified so that a header
proof can choose its canonical input extension independently. -/
def CheckedBodyHasType (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (checked : CheckedFunction) : Prop :=
  ∃ facts : BodyFacts,
    (∀ lexicalContext,
      MonoBindersExtend signature.id
        (checkedBodyContext signatures signature checked)
        checked.typedBody.inputs signature.parameterTypes lexicalContext →
      BodyHasType checked.typedBody lexicalContext
        (TypeSystem.Ty.productMany signature.returnTypes) facts) ∧
    facts.type = TypeSystem.Ty.productMany signature.returnTypes

/-- The recursive inference proof can stop at the exact statement-root list:
the closed-body completion step is supplied by the control-typing bridge. -/
def CheckedBodyStatementsHaveType (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (checked : CheckedFunction) : Prop :=
  ∀ statements : List StatementId,
    checked.typedBody.roots = statements.map NodeId.statement →
    ∃ facts : BodyFacts,
      facts.type = TypeSystem.Ty.productMany signature.returnTypes ∧
      ∀ lexicalContext,
        MonoBindersExtend signature.id
          (checkedBodyContext signatures signature checked)
          checked.typedBody.inputs signature.parameterTypes lexicalContext →
        ∃ finalContext,
          StatementsHaveType checked.typedBody
            { returnType := TypeSystem.Ty.productMany signature.returnTypes }
            lexicalContext statements finalContext facts

/-- A successful body check supplies the statement-only roots; the recursive
statement derivation then yields the complete `BodyHasType` judgment. -/
theorem checkedBodyHasType_ofStatements
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked)
    (statementsTyping :
      CheckedBodyStatementsHaveType signatures signature checked) :
    CheckedBodyHasType signatures signature checked := by
  obtain ⟨body, roots⟩ :=
    SourceInferenceSoundness.checkFunctionBody_success_statementRoots success
  obtain ⟨facts, factsType, typing⟩ :=
    statementsTyping body.statements roots
  refine ⟨facts, ?_, factsType⟩
  intro lexicalContext inputsExtend
  obtain ⟨finalContext, typed⟩ := typing lexicalContext inputsExtend
  exact SourceInferenceSoundness.bodyHasType_of_statementRoots roots typed
    factsType

/-- The complete body judgment follows from the checker-derived header and
structural certificates once deep statement typing is supplied.  This isolates
the one remaining recursive inference-soundness obligation. -/
theorem bodyDefinitionHasType_ofCheckFunctionBody
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    {facts : BodyFacts}
    (header : CheckedBodyHeaderWellFormed signatures signature checked)
    (predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution) =
          signature.scheme.predicates)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked)
    (bodyTyping : ∀ lexicalContext,
      MonoBindersExtend signature.id
        (checkedBodyContext signatures signature checked)
        checked.typedBody.inputs signature.parameterTypes lexicalContext →
      BodyHasType checked.typedBody lexicalContext
        (TypeSystem.Ty.productMany signature.returnTypes) facts)
    (factsType : facts.type =
      TypeSystem.Ty.productMany signature.returnTypes) :
    BodyDefinitionHasType signatures signature.scheme.parameters
      signature.scheme.predicates signature.parameterNames
      signature.parameterTypes signature.parameterComptime signature.returnTypes
      signature.returnComptime (BodyDefinition.ofChecked checked) facts := by
  obtain ⟨lexicalContext, inputsExtend⟩ := header.inputs_extend
  have graphClosed :=
    SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed
      success
  have localOwnership :=
    SourceInferenceSoundness.checkFunctionBody_success_localIdentityOwnership
      success
  have requirementOwnership :=
    SourceInferenceSoundness.checkFunctionBody_success_requirementOwnership
      success
  have requirementLedger : ScopedRequirementLedgerWellFormed
      (checkedBodyContext signatures signature checked) checked.typedBody := by
    apply ScopedRequirementLedgerWellFormed.transportContext
      (source := SourceInferenceSoundness.checkedFinalizedRequirementContext
        signatures signature checked)
      (target := checkedBodyContext signatures signature checked)
    · rfl
    · exact predicatesFixed.symm
    · rfl
    · exact SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed
        success
  refine .intro (lexicalContext := lexicalContext) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact header.source_owner
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using header.parameter_binders
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using header.parameter_types
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using header.return_types
  · exact header.callable_type
  · exact header.result_type
  · exact header.return_comptime
  · exact header.input_names
  · exact header.input_comptime
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using inputsExtend
  · exact graphClosed
  · exact localOwnership
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using requirementLedger
  · simpa [BodyDefinition.ofChecked, checkedBodyContext,
      header.declaration_eq] using requirementOwnership
  · exact bodyTyping lexicalContext inputsExtend
  · exact factsType

/-- For a top-level function, successful checking already supplies every
nonrecursive premise of semantic validity. -/
theorem functionDefinitionValid_ofCheckProgram
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    {function : CheckedFunction}
    (member : function ∈ checked.functions)
    (deep : ∀ signature, signature ∈ checked.signatures.functions →
      checkFunctionBody checked.environment checked.signatures signature fuel =
        .ok function →
      CheckedBodyHasType checked.signatures signature function) :
    FunctionDefinition.Valid checked.signatures
      (FunctionDefinition.ofChecked function) := by
  obtain ⟨signature, signatureMember, bodySuccess⟩ :=
    Frontend.checkProgram_success_function_body success member
  obtain ⟨headerSignature, headerMember, header⟩ :=
    checkedFunctionHeaderWellFormed_ofCheckProgram success member
  have signatureEq : headerSignature = signature := by
    have catalog := SignatureCatalogWellFormed.ofCheckProgram success
    have ids := catalog.function_ids
    have leftId : headerSignature.id = function.declaration :=
      header.declaration_eq.symm
    have rightId : function.declaration = signature.id :=
      checkFunctionBody_success_declaration bodySuccess
    exact eq_of_mem_of_nodup_map ids headerMember signatureMember
      (leftId.trans rightId)
  subst headerSignature
  obtain ⟨facts, bodyTyping, factsType⟩ :=
    deep signature signatureMember bodySuccess
  have predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution function.substitution) =
          signature.scheme.predicates :=
    ((Frontend.checkProgram_success_signature_formation success).functions
      signature signatureMember).2.2.apply_eq_self function.substitution
  exact .intro signatureMember header.declaration_eq
    (bodyDefinitionHasType_ofCheckFunctionBody header predicatesFixed
      bodySuccess bodyTyping factsType)

/-- Checked method provenance and the signature catalog determine its exact
trait method and body context.  Deep body typing is the remaining independent
premise. -/
theorem methodDefinitionValid_ofCheckProgram
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    {checkedMethod : CheckedImplementationMethod}
    (member : checkedMethod ∈ checked.methods)
    (deep : ∀ implementation method trait,
      implementation ∈ checked.signatures.implementations →
      method ∈ implementation.methods →
      checked.signatures.trait? method.traitMethod.trait = some trait →
      checkFunctionBody checked.environment checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
          .ok checkedMethod.checked →
      CheckedBodyHasType checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method)
        checkedMethod.checked) :
    MethodDefinition.Valid checked.signatures
      (MethodDefinition.ofChecked checkedMethod) := by
  obtain ⟨implementation, method, trait, implementationMember, methodMember,
    traitLookup, methodId, bodySuccess⟩ :=
    Frontend.checkProgram_success_method_body success member
  let catalog := SignatureCatalogWellFormed.ofCheckProgram success
  have implementationWellFormed :=
    catalog.implementations_semantic implementation implementationMember
  have methodWellFormed :=
    implementationWellFormed.methods method methodMember
  obtain ⟨semanticTrait, traitMethod, semanticTraitMember, selectedHeadTrait,
    traitMethodMember, traitMethodId, _, _, _, _, _, _⟩ :=
    methodWellFormed.trait_method
  have rawLookup :
      checked.signatures.traits.find?
        (fun candidate => decide (candidate.id = method.traitMethod.trait)) =
          some trait := by
    simpa [ProgramSignatures.trait?] using traitLookup
  have selectedMember : trait ∈ checked.signatures.traits :=
    List.mem_of_find?_eq_some rawLookup
  have selectedId : trait.id = method.traitMethod.trait :=
    of_decide_eq_true (List.find?_some
      (p := fun candidate : ProgramTraitSignature =>
        decide (candidate.id = method.traitMethod.trait)) rawLookup)
  have semanticTraitWellFormed :=
    catalog.traits_semantic semanticTrait semanticTraitMember
  have traitMethodWellFormed :=
    semanticTraitWellFormed.methods traitMethod traitMethodMember
  have semanticId : semanticTrait.id = method.traitMethod.trait := by
    rw [← traitMethodWellFormed.owner]
    exact congrArg ProgramTraitMethodId.trait traitMethodId
  have traitEq : trait = semanticTrait :=
    Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids
      selectedMember semanticTraitMember (selectedId.trans semanticId.symm)
  subst semanticTrait
  let signature :=
    implementation.functionSignatureOfMethodWithTrait trait method
  have header : CheckedBodyHeaderWellFormed checked.signatures signature
      checkedMethod.checked :=
    CheckedBodyHeaderWellFormed.ofCheckImplementationMethod
      implementationWellFormed methodWellFormed bodySuccess
  obtain ⟨facts, bodyTyping, factsType⟩ :=
    deep implementation method trait implementationMember methodMember
      traitLookup bodySuccess
  have predicatesFixed :
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution
          checkedMethod.checked.substitution) =
        signature.scheme.predicates := by
    simpa [signature,
      ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod] using
      methodAssumptions_applySubstitution_eq_self catalog
        implementationMember methodMember selectedMember
        selectedHeadTrait checkedMethod.checked.substitution
  have bodyValid := bodyDefinitionHasType_ofCheckFunctionBody header
    predicatesFixed bodySuccess bodyTyping factsType
  refine .intro (facts := facts) implementationMember methodMember methodId
    methodWellFormed.owner selectedMember traitMethodMember ?_ ?_ ?_ ?_
  · exact traitMethodId.symm
  · exact traitMethodWellFormed.owner
  · simpa [MethodDefinition.ofChecked, BodyDefinition.ofChecked,
      signature, ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod]
      using header.declaration_eq
  · simpa [MethodDefinition.ofChecked, signature,
      ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
      ProgramImplementationSignature.functionSignatureOfMethod,
      ProgramFunctionSignature.parameterNames,
      ProgramFunctionSignature.parameterTypes,
      ProgramFunctionSignature.parameterComptime,
      ProgramImplMethodSignature.parameterNames,
      ProgramImplMethodSignature.parameterTypes,
      ProgramImplMethodSignature.parameterComptime,
      methodAssumptions] using bodyValid

/-- Exactly the recursive body-typing results needed to finish a checked
program.  All declaration identities, signature formation, ownership, and
requirement evidence follow from checker success independently. -/
structure CheckedProgramBodiesHaveType (checked : CheckedProgram)
    (fuel : Nat) : Prop where
  functions : ∀ function, function ∈ checked.functions →
    ∀ signature, signature ∈ checked.signatures.functions →
      checkFunctionBody checked.environment checked.signatures signature fuel =
        .ok function →
      CheckedBodyHasType checked.signatures signature function
  methods : ∀ checkedMethod, checkedMethod ∈ checked.methods →
    ∀ implementation method trait,
      implementation ∈ checked.signatures.implementations →
      method ∈ implementation.methods →
      checked.signatures.trait? method.traitMethod.trait = some trait →
      checkFunctionBody checked.environment checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
          .ok checkedMethod.checked →
      CheckedBodyHasType checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method)
        checkedMethod.checked

/-- The precise remaining recursive soundness certificate: each successfully
inferred block has a declarative statement-list derivation in the canonical
input context and the checker's finalized typed source. -/
structure CheckedProgramBodiesHaveStatementTyping (checked : CheckedProgram)
    (fuel : Nat) : Prop where
  functions : ∀ function, function ∈ checked.functions →
    ∀ signature, signature ∈ checked.signatures.functions →
      checkFunctionBody checked.environment checked.signatures signature fuel =
        .ok function →
      CheckedBodyStatementsHaveType checked.signatures signature function
  methods : ∀ checkedMethod, checkedMethod ∈ checked.methods →
    ∀ implementation method trait,
      implementation ∈ checked.signatures.implementations →
      method ∈ implementation.methods →
      checked.signatures.trait? method.traitMethod.trait = some trait →
      checkFunctionBody checked.environment checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method) fuel =
          .ok checkedMethod.checked →
      CheckedBodyStatementsHaveType checked.signatures
        (implementation.functionSignatureOfMethodWithTrait trait method)
        checkedMethod.checked

/-- The body root and control-completion bridges discharge the remaining
whole-body bookkeeping once all inferred statement lists are typed. -/
theorem CheckedProgramBodiesHaveStatementTyping.bodyTypes
    {checked : CheckedProgram} {fuel : Nat}
    (deep : CheckedProgramBodiesHaveStatementTyping checked fuel) :
    CheckedProgramBodiesHaveType checked fuel := by
  constructor
  · intro function member signature signatureMember bodySuccess
    exact checkedBodyHasType_ofStatements bodySuccess
      (deep.functions function member signature signatureMember bodySuccess)
  · intro checkedMethod member implementation method trait
      implementationMember methodMember traitLookup bodySuccess
    exact checkedBodyHasType_ofStatements bodySuccess
      (deep.methods checkedMethod member implementation method trait
        implementationMember methodMember traitLookup bodySuccess)

/-- Checker success and deep inference soundness assemble the complete
declarative program judgment with no caller-supplied function or method
validity premises. -/
theorem programWellFormed_ofCheckProgram_deep
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (deep : CheckedProgramBodiesHaveType checked fuel) :
    ProgramWellFormed (Program.ofChecked checked) := by
  apply CheckedProgramWellFormedConditions.programWellFormed
  apply CheckedProgramWellFormedConditions.ofCheckProgram success
  · intro function member
    exact functionDefinitionValid_ofCheckProgram success member
      (deep.functions function member)
  · intro method member
    exact methodDefinitionValid_ofCheckProgram success member
      (deep.methods method member)

/-- The complete checker-to-program bridge reduces to soundness of the
recursive statement inference pass. -/
theorem programWellFormed_ofCheckProgram_statements
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked)
    (deep : CheckedProgramBodiesHaveStatementTyping checked fuel) :
    ProgramWellFormed (Program.ofChecked checked) :=
  programWellFormed_ofCheckProgram_deep success deep.bodyTypes

end Solcore.SourceSemantics
