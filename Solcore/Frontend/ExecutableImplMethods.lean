import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceSpecialization

/-!
Checked source bodies for the first executable implementation-method profile.

This boundary accepts explicitly sized implementation evidence whose sole
method carries no additional predicates.  A generic implementation is admitted
only when its closed evidence goal determines every declaration parameter.
Closed implementation-level predicates must correspond exactly to the evidence
premises, while trait-level predicates are instantiated at the closed evidence
goal.  Both become static assumptions of the synthetic method.  The boundary
validates the retained method catalog defensively, checks the generic method as
an ordinary synthetic function, and closes it through the existing source
specializer before exposing it to runtime lowering.
-/

set_option autoImplicit false

namespace Solcore.Frontend.ExecutableImplMethods

open TypeSystem

/-- A cataloged implementation method whose source body has passed the ordinary
source checker under its synthetic callable signature. -/
structure CheckedMethod where
  id : ProgramImplMethodId
  traitMethod : ProgramTraitMethodSignature
  traitPredicates : List ProgramPredicate
  implementationPredicates : List ProgramPredicate
  implementationPremises : List TypedTraitResolution.Evidence
  synthetic : ProgramFunctionSignature
  checked : SourceInference.CheckedFunction
  specialized : SourceSpecialization.SpecializedFunction
  deriving Repr

/-- The first reason that a purportedly closed evidence goal still contains a
non-runtime type. -/
inductive NonClosedType where
  | flexible (id : TypeVarId)
  | rigid (id : TypeParameterId)
  | error
  deriving Repr, DecidableEq

/-- Explicit rejections at the deliberately narrow executable-method boundary. -/
inductive Error where
  | evidencePremisesPresent
      (implementation : Resolved.DeclarationId) (count : Nat)
  | evidencePremiseCountMismatch
      (implementation : Resolved.DeclarationId) (expected actual : Nat)
  | evidencePremiseGoalMismatch
      (implementation : Resolved.DeclarationId) (index : Nat)
      (expected actual : ProgramPredicate)
  | evidenceGoalArityMismatch
      (trait : Resolved.DeclarationId) (expected actual : Nat)
  | evidenceGoalNotClosed
      (goal : ProgramPredicate) (reason : NonClosedType)
  | evidenceResolutionNoSolution (goal : ProgramPredicate)
  | evidenceResolutionInconclusive
      (reason : TraitResolution.InconclusiveReason
        Resolved.DeclarationId Ty Resolved.DeclarationId)
  | evidenceNotSelected
      (implementation : Resolved.DeclarationId) (goal : ProgramPredicate)
  | missingImplementation (implementation : Resolved.DeclarationId)
  | duplicateImplementations
      (implementation : Resolved.DeclarationId) (count : Nat)
  /-- Retained for source compatibility with the original monomorphic gate.
  Determined generic parameters now specialize instead. -/
  | implementationParametersPresent
      (implementation : Resolved.DeclarationId)
      (parameters : List TypeParameterId)
  | implementationParameterNotDetermined
      (implementation : Resolved.DeclarationId)
      (parameter : TypeParameterId) (reason : NonClosedType)
  | implementationHeadMismatch
      (implementation : Resolved.DeclarationId)
      (evidence catalog : ProgramPredicate)
  | implementationPredicatesPresent
      (implementation : Resolved.DeclarationId)
      (predicates : List ProgramPredicate)
  | implementationPredicateNotClosed
      (implementation : Resolved.DeclarationId) (predicate : ProgramPredicate)
      (reason : NonClosedType)
  | missingTrait (trait : Resolved.DeclarationId)
  | duplicateTraits (trait : Resolved.DeclarationId) (count : Nat)
  | traitArityMismatch
      (trait : Resolved.DeclarationId) (expected actual : Nat)
  /-- Retained for source compatibility with the former all-predicates gate.
  The current profile instantiates closed trait predicates instead. -/
  | traitPredicatesPresent
      (trait : Resolved.DeclarationId) (predicates : List ProgramPredicate)
  | traitPredicateNotClosed
      (trait : Resolved.DeclarationId) (predicate : ProgramPredicate)
      (reason : NonClosedType)
  | missingImplementationMethod
      (implementation : Resolved.DeclarationId) (expectedName : String)
  | multipleImplementationMethods
      (implementation : Resolved.DeclarationId) (count : Nat)
  | missingTraitMethod
      (trait : Resolved.DeclarationId) (expectedName : String)
  | multipleTraitMethods (trait : Resolved.DeclarationId) (count : Nat)
  | implementationMethodNameMismatch
      (method : ProgramImplMethodId) (expected actual : String)
  | traitMethodNameMismatch
      (method : ProgramTraitMethodId) (expected actual : String)
  | implementationMethodPredicatesPresent
      (method : ProgramImplMethodId) (predicates : List ProgramPredicate)
  | traitMethodPredicatesPresent
      (method : ProgramTraitMethodId) (predicates : List ProgramPredicate)
  | implementationMethodOwnerMismatch
      (method : ProgramImplMethodId)
      (expected actual : Resolved.DeclarationId)
  | traitMethodOwnerMismatch
      (method : ProgramTraitMethodId)
      (expected actual : Resolved.DeclarationId)
  | methodAssociationMismatch
      (method : ProgramImplMethodId)
      (expected actual : ProgramTraitMethodId)
  | sourceInference (error : SourceInference.Error)
  | specialization (error : SourceSpecialization.Error)
  | specializedAssumptionsMismatch
      (implementation : Resolved.DeclarationId)
      (expected actual : List ProgramPredicate)
  deriving Repr, DecidableEq

private def exactImplementation
    (program : CheckedProgram) (id : Resolved.DeclarationId) :
    Except Error ProgramImplementationSignature :=
  match program.signatures.implementations.filter fun implementation =>
      decide (implementation.id = id) with
  | [] => .error (.missingImplementation id)
  | [implementation] => .ok implementation
  | implementations =>
      .error (.duplicateImplementations id implementations.length)

private def exactTrait
    (program : CheckedProgram) (id : Resolved.DeclarationId) :
    Except Error ProgramTraitSignature :=
  match program.signatures.traits.filter fun trait => decide (trait.id = id) with
  | [] => .error (.missingTrait id)
  | [trait] => .ok trait
  | traits => .error (.duplicateTraits id traits.length)

private def onlyImplementationMethod
    (implementation : ProgramImplementationSignature) (expectedName : String) :
    Except Error ProgramImplMethodSignature :=
  match implementation.methods with
  | [] => .error (.missingImplementationMethod implementation.id expectedName)
  | [method] => .ok method
  | methods =>
      .error (.multipleImplementationMethods implementation.id methods.length)

private def onlyTraitMethod
    (trait : ProgramTraitSignature) (expectedName : String) :
    Except Error ProgramTraitMethodSignature :=
  match trait.methods with
  | [] => .error (.missingTraitMethod trait.id expectedName)
  | [method] => .ok method
  | methods => .error (.multipleTraitMethods trait.id methods.length)

private def firstNonClosedType : Ty → Option NonClosedType
  | .variable id => some (.flexible id)
  | .parameter id => some (.rigid id)
  | .constructor _ => none
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      (firstNonClosedType left).orElse fun _ => firstNonClosedType right
  | .proxy inner
  | .comptime inner => firstNonClosedType inner
  | .error => some .error

private def firstNonClosedGoalType (goal : ProgramPredicate) :
    Option NonClosedType :=
  (firstNonClosedType goal.subject).orElse fun _ =>
    goal.arguments.findSome? firstNonClosedType

private def validateEvidencePremiseGoals
    (implementation : Resolved.DeclarationId) :
    Nat → List ProgramPredicate → List TypedTraitResolution.Evidence →
      Except Error Unit
  | _, [], [] => pure ()
  | index, predicate :: predicates, evidence :: rest => do
      let .byImpl actual _ _ := evidence
      unless actual = predicate do
        throw (.evidencePremiseGoalMismatch implementation index predicate actual)
      validateEvidencePremiseGoals implementation (index + 1) predicates rest
  | _, _, _ => pure ()

private def validateEvidencePremises
    (implementation : Resolved.DeclarationId)
    (predicates : List ProgramPredicate)
    (evidence : List TypedTraitResolution.Evidence) : Except Error Unit := do
  unless predicates.length = evidence.length do
    throw (.evidencePremiseCountMismatch implementation predicates.length
      evidence.length)
  validateEvidencePremiseGoals implementation 0 predicates evidence

private def validateSelectedEvidence (program : CheckedProgram)
    (implementation : Resolved.DeclarationId) (goal : ProgramPredicate)
    (evidence : TypedTraitResolution.Evidence) : Except Error Unit :=
  match (TypedTraitResolution.resolve program.signatures.implRules 32
      goal).outcome with
  | .noSolution => .error (.evidenceResolutionNoSolution goal)
  | .inconclusive reason => .error (.evidenceResolutionInconclusive reason)
  | .success selected =>
      if selected == evidence then
        .ok ()
      else
        .error (.evidenceNotSelected implementation goal)

private def validateDeterminedParameters
    (implementation : Resolved.DeclarationId)
    (substitution : ParameterSubstitution) : Except Error Unit := do
  for (parameter, type) in substitution do
    match firstNonClosedType type with
    | some reason =>
        throw (.implementationParameterNotDetermined implementation parameter
          reason)
    | none => pure ()

private def closedSyntheticSignature
    (generic : ProgramFunctionSignature)
    (specialized : SourceSpecialization.SpecializedFunction) :
    ProgramFunctionSignature := {
  generic with
  parameterTypes := generic.parameterTypes.map
    specialized.parameterSubstitution.apply
  returnTypes := generic.returnTypes.map
    specialized.parameterSubstitution.apply
  scheme := {
    parameters := []
    predicates := specialized.assumptions
    body := specialized.function.type
  }
}

/-- Select and check the sole executable method justified by one closed piece
of trait evidence.  The evidence goal must determine every implementation
parameter.  Trait declaration predicates and exact closed implementation
premises become static method assumptions; runtime dictionaries and
method-level predicates remain explicit later profiles. -/
def checkMethodWithArity
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedTraitArity : Nat) (expectedName : String) :
    Except Error CheckedMethod := do
  let .byImpl goal implementationId premises := evidence
  let goalArity := goal.arguments.length + 1
  unless goalArity = expectedTraitArity do
    throw (.evidenceGoalArityMismatch goal.trait expectedTraitArity goalArity)
  let implementation ← exactImplementation program implementationId
  match firstNonClosedGoalType goal with
  | some reason => throw (.evidenceGoalNotClosed goal reason)
  | none => pure ()
  let headMatch ← match TypedTraitResolution.matchImplHeadWithParameters?
      implementation.parameters implementation.implRule goal with
    | some headMatch => pure headMatch
    | none => throw (.implementationHeadMismatch implementation.id goal
        implementation.head)
  validateDeterminedParameters implementation.id
    headMatch.parameterSubstitution
  for predicate in headMatch.wherePredicates do
    match firstNonClosedGoalType predicate with
    | some reason => throw (.implementationPredicateNotClosed implementation.id
        predicate reason)
    | none => pure ()
  validateEvidencePremises implementation.id headMatch.wherePredicates premises
  validateSelectedEvidence program implementation.id goal evidence
  let trait ← exactTrait program goal.trait
  unless trait.parameters.length = expectedTraitArity do
    throw (.traitArityMismatch trait.id expectedTraitArity trait.parameters.length)
  let traitParameterSubstitution : ParameterSubstitution :=
    trait.parameters.zip (goal.subject :: goal.arguments)
  let traitPredicates := trait.wherePredicates.map
    (ProgramPredicate.applyParameters traitParameterSubstitution)
  for predicate in traitPredicates do
    match firstNonClosedGoalType predicate with
    | some reason => throw (.traitPredicateNotClosed trait.id predicate reason)
    | none => pure ()
  let genericTraitParameterSubstitution : ParameterSubstitution :=
    trait.parameters.zip
      (implementation.head.subject :: implementation.head.arguments)
  let genericTraitPredicates := trait.wherePredicates.map
    (ProgramPredicate.applyParameters genericTraitParameterSubstitution)
  let implementationMethod ←
    onlyImplementationMethod implementation expectedName
  let traitMethod ← onlyTraitMethod trait expectedName
  unless implementationMethod.name = expectedName do
    throw (.implementationMethodNameMismatch implementationMethod.id
      expectedName implementationMethod.name)
  unless traitMethod.name = expectedName do
    throw (.traitMethodNameMismatch traitMethod.id expectedName traitMethod.name)
  unless implementationMethod.wherePredicates.isEmpty do
    throw (.implementationMethodPredicatesPresent implementationMethod.id
      implementationMethod.wherePredicates)
  unless traitMethod.wherePredicates.isEmpty do
    throw (.traitMethodPredicatesPresent traitMethod.id
      traitMethod.wherePredicates)
  unless implementationMethod.id.implementation = implementation.id do
    throw (.implementationMethodOwnerMismatch implementationMethod.id
      implementation.id implementationMethod.id.implementation)
  unless traitMethod.id.trait = trait.id do
    throw (.traitMethodOwnerMismatch traitMethod.id trait.id
      traitMethod.id.trait)
  unless implementationMethod.traitMethod = traitMethod.id do
    throw (.methodAssociationMismatch implementationMethod.id traitMethod.id
      implementationMethod.traitMethod)
  let baseSynthetic :=
    implementation.functionSignatureOfMethod implementationMethod
  let genericSynthetic := {
    baseSynthetic with
    scheme := {
      baseSynthetic.scheme with
      predicates := genericTraitPredicates ++ baseSynthetic.scheme.predicates
    }
  }
  let genericChecked ← SourceInference.checkFunctionBody program.environment
    program.signatures genericSynthetic |>.mapError Error.sourceInference
  let specialized ← SourceSpecialization.specializeFunction genericSynthetic
    genericChecked headMatch.parameterSubstitution |>.mapError
      Error.specialization
  let expectedAssumptions := traitPredicates ++ headMatch.wherePredicates
  unless specialized.assumptions = expectedAssumptions do
    throw (.specializedAssumptionsMismatch implementation.id
      expectedAssumptions specialized.assumptions)
  let synthetic := closedSyntheticSignature genericSynthetic specialized
  pure {
    id := implementationMethod.id
    traitMethod
    traitPredicates
    implementationPredicates := headMatch.wherePredicates
    implementationPremises := premises
    synthetic
    checked := specialized.function
    specialized
  }

/-- Compatibility name retained from the monomorphic executable profile.
Generic implementations whose parameters are fully determined by a closed goal
now pass through the same entry. -/
def checkMonomorphicMethodWithArity
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedTraitArity : Nat) (expectedName : String) :
    Except Error CheckedMethod :=
  checkMethodWithArity program evidence expectedTraitArity expectedName

/-- Compatibility name retained from the original no-premise profile.  Closed
implementation predicates and their exact evidence premises, including those
of a ground-specializable generic implementation, are now accepted here. -/
def checkMonomorphicPremiseFreeMethodWithArity
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedTraitArity : Nat) (expectedName : String) :
    Except Error CheckedMethod :=
  checkMethodWithArity program evidence expectedTraitArity
    expectedName

/-- Canonical one-parameter entry for the current executable method profile. -/
def checkMethod
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedName : String) : Except Error CheckedMethod :=
  checkMethodWithArity program evidence 1 expectedName

/-- Compatibility name retained from the monomorphic executable profile. -/
def checkMonomorphicMethod
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedName : String) : Except Error CheckedMethod :=
  checkMethod program evidence expectedName

/-- Compatibility entry for the original one-parameter runtime trait profile.
Consumers of multi-parameter traits must opt into the explicit-arity entry. -/
def checkMonomorphicPremiseFreeMethod
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedName : String) : Except Error CheckedMethod :=
  checkMethod program evidence expectedName

end Solcore.Frontend.ExecutableImplMethods
