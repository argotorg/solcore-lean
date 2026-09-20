import Solcore.Frontend.ProgramChecking

/-!
Checked source bodies for the first executable implementation-method profile.

This boundary intentionally accepts only explicitly sized, monomorphic,
premise-free implementation evidence whose implementation and sole method
carry no additional predicates.  Trait-level predicates are instantiated at
the closed evidence goal and retained as static assumptions of the synthetic
method; executing a body which consumes them remains a downstream policy.  The
boundary validates the retained method catalog defensively, projects the
implementation method to an ordinary synthetic function, and runs the existing
source body checker before exposing it to runtime lowering.
-/

set_option autoImplicit false

namespace Solcore.Frontend.ExecutableImplMethods

open TypeSystem

/-- A cataloged implementation method whose source body has passed the ordinary
source checker under its synthetic callable signature. -/
structure CheckedMethod where
  id : ProgramImplMethodId
  traitMethod : ProgramTraitMethodSignature
  synthetic : ProgramFunctionSignature
  checked : SourceInference.CheckedFunction
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
  | evidenceGoalArityMismatch
      (trait : Resolved.DeclarationId) (expected actual : Nat)
  | evidenceGoalNotClosed
      (goal : ProgramPredicate) (reason : NonClosedType)
  | missingImplementation (implementation : Resolved.DeclarationId)
  | duplicateImplementations
      (implementation : Resolved.DeclarationId) (count : Nat)
  | implementationParametersPresent
      (implementation : Resolved.DeclarationId)
      (parameters : List TypeParameterId)
  | implementationHeadMismatch
      (implementation : Resolved.DeclarationId)
      (evidence catalog : ProgramPredicate)
  | implementationPredicatesPresent
      (implementation : Resolved.DeclarationId)
      (predicates : List ProgramPredicate)
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

/-- Select and check the sole executable method justified by one closed piece
of trait evidence.  Trait declaration predicates become closed static method
assumptions; runtime dictionaries, generic implementations, recursive evidence
premises, and implementation/method predicates remain explicit later profiles. -/
def checkMonomorphicPremiseFreeMethodWithArity
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedTraitArity : Nat) (expectedName : String) :
    Except Error CheckedMethod := do
  let .byImpl goal implementationId premises := evidence
  unless premises.isEmpty do
    throw (.evidencePremisesPresent implementationId premises.length)
  let goalArity := goal.arguments.length + 1
  unless goalArity = expectedTraitArity do
    throw (.evidenceGoalArityMismatch goal.trait expectedTraitArity goalArity)
  let implementation ← exactImplementation program implementationId
  unless implementation.parameters.isEmpty do
    throw (.implementationParametersPresent implementation.id
      implementation.parameters)
  match firstNonClosedGoalType goal with
  | some reason => throw (.evidenceGoalNotClosed goal reason)
  | none => pure ()
  unless implementation.head = goal do
    throw (.implementationHeadMismatch implementation.id goal
      implementation.head)
  unless implementation.wherePredicates.isEmpty do
    throw (.implementationPredicatesPresent implementation.id
      implementation.wherePredicates)
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
  let synthetic := {
    baseSynthetic with
    scheme := {
      baseSynthetic.scheme with
      predicates := traitPredicates ++ baseSynthetic.scheme.predicates
    }
  }
  let checked ← SourceInference.checkFunctionBody program.environment
    program.signatures synthetic |>.mapError Error.sourceInference
  pure {
    id := implementationMethod.id
    traitMethod
    synthetic
    checked
  }

/-- Compatibility entry for the original one-parameter runtime trait profile.
Consumers of multi-parameter traits must opt into the explicit-arity entry. -/
def checkMonomorphicPremiseFreeMethod
    (program : CheckedProgram) (evidence : TypedTraitResolution.Evidence)
    (expectedName : String) : Except Error CheckedMethod :=
  checkMonomorphicPremiseFreeMethodWithArity program evidence 1 expectedName

end Solcore.Frontend.ExecutableImplMethods
