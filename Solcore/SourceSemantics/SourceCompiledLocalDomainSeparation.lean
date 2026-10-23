import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrderedDomain
import Solcore.SourceSemantics.SourceCompiledLocalLexicalOrder
import Solcore.SourceSemantics.SourceCompiledSpecializedQuantifierSeparation

/-! Actual discovery order and the same cached body's quantified owners
exclude earlier owners from a contextual instance's substitution domain. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceSpecializationWorklist SourceCompiledGeneralizedSoundness
open CoreLowering.GeneralizedLocalLexicalOrigin

private theorem initialized_binding_of_lexical_origin
    {source : TypedSource} {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin source localInstance) :
    ({ binder := localInstance.binding.binder,
       initializer := .expression localInstance.binding.initializer } : InitializedLetBinding) ∈
      initializedLetBindings source := by
  obtain ⟨statement, present, form⟩ :=
    localLambdaBindings_statement_origin origin.binding_member
  apply List.mem_flatMap.mpr
  refine ⟨.statement statement, present, ?_⟩
  change _ ∈ statementInitializedLetBindings statement.form
  rw [form]
  exact List.mem_singleton_self _

namespace BodySelection
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}

/-- The order used by the domain induction is supplied by the actual inferred
initializer and the exact reads in its direct lexical body. -/
theorem contextual_read_order
    (selected : BodySelection compiled named.specialized fuel)
    (checked : checkProgram raw fuel = .ok compiled.program) :
    ContextualReadOrder named.specialized.function.typedBody := by
  intro parent origin nodes accepted expression member name target form
  exact selected.local_lambda_read_binder_lt checked origin accepted member form

/-- Every key of the actual cumulative substitution belongs to an owner at
or after this instance. A distinct, earlier initialized owner cannot contribute
that same quantified variable. -/
theorem local_domain_excludes_earlier
    (selected : BodySelection compiled named.specialized fuel)
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {localInstance : LocalLambdaInstance}
    (origin : LocalLambdaInstance.LexicalReadOrigin
      named.specialized.function.typedBody localInstance)
    {earlier : InitializedLetBinding}
    (earlierMember : earlier ∈ initializedLetBindings named.specialized.function.typedBody)
    (before : earlier.binder.id.binderIndex <
      localInstance.binding.binder.id.binderIndex)
    {q : TypeVarId} (quantified : q ∈ earlier.binder.scheme.quantified) :
    q ∉ localInstance.substitution.domain := by
  intro key
  obtain ⟨owner, ownerOrigin, ownerQuantified, afterInstance⟩ :=
    domain_owner_at_or_after origin (selected.contextual_read_order checked) key
  let ownerBinding : InitializedLetBinding :=
    { binder := owner.binding.binder, initializer := .expression owner.binding.initializer }
  have ownerMember : ownerBinding ∈
      initializedLetBindings named.specialized.function.typedBody :=
    initialized_binding_of_lexical_origin ownerOrigin
  have different : ownerBinding.binder ≠ earlier.binder := by
    intro same
    have sameIndex := congrArg (fun binder : TypedBinder => binder.id.binderIndex) same
    change owner.binding.binder.id.binderIndex = earlier.binder.id.binderIndex at sameIndex
    have ordered := Nat.lt_of_lt_of_le before afterInstance
    omega
  exact selected.specialized_initialized_quantifiers_disjoint artifact checked position
    earlierMember ownerBinding ownerMember different q quantified ownerQuantified

end BodySelection
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
