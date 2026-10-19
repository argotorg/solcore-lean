import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadFormation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceReadInversion

/-! The exact original declaration identifies a polymorphic lexical scheme.
The actual environment and heap then force the descriptor branch; its stored
compiler binding and shared frame come from the physical scope authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts
open Core Frontend SourceInference TypeSystem GeneralHeap ReadOnly
open GeneralizedLocalLocatedRows

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {context : SourceSemantics.Context} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Core.Environment} {environment : Dynamic.Environment}

theorem binder
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate) :
    certificate.read.binder = recipe.observations.binding.binder.id := by
  have original := Option.some.inj
    (certificate.observations.originalFound.symm.trans recipe.observations.originalFound)
  have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  obtain ⟨name, form⟩ := certificate.read.nodeForm
  rw [normalized, certificate.observations.form, original, recipe.observations.originalForm] at form
  exact ReferenceResolution.local.inj (ExpressionForm.reference.inj form).2.symm

structure Reached
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment) where
  function : Dynamic.GeneralizedClosure
  location : Dynamic.Location
  lexical : Substitution
  located : Located (GeneralizedLocalInstanceValues.model compiled.indexed) function certificate.read.binding lexical
    location mapping world heap store
  lookup : Dynamic.Environment.LooksUp environment certificate.read.binder location
  caller : named.signature.key = certificate.read.binding.caller
  binder : certificate.read.binder = certificate.read.binding.binder.id
  contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical []
  frames : located.Frames physical.location
  fields : Dynamic.RuntimeContextFields function.definitionContext context
  requirements : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements
  scheme : function.binder.scheme = certificate.read.binding.binder.scheme
  matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme certificate.observations.original.rawType =
    some certificate.read.child

theorem resolve
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named source scope id reasonAt lowered)
    (recipe : GeneralizedLocalNamedRecipeCompilation.Receipt certificate)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world heap store environment)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment) : Nonempty (Reached certificate physical) := by
  have binderEq := binder certificate recipe
  have declared := physical.sourceDeclarations _ _ _ _
    (by simpa only [binderEq] using certificate.read.slot) recipe.observations.declaration
  obtain ⟨location, cell, lookup, read, _, storage⟩ := locals.lookup declared
  cases storage with
  | ordinary monomorphic _ => exact False.elim (recipe.observations.polymorphic monomorphic)
  | generalized descriptor sourceBinder sourceScheme =>
    obtain ⟨binding, lexical, located, caller, actualBinder, extension, frames, fields, requirements⟩ :=
      physical.generalized lookup read descriptor
    have bindingEq : certificate.read.binding = binding := by
      have registered : compiled.indexed.base.locals.binding named.signature.key certificate.read.binder = .ok binding := by
        simpa only [GeneralizedLocalInstanceValues.model, caller, actualBinder, binderEq] using located.attachment.registered
      exact Except.ok.inj (certificate.read.bindingFound.symm.trans registered)
    subst binding
    have matched := certificate.read.matched
    simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at matched
    have rawType := certificate.read.rawType
    simp only [EmptySourceSubstitution.type] at rawType
    have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
    rw [rawType, normalized, certificate.observations.rawType] at matched
    refine ⟨⟨_, location, lexical, located, ?_, caller.symm, ?_, extension, frames, fields, requirements,
      sourceScheme.trans (congrArg (fun binding => binding.binder.scheme) recipe.binding), ?_⟩⟩
    · simpa only [binderEq] using lookup
    · exact binderEq.trans (congrArg (fun binding => binding.binder.id) recipe.binding)
    · simpa only [sourceScheme, recipe.binding] using matched

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts
