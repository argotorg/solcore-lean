import Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCollectors

/-! Finite initializer profiles inspect the actual catalog before execution.
Scope and compilation budgets do not change these original metadata checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open CallableIndexedNamedGeneration (Prepared Compilation context source)
open GeneralizedLocalInitializerCompilation (namedInputs)
open GeneralizedLocalInitializerPackets (Profile BindingProfile)

private theorem binding_member {locals : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} (located : locals.binding caller binder = .ok binding) : binding ∈ locals.bindings := by
  unfold Catalog.binding at located
  generalize filtered : locals.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | nil =>
      cases located
      exact (List.mem_filter.mp (show binding ∈ locals.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by rw [filtered]; simp)).1
    | cons next tail => cases located

variable {checked : SourceCoreCompatibleCatalog.Checked}

structure Candidate (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (binding : Binding) (candidate : Instance) where
  original : GeneralizedLocalInitializerPackets.BindingObservations
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    named.signature.key binding.initializer binding candidate
  body : GeneralizedLocalBodyProfile.Profile prepared.base.locals named.signature.key
    candidate.source binding.initializer

def candidates? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (binding : Binding) : (candidates : List Instance) →
      Option (PLift (∀ candidate ∈ candidates, Nonempty (Candidate prepared named binding candidate)))
  | [] => some ⟨by intro candidate member; cases member⟩
  | candidate :: rest => do
    let head ← GeneralizedLocalInitializerPackets.bindingObservations?
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      named.signature.key binding.initializer binding candidate
    let body ← GeneralizedLocalBodyProfile.profile? prepared.base.locals named.signature.key
      candidate.source binding.initializer
    let ⟨tail⟩ ← candidates? prepared named binding rest
    pure ⟨by
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact ⟨⟨head, body⟩⟩
      · exact tail selected member⟩

def Rows (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (bindings : List Binding) : Prop :=
  ∀ binding ∈ bindings, binding.caller = named.signature.key →
    ∀ candidate ∈ binding.atContext [], Nonempty (Candidate prepared named binding candidate)

def rows? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) :
    (bindings : List Binding) → Option (PLift (Rows prepared named bindings))
  | [] => some ⟨by intro binding member; cases member⟩
  | binding :: rest => do
    let ⟨tail⟩ ← rows? prepared named rest
    if caller : binding.caller = named.signature.key then
      let ⟨head⟩ ← candidates? prepared named binding (binding.atContext [])
      pure ⟨by
        intro selected member owner
        rcases List.mem_cons.mp member with same | member
        · subst selected; exact head
        · exact tail selected member owner⟩
    else
      pure ⟨by
        intro selected member owner
        rcases List.mem_cons.mp member with same | member
        · subst selected; exact False.elim (caller owner)
        · exact tail selected member owner⟩

/-- The actual reached site selects its original finite catalog entry. No
identity is inferred from the row's native type. -/
theorem Rows.at_site {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (reasonAt : ExpressionId → Word)
    (profiles : Rows prepared named prepared.base.locals.bindings)
    {scope binder initializer}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer) (childFuel : Nat) :
    ∀ candidate ∈ site.binding.atContext [], Nonempty (BindingProfile
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt)
      site.binding candidate) := by
  intro candidate member
  obtain ⟨profile⟩ := profiles site.binding (binding_member site.located) site.bindingCaller candidate member
  have original := profile.original
  rw [site.bindingInitializer] at original
  exact ⟨original⟩

/-- Body eligibility follows the same actual catalog row and original source. -/
theorem Rows.bodies_at_site {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code) (reasonAt : ExpressionId → Word)
    (profiles : Rows prepared named prepared.base.locals.bindings)
    {scope binder initializer}
    (site : CellAwareSourceBodyAdmission.Site prepared.base.locals named.signature.key []
      (source named) binder initializer) (childFuel : Nat) :
    ∀ candidate ∈ site.binding.atContext [], Nonempty (GeneralizedLocalBodyProfile.Profile
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).locals
      (namedInputs compiled childFuel (childFuel + 1) (context prepared named) scope initializer reasonAt).current.owner
      candidate.source initializer) := by
  intro candidate member
  obtain ⟨profile⟩ := profiles site.binding (binding_member site.located) site.bindingCaller candidate member
  have body := profile.body
  rw [site.bindingInitializer] at body
  exact ⟨body⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
