import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation

/-! Named read admission checks the actual metadata factories before execution.
These finite observations contain no native body or execution callback and are
independent of the eventual native scope and emitted read expression. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
open Core Frontend SourceInference TypeSystem
open CallableIndexedNamedGeneration (Prepared state)
open SourceCoreCallableAncestryReadRecipes

structure Observations {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan
  found : prepared.ancestry.views.viewAt? named.signature.key id [] = some entry
  generalized : entry.view.wrapsPrincipal = true
  viewCandidate : SourceCoreLocalPolymorphism.Instance
  selected : entry.view.selectedInstance = some viewCandidate
  target : Word
  targetSelected : prepared.ancestry.graph.inputs.callable.table.idAt?
    (.lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution) = some target
  read : Read prepared.ancestry.graph.inputs (state named) entry.id target
  readAccepted : prepareRead prepared.ancestry.graph.inputs (state named) entry.id target = .ok read
  applied : Applied read (state named)
  appliedAccepted : applyRead read (state named) = .ok applied
  binding : SourceCoreLocalPolymorphism.Binding
  namedCaller : binding.caller = named.signature.key
  namedSource : binding.source = CallableIndexedNamedGeneration.source named
  declaration : (SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named)).filter
    (fun binder => decide (binder.id = binding.binder.id)) = [binding.binder]
  polymorphic : binding.binder.scheme.quantified ≠ []
  bindingFound : prepared.base.locals.binding named.signature.key read.entry.view.binding.binder.id = .ok binding
  sameEntry : read.entry = entry
  initializer : read.entry.view.principal.initializer = binding.initializer
  scheme : read.binder.scheme = binding.binder.scheme
  original : ExpressionNode
  originalFound : source.lookupExpression? id = some original
  name : String
  originalForm : original.form = .reference name (.local binding.binder.id)
  rawType : read.node.rawType = original.rawType
  candidate : SourceCoreLocalPolymorphism.Instance
  rows : (binding.atContext []).filter (fun item => decide (item.origin.substitution = read.substitution)) = [candidate]
  candidateInitializer : candidate.origin.initializer = binding.initializer
  origin : SourceCoreStageCodebook.Origin.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution =
    .lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution

private theorem find_unique_key {α β : Type} [DecidableEq β] (items : List α) (key : α → β)
    (unique : (items.map key).Nodup) {item : α} (member : item ∈ items) :
    items.find? (fun candidate => decide (key candidate = key item)) = some item := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst item; simp
    · have different : key head ≠ key item := by
        intro same
        exact unique.1 (List.mem_map.mpr ⟨item, member, same.symm⟩)
      simpa [List.find?_cons, different] using ih unique.2 member

private theorem same_entry {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : Prepared checked} {named : SourceCoreGeneralFunctions.Function} {id : ExpressionId}
    {entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan} {target : Word}
    (found : prepared.ancestry.views.viewAt? named.signature.key id [] = some entry)
    (read : Read prepared.ancestry.graph.inputs (state named) entry.id target) : read.entry = entry := by
  have selected : prepared.ancestry.views.entryAt? entry.id = some entry :=
    find_unique_key _ _ prepared.ancestry.views.idsUnique (List.mem_of_find?_eq_some found)
  exact Option.some.inj (read.selected.symm.trans selected)

def observations? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Observations prepared named source id) :=
  match found : prepared.ancestry.views.viewAt? named.signature.key id [] with
  | none => none
  | some entry =>
    if generalized : entry.view.wrapsPrincipal = true then
      match selected : entry.view.selectedInstance with
      | none => none
      | some viewCandidate =>
        match targetSelected : prepared.ancestry.graph.inputs.callable.table.idAt?
            (.lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution) with
        | none => none
        | some target =>
          match readAccepted : prepareRead prepared.ancestry.graph.inputs (state named) entry.id target with
          | .error _ => none
          | .ok read =>
            match appliedAccepted : applyRead read (state named) with
            | .error _ => none
            | .ok applied =>
              match bindingFound : prepared.base.locals.binding named.signature.key read.entry.view.binding.binder.id with
              | .error _ => none
              | .ok binding =>
               if namedCaller : binding.caller = named.signature.key then
                if namedSource : binding.source = CallableIndexedNamedGeneration.source named then
                 if declaration : (SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named)).filter
                     (fun binder => decide (binder.id = binding.binder.id)) = [binding.binder] then
                  if polymorphic : binding.binder.scheme.quantified ≠ [] then
                   if initializer : read.entry.view.principal.initializer = binding.initializer then
                  if scheme : read.binder.scheme = binding.binder.scheme then
                    match originalFound : source.lookupExpression? id with
                    | none => none
                    | some original =>
                      match originalForm : original.form with
                      | .reference name (.local binder) =>
                        if sameBinder : binder = binding.binder.id then
                          if rawType : read.node.rawType = original.rawType then
                            match rows : (binding.atContext []).filter (fun item => decide (item.origin.substitution = read.substitution)) with
                            | [candidate] =>
                              if candidateInitializer : candidate.origin.initializer = binding.initializer then
                               if origin : SourceCoreStageCodebook.Origin.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution =
                                  .lambda viewCandidate.origin.caller viewCandidate.origin.initializer viewCandidate.origin.substitution then
                                some ⟨entry, found, generalized, viewCandidate, selected, target, targetSelected,
                                  read, readAccepted, applied, appliedAccepted, binding, namedCaller, namedSource, declaration, polymorphic, bindingFound,
                                  same_entry found read, initializer, scheme, original, originalFound, name,
                                  by simpa only [sameBinder] using originalForm, rawType, candidate, rows, candidateInitializer, origin⟩
                               else none
                              else none
                            | _ => none
                          else none
                        else none
                      | _ => none
                  else none
                 else none
                else none
                else none
                 else none
               else none
    else none

structure Receipt {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered) where
  observations : Observations prepared named source id
  binding : observations.binding = certificate.read.binding
  candidate : observations.candidate = certificate.read.candidate
  rawType : observations.read.node.rawType = certificate.read.node.rawType
  parameter : Core.Ty
  result : Core.Ty
  nativeType : certificate.raw.type = CallableContract.functionType parameter result
  emitted : lowered = {certificate.raw with expression := (SourceCoreCallableIndexedAncestry.viewLower
    prepared.ancestry.layout.frame parameter result observations.entry.id observations.target
    (scope.length + 1 + prepared.base.globals.length) certificate.raw.expression)}

private theorem binding_id {catalog : SourceCoreLocalPolymorphism.Catalog}
    {caller : SourceCoreLocalPolymorphism.Key} {id : Resolved.LocalId}
    {binding : SourceCoreLocalPolymorphism.Binding}
    (found : catalog.binding caller id = .ok binding) : binding.binder.id = id := by
  unfold SourceCoreLocalPolymorphism.Catalog.binding at found
  generalize rowsEq : catalog.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = id)) = rows at found
  cases rows with
  | nil => cases found
  | cons head tail =>
    cases tail with
    | nil =>
      cases found
      have member : binding ∈ catalog.bindings.filter (fun entry => decide (entry.caller = caller ∧ entry.binder.id = id)) := by
        rw [rowsEq]
        exact List.mem_singleton_self _
      exact (of_decide_eq_true (List.mem_filter.mp member).2).2
    | cons => cases found

/-- The accepted native read determines the same full candidate as the static
metadata factories, even when several instances have equal native types. -/
theorem of_certificate {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (observed : Observations prepared named source id)
    (certificate : GeneralizedLocalNamedReadCompilation.Certificate prepared named source scope id reasonAt lowered) :
    Nonempty (Receipt certificate) := by
  have originalEq : observed.original = certificate.observations.original :=
    Option.some.inj (observed.originalFound.symm.trans certificate.observations.originalFound)
  have nodeEq : certificate.read.node = certificate.observations.node :=
    Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  have rawType : observed.read.node.rawType = certificate.read.node.rawType := by
    rw [nodeEq, certificate.observations.rawType, ← originalEq]
    exact observed.rawType
  obtain ⟨name, form⟩ := certificate.read.nodeForm
  have sameForm := form.symm.trans (congrArg ExpressionNode.form nodeEq)
  rw [certificate.observations.form, ← originalEq, observed.originalForm] at sameForm
  have binderEq : certificate.read.binder = observed.binding.binder.id := by
    injection sameForm with _ resolution
    injection resolution
  have observedBinder := binding_id observed.bindingFound
  have bindingEq : observed.binding = certificate.read.binding := by
    have selected := observed.bindingFound
    rw [← observedBinder, ← binderEq] at selected
    exact Except.ok.inj (selected.symm.trans certificate.read.bindingFound)
  have matched := CallableAncestryProfiles.SourceComposition.witnesses_matched observed.read.factory
  have rawMatched := certificate.read.matched
  simp only [EmptySourceSubstitution.scheme, EmptySourceSubstitution.type] at rawMatched
  have originalType : certificate.read.original.rawType = certificate.read.node.rawType := by
    simpa only [EmptySourceSubstitution.type] using certificate.read.rawType
  rw [originalType, ← bindingEq, ← observed.scheme, ← rawType] at rawMatched
  have childEq : certificate.read.child = observed.read.substitution :=
    Option.some.inj (rawMatched.symm.trans matched)
  have key : certificate.read.candidate.origin.substitution = observed.read.substitution := by
    have actualKey := certificate.read.candidate_key
    have identity : certificate.read.child.compose [] = certificate.read.child := by
      simp [Substitution.compose, List.filter_eq_self]
    exact actualKey.trans (identity.trans childEq)
  have member : certificate.read.candidate ∈ (observed.binding.atContext []).filter
      (fun item => decide (item.origin.substitution = observed.read.substitution)) := by
    apply List.mem_filter.mpr
    constructor
    · rw [bindingEq]
      exact List.mem_of_getElem? certificate.read.candidate_at
    · simp only [key, decide_true]
  rw [observed.rows] at member
  have candidateEq := (List.mem_singleton.mp member).symm
  obtain ⟨viewed, _, route⟩ := CallableIndexedFormation.lowerView_receipt prepared.ancestry certificate.viewAccepted
  have entryEq : viewed.entry = observed.entry := Option.some.inj (viewed.found.symm.trans observed.found)
  rcases route with ⟨ordinary, _⟩ | ⟨_, candidate, target, parameter, result, selected, targetSelected, type, emitted⟩
  · rw [entryEq, observed.generalized] at ordinary
    cases ordinary
  · rw [entryEq, observed.selected] at selected
    have candidateViewEq := Option.some.inj selected
    rw [← candidateViewEq, observed.targetSelected] at targetSelected
    have targetEq := Option.some.inj targetSelected
    refine ⟨⟨observed, bindingEq, candidateEq, rawType, parameter, result, type, ?_⟩⟩
    simpa only [entryEq, ← targetEq] using emitted

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
