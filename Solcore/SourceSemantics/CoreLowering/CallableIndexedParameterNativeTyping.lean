import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates

/-! Static typing of the real marked parameter fold. The packed argument and
lexical references retain their actual insertion indices. This result concerns
generated expressions, not equality of closure values under weakening. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
open Core Frontend SourceInference CallableIndexedParameterCertificates

def packed : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: next :: rest => .product type (packed (next :: rest))

theorem projection_typed {definitions : DataEnvironment} {context : Core.Context}
    {types : List Ty} {index : Nat} {type : Ty} {bundle : Expr}
    (found : types[index]? = some type)
    (typed : HasType context bundle (packed types) definitions) :
    HasType context (SourceCoreFunctions.argumentProjection index types.length bundle) type definitions := by
  induction types generalizing index bundle with
  | nil => cases found
  | cons head rest ih =>
    cases rest with
    | nil =>
      cases index with
      | zero => cases found; exact typed
      | succ index => simp at found
    | cons next tail =>
      cases index with
      | zero => cases found; exact .first typed
      | succ index =>
        simpa [SourceCoreFunctions.argumentProjection] using ih (by simpa using found) (HasType.second typed)

def finalContext (bindings : List Binding) (context : Core.Context) : Core.Context :=
  (bindings.map (fun binding => OptionalCell.referenceType binding.2)).reverse ++ context

theorem tree_native {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {all : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {index : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active frame globals onError source all.length output body scope index bindings code)
    (registered : frame.Registered layouts.definitions)
    (outputWF : output.WellFormed layouts.definitions)
    (payloadWF : ∀ binding ∈ bindings, binding.2.WellFormed layouts.definitions)
    (ordinary : ∀ binding ∈ bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (selected : ∀ position binding, bindings[position]? = some binding → all[index + position]? = some binding.2)
    {context : Core.Context}
    (bundle : context[index]? = some (packed all))
    (references : ∀ position binding, scope[position]? = some binding →
      context[Renaming.insertion index position]? = some (OptionalCell.referenceType binding.2))
    (current : context[Renaming.insertion index (scope.length + 1 + globals)]? = some (.cell frame.type))
    (continuation : HasType (finalContext bindings context) body (LanguageResult.resultType output) layouts.definitions) :
    HasType context code (LanguageResult.resultType output) layouts.definitions := by
  induction tree generalizing context with
  | nil => exact continuation
  | @cons scope index binder payload bindings code allocation annotation same tail ih =>
    have member : (binder, payload) ∈ (binder, payload) :: bindings := by simp
    have next := ih (fun binding h => payloadWF binding (List.mem_cons_of_mem _ h))
      (fun binding h => ordinary binding (List.mem_cons_of_mem _ h))
      (fun position binding h => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected (position + 1) binding h)
      (context := OptionalCell.referenceType payload :: context)
      (by simpa using bundle) ?_ ?_ ?_
    · have captured : HasType (payload :: context)
          (SourceCoreSourceCells.captures (request source scope index (binder, payload)).references scope)
          (SourceCoreSourceCells.captureType scope) layouts.definitions := by
        apply SourceCoreSourceCells.captures_hasType
        intro position binding found
        simpa [request, Renaming.comp, Renaming.insertion] using references position binding found
      have allocated := allocation.hasType (payloadWF _ member) captured
        (by intro expression found; cases found; exact .var rfl)
      have annotated : HasType (payload :: context) annotation.expression
          (OptionalCell.referenceType payload) layouts.definitions := by
        rw [annotation.exact, same]
        apply SourceCoreCallableIndexedAllocationFrames.snapshotBefore_hasType registered
        · apply HasType.var
          have ordinaryHead := ordinary _ member
          change (payload :: context)[Renaming.comp (Renaming.insertion 0) (Renaming.insertion index)
            (scope.length + (if source.inputs.any (fun input => decide (input.id = binder.id)) then 0 else 1) + globals)]? = _
          rw [ordinaryHead]
          exact current
        · exact allocated
      apply LanguageResult.bind_hasType outputWF
      · exact LanguageResult.success_hasType (projection_typed (by simpa using selected 0 _ rfl) (.var bundle))
      · apply HasType.letE annotated
        simpa [Core.Context.insertAt] using next.weakenAt (inserted := payload) 1
    · intro position binding found
      cases position with
      | zero => cases found; simp [Renaming.insertion]
      | succ position =>
        rw [← Renaming.lift_insertion]
        exact references position binding found
    · have arithmetic : ((binder.id, payload) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp; omega
      rw [arithmetic, ← Renaming.lift_insertion]
      exact current
    · simpa [finalContext, List.reverse_cons, List.append_assoc] using continuation

private theorem insertAt_append (front suffix : Core.Context) (type : Ty) :
    (front ++ suffix).insertAt front.length type = front ++ type :: suffix := by
  induction front with
  | nil => cases suffix <;> rfl
  | cons head rest ih => simp [Core.Context.insertAt, ih]

/-- The exact accepted allocation fold is typed from its body in the actual
source-reference context. No type of the completed prefix is assumed. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection (body.weakenAt bindings.length) = .ok code)
    (registered : frame.Registered layouts.definitions)
    (outputWF : output.WellFormed layouts.definitions)
    (payloadWF : ∀ binding ∈ bindings, binding.2.WellFormed layouts.definitions)
    (ordinary : ∀ binding ∈ bindings,
      source.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + globals]? = some (.cell frame.type))
    (bodyTyped : HasType (SourceCoreLocalCell.coreContext
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      body (LanguageResult.resultType output) layouts.definitions) :
    HasType (packed (bindings.map Prod.snd) :: SourceCoreLocalCell.coreContext scope ++ administrative)
      code (LanguageResult.resultType output) layouts.definitions := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have selected : ∀ position binding, bindings[position]? = some binding →
      (bindings.map Prod.snd)[0 + position]? = some binding.2 := by
    intro position binding found
    simp [found]
  apply tree_native (all := bindings.map Prod.snd) (by simpa using tree) registered outputWF payloadWF ordinary selected rfl
  · intro position binding found
    change (SourceCoreLocalCell.coreContext scope ++ administrative)[position]? = _
    rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
    simp [SourceCoreLocalCell.coreContext, found, OptionalCell.referenceType]
  · exact current
  · have typed := bodyTyped.weakenAt (inserted := packed (bindings.map Prod.snd)) bindings.length
    have contextEq : (SourceCoreLocalCell.coreContext
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative).insertAt
        bindings.length (packed (bindings.map Prod.snd)) =
        finalContext bindings (packed (bindings.map Prod.snd) :: SourceCoreLocalCell.coreContext scope ++ administrative) := by
      simp only [SourceCoreLocalCell.coreContext, List.map_append, List.map_map, List.map_reverse, List.append_assoc, finalContext]
      have length : (List.map (fun binding : Binding => OptionalCell.referenceType binding.2) bindings).reverse.length = bindings.length := by simp
      change Core.Context.insertAt ((bindings.map (fun binding => OptionalCell.referenceType binding.2)).reverse ++
        (SourceCoreLocalCell.coreContext scope ++ administrative)) bindings.length _ = _
      rw [← length, insertAt_append]
      rfl
    rw [contextEq] at typed
    exact typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
