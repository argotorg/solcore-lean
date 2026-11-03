import Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
import Solcore.SourceSemantics.CoreLowering.CaptureCopiesMarkedSupport
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeInversion
import Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames

/-! Typing of the copies a closure makes through the indexed marked
allocator. Each copy is a frame snapshot, a marker over the scope's slots and a
cell of the copied slot's payload type, so it has the type of the slot it
copies, and copies keep the typing of the expression they precede. Conversely,
each copy ends by allocating a cell of its slot's payload type, so the
redirection of copied slots pulls the copies' typing back to the expression. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
open Core Frontend Frontend.SourceInference CaptureCopyRenaming
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming)

/-- One branch of a marked copy, below its payload binder: the frame snapshot
before an allocation of the slot's payload type whose marker captures the
scope's slots, `ordinal` copies past their original positions. -/
private theorem markedBranch_hasType {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal : Nat} {payload : Option Expr} {context : Core.Context} {inserted : Ty}
    {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError)
      ⟨source, scope, Renaming.comp (Renaming.insertion 0)
        (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type, payload⟩ =
      .ok code)
    (frameRegistered : layout.Registered layouts.definitions)
    (payloadWF : type.WellFormed layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (slotType : Ty), scope[index]? = some (id, slotType) →
      context[base index + ordinal]? = some (.cell (OptionalCell.cellType slotType)))
    (frame : context[base (scope.length + 1 + globals) + ordinal]? = some (.cell layout.type))
    (initializer : ∀ expression, payload = some expression →
      HasType (inserted :: context) expression type layouts.definitions) :
    HasType (inserted :: context) code (OptionalCell.referenceType type) layouts.definitions := by
  obtain ⟨allocation, annotation, same, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError accepted
  rw [annotation.exact, same]
  apply SourceCoreCallableIndexedAllocationFrames.snapshotBefore_hasType frameRegistered
  · apply HasType.var
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        ⟨source, scope, Renaming.comp (Renaming.insertion 0)
          (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type, payload⟩ =
        source.inputs.any (fun input => decide (input.id = binder.id)) := rfl
    show (inserted :: context)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal
        (scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
          ⟨source, scope, Renaming.comp (Renaming.insertion 0)
            (SourceCoreSourceCells.copyReferences source scope binder base ordinal), binder, type,
            payload⟩ then 0 else 1) + globals))]? = some (.cell layout.type)
    rw [named, CaptureCopies.copyReferences_frame]
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ]
    exact frame
  · apply allocation.hasType payloadWF _ initializer
    apply SourceCoreSourceCells.captures_hasType
    intro position binding found
    have below : position < scope.length := (List.getElem?_eq_some_iff.mp found).1
    show (inserted :: context)[Renaming.insertion 0
      (SourceCoreSourceCells.copyReferences source scope binder base ordinal position)]? =
        some (OptionalCell.referenceType binding.2)
    simp only [Renaming.insertion, Nat.zero_le, ↓reduceIte, List.getElem?_cons_succ,
      SourceCoreSourceCells.copyReferences, below]
    exact slots position binding.1 binding.2 found

/-- One marked copy of a slot is a cell of the slot's payload type: both
branches of the payload test allocate one. -/
private theorem markedCopy_hasType {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    {base : Nat → Nat} {ordinal : Nat} {context : Core.Context} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope (SourceCoreSourceCells.copyReferences source scope binder base ordinal) binder type
      reference = .ok copy)
    (frameRegistered : layout.Registered layouts.definitions)
    (payloadWF : type.WellFormed layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (slotType : Ty), scope[index]? = some (id, slotType) →
      context[base index + ordinal]? = some (.cell (OptionalCell.cellType slotType)))
    (frame : context[base (scope.length + 1 + globals) + ordinal]? = some (.cell layout.type))
    (referenceTyped : HasType context reference (.cell (OptionalCell.cellType type)) layouts.definitions) :
    HasType context copy (.cell (OptionalCell.cellType type)) layouts.definitions := by
  obtain ⟨absent, present, absentAccepted, presentAccepted, rfl⟩ := CaptureCopies.copyCell_some accepted
  exact .caseE (.loadCell referenceTyped)
    (markedBranch_hasType absentAccepted frameRegistered payloadWF slots frame
      (fun _ found => by cases found))
    (markedBranch_hasType presentAccepted frameRegistered payloadWF slots frame
      (fun _ found => by cases found; exact .var rfl))

/-- One more copy, of a slot of type `slotType`, keeps the copy renaming
type-respecting. -/
private theorem respects_markedCopy {done : List Nat} {position : Nat} {context copies : Core.Context}
    {slotType : Ty} (respects : Renaming.Respects (copyRenaming done) context (copies ++ context))
    (slot : context[position]? = some slotType) :
    Renaming.Respects (copyRenaming (done ++ [position])) context ((slotType :: copies) ++ context) := by
  intro index type found
  by_cases member : index ∈ done
  · rw [copyRenaming_snoc_of_mem member]
    simpa using respects found
  · by_cases same : index = position
    · subst index
      rw [copyRenaming_snoc_self member]
      rw [slot] at found
      simpa using found
    · rw [copyRenaming_snoc_of_ne same]
      simpa using respects found

/-- The remaining marked copies of a chain type its body, renamed to the
copies, in the context extended by every copy. -/
private theorem copyChainIndexed_hasType {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty}
    (frameRegistered : layout.Registered layouts.definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (frame : context[base (scope.length + 1 + globals)]? = some (.cell layout.type))
    (bodyTyped : HasType context body type layouts.definitions) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (done : List Nat) (copies : Core.Context)
      (emitted : Expr),
      done.length = ordinal → copies.length = ordinal →
      Renaming.Respects (copyRenaming done) context (copies ++ context) →
      (∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty), rest[offset]? = some (id, payload) →
        context[base (index + offset)]? = some (.cell (OptionalCell.cellType payload))) →
      (∀ binding ∈ rest, binding.2.WellFormed layouts.definitions) →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope base rest index ordinal
        (body.rename (copyRenaming (done ++ chainPositions source base rest index))) = .ok emitted →
      HasType (copies ++ context) emitted type layouts.definitions
  | [], _, _, done, copies, emitted, _, _, respects, _, _, accepted => by
      rw [CaptureCopies.copyChain_nil _ _ _ _ _ _ accepted]
      simpa [chainPositions] using bodyTyped.rename respects
  | (id, payload) :: rest, index, ordinal, done, copies, emitted, doneLength, copiesLength, respects,
      restSlots, wellFormed, accepted => by
      have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
        simpa using restSlots 0 id payload rfl
      have later : ∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty),
          rest[offset]? = some (id, payload) →
          context[base (index + 1 + offset)]? = some (.cell (OptionalCell.cellType payload)) := by
        intro offset id payload found
        have shifted := restSlots (offset + 1) id payload (by simpa using found)
        rwa [show index + (offset + 1) = index + 1 + offset by omega] at shifted
      have laterWellFormed : ∀ binding ∈ rest, binding.2.WellFormed layouts.definitions :=
        fun binding member => wellFormed binding (List.mem_cons_of_mem _ member)
      cases copied : copiedBinder? source id with
      | none =>
          have positions : chainPositions source base ((id, payload) :: rest) index =
              chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied]
          rw [CaptureCopies.copyChain_shared _ _ _ _ _ _ _ copied, positions] at accepted
          exact copyChainIndexed_hasType frameRegistered slots frame bodyTyped rest (index + 1) ordinal done
            copies emitted doneLength copiesLength respects later laterWellFormed accepted
      | some binder =>
          have positions : done ++ chainPositions source base ((id, payload) :: rest) index =
              (done ++ [base index]) ++ chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied, List.append_assoc, List.singleton_append]
          rw [positions] at accepted
          obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ :=
            CaptureCopies.copyChain_copied copied accepted
          have copyTyped : HasType (copies ++ context) copy (.cell (OptionalCell.cellType payload))
              layouts.definitions := by
            apply markedCopy_hasType copyAccepted frameRegistered (wellFormed (id, payload) (by simp))
            · intro position slotId slotType found
              rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact slots position slotId slotType found
            · rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact frame
            · apply HasType.var
              rw [CaptureCopies.getElem?_append_shift copiesLength]
              exact slot
          have tail := copyChainIndexed_hasType frameRegistered slots frame bodyTyped rest (index + 1)
            (ordinal + 1) (done ++ [base index]) (.cell (OptionalCell.cellType payload) :: copies)
            continuation (by simp [doneLength]) (by simp [copiesLength]) (respects_markedCopy respects slot)
            later laterWellFormed continuationAccepted
          exact .letE copyTyped tail

/-- Marked copies keep an expression's type when every scope slot holds a cell
of its well-formed payload type and the frame slot holds the frame cell. -/
theorem copyScopeIndexed_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body emitted : Expr} {type : Ty}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError))) source scope base body = .ok emitted)
    (sameDefinitions : layouts.definitions = definitions) (frameRegistered : layout.Registered definitions)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (payloads : ∀ binding ∈ scope, binding.2.WellFormed definitions)
    (frame : context[base (scope.length + 1 + globals)]? = some (.cell layout.type))
    (typed : HasType context body type definitions) :
    HasType context emitted type definitions := by
  subst sameDefinitions
  simp only [SourceCoreSourceCells.copyScope, scopeCopyRenaming_eq] at accepted
  exact copyChainIndexed_hasType frameRegistered slots frame typed scope 0 0 [] [] emitted rfl rfl
    (fun _ _ found => by simpa [copyRenaming_nil] using found)
    (fun offset id payload found => by simpa using slots offset id payload found)
    payloads (by simpa only [List.nil_append] using accepted)

/-- The absent branch of a marked copy ends by allocating a cell of the
request's optional payload type, so that is its only type. -/
private theorem markedAbsent_type {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
      (layouts.allocatorAt owner active onError) request)
    (same : annotation.original = allocation.expression) (absent : request.payload = none)
    {definitions : DataEnvironment} {context : Core.Context} {result : Ty}
    (typed : HasType context annotation.expression result definitions) :
    result = OptionalCell.referenceType request.payloadType := by
  rw [annotation.exact] at typed
  cases typed with
  | letE _ original =>
    have allocated := TypedLexicalWhile.Native.remove_front original
    rw [same, allocation.expressionExact] at allocated
    unfold SourceCoreAllocationLayouts.allocation at allocated
    simp only [absent] at allocated
    unfold SourceCoreHeapMarkers.allocate at allocated
    cases allocated with
    | letE _ cell =>
      unfold OptionalCell.allocate at cell
      cases cell with
      | newCell _ => rfl

/-- A marked copy of a slot has only the type of a cell of the slot's payload
type. -/
private theorem markedCopy_type {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {references : Renaming}
    {binder : TypedBinder} {type : Ty} {reference copy : Expr}
    (accepted : SourceCoreSourceCells.copyCell
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)))
      source scope references binder type reference = .ok copy)
    {definitions : DataEnvironment} {context : Core.Context} {copyType : Ty}
    (typed : HasType context copy copyType definitions) :
    copyType = .cell (OptionalCell.cellType type) := by
  obtain ⟨absent, present, absentAccepted, _, rfl⟩ := CaptureCopies.copyCell_some accepted
  obtain ⟨allocation, annotation, same, rfl⟩ :=
    CallableIndexedAllocationCompletion.accepted_receipts onError absentAccepted
  cases typed with
  | caseE _ absentTyped _ => exact markedAbsent_type allocation annotation same rfl absentTyped

/-- One more copy, of a slot holding the copy's type, keeps the copy renaming
pulling typings back to the original context. -/
private theorem pullsBack_markedCopy {done : List Nat} {position : Nat} {context copies : Core.Context}
    {slotType : Ty}
    (back : TypedLexicalWhile.Native.PullsBack (copyRenaming done) context (copies ++ context))
    (slot : context[position]? = some slotType) :
    TypedLexicalWhile.Native.PullsBack (copyRenaming (done ++ [position])) context
      ((slotType :: copies) ++ context) := by
  intro index type found
  by_cases member : index ∈ done
  · rw [copyRenaming_snoc_of_mem member] at found
    exact back index type (by simpa using found)
  · by_cases same : index = position
    · subst index
      rw [copyRenaming_snoc_self member] at found
      rw [slot]
      simpa using found
    · rw [copyRenaming_snoc_of_ne same] at found
      exact back index type (by simpa using found)

/-- Typed marked copies of a chain type its body, renamed to the copies, in
the context extended by the copies' types; the copy renaming pulls that typing
back to the original context. -/
private theorem copyChainIndexed_body_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty} :
    ∀ (rest : SourceCoreLocalCell.Scope) (index ordinal : Nat) (done : List Nat) (copies : Core.Context)
      (emitted : Expr),
      TypedLexicalWhile.Native.PullsBack (copyRenaming done) context (copies ++ context) →
      (∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty), rest[offset]? = some (id, payload) →
        context[base (index + offset)]? = some (.cell (OptionalCell.cellType payload))) →
      SourceCoreSourceCells.copyChain
        (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)))
        source scope base rest index ordinal
        (body.rename (copyRenaming (done ++ chainPositions source base rest index))) = .ok emitted →
      HasType (copies ++ context) emitted type definitions →
      HasType context body type definitions
  | [], _, _, done, copies, emitted, back, _, accepted, typed => by
      rw [CaptureCopies.copyChain_nil _ _ _ _ _ _ accepted] at typed
      simp only [chainPositions, List.append_nil] at typed
      exact TypedLexicalWhile.Native.typing body back typed
  | (id, payload) :: rest, index, ordinal, done, copies, emitted, back, restSlots, accepted, typed => by
      have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
        simpa using restSlots 0 id payload rfl
      have later : ∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty),
          rest[offset]? = some (id, payload) →
          context[base (index + 1 + offset)]? = some (.cell (OptionalCell.cellType payload)) := by
        intro offset id payload found
        have shifted := restSlots (offset + 1) id payload (by simpa using found)
        rwa [show index + (offset + 1) = index + 1 + offset by omega] at shifted
      cases copied : copiedBinder? source id with
      | none =>
          have positions : chainPositions source base ((id, payload) :: rest) index =
              chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied]
          rw [CaptureCopies.copyChain_shared _ _ _ _ _ _ _ copied, positions] at accepted
          exact copyChainIndexed_body_hasType rest (index + 1) ordinal done copies emitted back later
            accepted typed
      | some binder =>
          have positions : done ++ chainPositions source base ((id, payload) :: rest) index =
              (done ++ [base index]) ++ chainPositions source base rest (index + 1) := by
            simp only [chainPositions, copied, List.append_assoc, List.singleton_append]
          rw [positions] at accepted
          obtain ⟨copy, continuation, copyAccepted, continuationAccepted, rfl⟩ :=
            CaptureCopies.copyChain_copied copied accepted
          cases typed with
          | letE copyTyped continuationTyped =>
            obtain rfl := markedCopy_type copyAccepted copyTyped
            exact copyChainIndexed_body_hasType rest (index + 1) (ordinal + 1) (done ++ [base index])
              (.cell (OptionalCell.cellType payload) :: copies) continuation (pullsBack_markedCopy back slot)
              later continuationAccepted continuationTyped

/-- Marked copies around an expression type it in the original context, when
every scope slot holds a cell of its payload type. -/
theorem copyScopeIndexed_body_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body emitted : Expr} {type : Ty}
    (accepted : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError))) source scope base body = .ok emitted)
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (typed : HasType context emitted type definitions) :
    HasType context body type definitions := by
  simp only [SourceCoreSourceCells.copyScope, scopeCopyRenaming_eq] at accepted
  exact copyChainIndexed_body_hasType scope 0 0 [] [] emitted
    (by intro index type found; simpa [copyRenaming_nil] using found)
    (fun offset id payload found => by simpa using slots offset id payload found)
    (by simpa only [List.nil_append] using accepted) typed

end Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
