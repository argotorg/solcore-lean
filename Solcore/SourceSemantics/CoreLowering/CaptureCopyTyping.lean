import Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming

/-! Typing of the copies a closure makes of its captured cells. Each copy has
the type of the slot it copies, so the redirection of copied slots has a
type-respecting left inverse: a well-typed expression under its copies is
already well typed without them. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
open Core Frontend Frontend.SourceInference CaptureCopyRenaming
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming copyChainPlain)

/-- One more copy, of a slot of type `slotType`, keeps the copy renaming
type-respecting. -/
private theorem respects_copy {done : List Nat} {position : Nat} {context copies : Core.Context}
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

/-- The remaining copies of a chain type its body, renamed to the copies, in
the context extended by every copy. -/
private theorem copyChainPlain_hasType {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {base : Nat → Nat} {body : Expr} {type : Ty}
    (bodyTyped : HasType context body type definitions) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat) (done : List Nat) (copies : Core.Context),
      copies.length = done.length →
      Renaming.Respects (copyRenaming done) context (copies ++ context) →
      (∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty), rest[offset]? = some (id, payload) →
        context[base (index + offset)]? = some (.cell (OptionalCell.cellType payload))) →
      HasType (copies ++ context)
        (copyChainPlain source base rest index done.length
          (body.rename (copyRenaming (done ++ chainPositions source base rest index)))) type definitions
  | [], _, done, copies, _, respects, _ => by
      simpa [copyChainPlain, chainPositions] using bodyTyped.rename respects
  | (id, payload) :: rest, index, done, copies, lengths, respects, slots => by
      have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
        simpa using slots 0 id payload rfl
      have later : ∀ (offset : Nat) (id : Resolved.LocalId) (payload : Ty),
          rest[offset]? = some (id, payload) →
          context[base (index + 1 + offset)]? = some (.cell (OptionalCell.cellType payload)) := by
        intro offset id payload found
        have shifted := slots (offset + 1) id payload (by simpa using found)
        rwa [show index + (offset + 1) = index + 1 + offset by omega] at shifted
      cases copied : copiedBinder? source id with
      | none =>
          have tail := copyChainPlain_hasType (source := source) bodyTyped rest (index + 1) done copies
            lengths respects later
          simpa [copyChainPlain, chainPositions, copied] using tail
      | some binder =>
          have tail := copyChainPlain_hasType (source := source) bodyTyped rest (index + 1)
            (done ++ [base index]) (.cell (OptionalCell.cellType payload) :: copies) (by simp [lengths])
            (respects_copy respects slot) later
          simp only [copyChainPlain, chainPositions, copied]
          refine .letE (.newCell (.loadCell (.var ?_))) ?_
          · rw [List.getElem?_append_right (by omega)]
            simpa [lengths] using slot
          · simpa [List.append_assoc] using tail

/-- The left inverse after one more copy of `position`: the newest slot reads
back as `position`. -/
private def prepend (position : Nat) (mapping : Renaming) : Renaming
  | 0 => position
  | index + 1 => mapping index

/-- A chain typed in the context extended by its copies types its body there;
a left inverse of the final copy renaming that respects this context takes the
body back to the original context. Each copy reads its slot's type, and an
injective `base` keeps every later position fresh. -/
private theorem copyChainPlain_hasType_inverse {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {base : Nat → Nat} {body : Expr} {type : Ty}
    (injective : ∀ left right, base left = base right → left = right) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat) (done : List Nat) (copies : Core.Context)
      (inverse : Renaming),
      copies.length = done.length →
      Renaming.Respects inverse (copies ++ context) context →
      (∀ position, inverse (copyRenaming done position) = position) →
      (∀ offset, base (index + offset) ∉ done) →
      HasType (copies ++ context)
        (copyChainPlain source base rest index done.length
          (body.rename (copyRenaming (done ++ chainPositions source base rest index)))) type definitions →
      HasType context body type definitions
  | [], _, done, copies, inverse, _, respects, leftInverse, _, typed => by
      have renamed := (show HasType (copies ++ context) (body.rename (copyRenaming done)) type definitions by
        simpa [copyChainPlain, chainPositions] using typed).rename respects
      have identity : Renaming.comp inverse (copyRenaming done) = Renaming.id := by
        funext position
        exact leftInverse position
      rwa [Expr.rename_comp, identity, Expr.rename_id] at renamed
  | (id, payload) :: rest, index, done, copies, inverse, lengths, respects, leftInverse, fresh, typed => by
      have later : ∀ offset, base (index + 1 + offset) ∉ done := by
        intro offset
        simpa [show index + (offset + 1) = index + 1 + offset by omega] using fresh (offset + 1)
      cases copied : copiedBinder? source id with
      | none =>
          apply copyChainPlain_hasType_inverse (source := source) injective rest (index + 1) done copies
            inverse lengths respects leftInverse later
          simpa [copyChainPlain, chainPositions, copied] using typed
      | some binder =>
          simp only [copyChainPlain, chainPositions, copied] at typed
          match typed with
          | .letE (.newCell (.loadCell (.var lookup))) bodyTyped =>
              have slot : context[base index]? = some (.cell (OptionalCell.cellType payload)) := by
                rw [List.getElem?_append_right (by omega)] at lookup
                simpa [lengths] using lookup
              have selfFresh : base index ∉ done := by simpa using fresh 0
              apply copyChainPlain_hasType_inverse (source := source) injective rest (index + 1)
                (done ++ [base index]) (.cell (OptionalCell.cellType payload) :: copies)
                (prepend (base index) inverse) (by simp [lengths])
              · intro position slotType found
                cases position with
                | zero =>
                    simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at found
                    subst found
                    exact slot
                | succ position => exact respects (by simpa using found)
              · intro position
                by_cases same : position = base index
                · subst position
                  rw [copyRenaming_snoc_self selfFresh]
                  rfl
                · rw [copyRenaming_snoc_of_ne same]
                  exact leftInverse position
              · intro offset member
                rcases List.mem_append.mp member with old | new
                · exact later offset old
                · have same := injective _ _ (List.mem_singleton.mp new)
                  omega
              · simpa [List.append_assoc] using bodyTyped

/-- Plain copies around an expression type it in the original context. -/
theorem copyScopePlain_body_hasType {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty}
    (injective : ∀ left right, base left = base right → left = right)
    (typed : HasType context (SourceCoreSourceCells.copyScopePlain source scope base body) type definitions) :
    HasType context body type definitions := by
  simp only [SourceCoreSourceCells.copyScopePlain, scopeCopyRenaming_eq] at typed
  exact copyChainPlain_hasType_inverse injective scope 0 [] [] Renaming.id rfl (fun _ _ found => found)
    (fun position => copyRenaming_nil position) (fun _ absent => by cases absent) (by simpa using typed)

/-- Plain copies keep an expression's type when every scope slot holds a cell
of its payload type. -/
theorem copyScopePlain_hasType {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {base : Nat → Nat}
    {body : Expr} {type : Ty}
    (slots : ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      context[base index]? = some (.cell (OptionalCell.cellType payload)))
    (typed : HasType context body type definitions) :
    HasType context (SourceCoreSourceCells.copyScopePlain source scope base body) type definitions := by
  simp only [SourceCoreSourceCells.copyScopePlain, scopeCopyRenaming_eq]
  have chain := copyChainPlain_hasType (source := source) (base := base) typed scope 0 [] [] rfl
    (fun _ _ found => by simpa [copyRenaming_nil] using found)
    (fun offset id payload found => by simpa using slots offset id payload found)
  simpa using chain

/-- Every slot of a lexical scope holds a cell of its payload type. -/
theorem scope_slots {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} :
    ∀ (index : Nat) (id : Resolved.LocalId) (payload : Ty), scope[index]? = some (id, payload) →
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? =
        some (Ty.cell (OptionalCell.cellType payload)) := by
  intro index id payload found
  have bound : index < scope.length := (List.getElem?_eq_some_iff.mp found).1
  rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using bound)]
  simp [SourceCoreLocalCell.coreContext, found]

/-- The snapshot form of a generalized declaration without an allocator has
the type of the ordinary declaration it replaces. -/
theorem letInitializedSnapshot_none_hasType {definitions : DataEnvironment} {administrative : Core.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {output payload : Ty} {initializer body code : Expr}
    (payloadWF : Ty.WellFormed definitions payload) (outputWF : Ty.WellFormed definitions output)
    (initialTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) initializer
      (LanguageResult.resultType payload) definitions)
    (bodyTyped : HasType (SourceCoreLocalCell.coreContext ((binder.id, payload) :: scope) ++ administrative) body
      (LanguageResult.resultType output) definitions)
    (accepted : SourceCoreSourceCells.letInitializedSnapshot none source scope binder output payload
      initializer body = .ok code) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code
      (LanguageResult.resultType output) definitions := by
  simp only [SourceCoreSourceCells.letInitializedSnapshot, SourceCoreSourceCells.copyScope_none,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
  subst code
  have referenceWF : Ty.WellFormed definitions (OptionalCell.referenceType payload) :=
    .cell (.sum .unit payloadWF)
  apply LanguageResult.bind_hasType outputWF _ (by simpa [SourceCoreLocalCell.coreContext] using bodyTyped)
  apply copyScopePlain_hasType scope_slots
  exact LanguageResult.bind_hasType referenceWF initialTyped
    (LanguageResult.success_hasType (OptionalCell.allocateInitialized_hasType (.var rfl)))

end Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
