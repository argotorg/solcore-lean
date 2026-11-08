import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GenericHeaps
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.Frontend.Internal.RuntimeValidation

/-!
# Capture copies and function code

Renaming and typing of capture copies, certificates of function code and captures, decorated function code, and the boundary of closures kept from before by-value capture.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming
/-! The renaming that redirects a scope's copied slots to their copies, one
copy at a time. A copy chain copies its slots at the positions
`chainPositions` lists, in copy order. Each further copy at a fresh position
moves that position to the newest slot and every other index one slot
further, so a lookup agreement through the earlier copies extends to the
next one. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming
open Core Frontend Frontend.SourceInference
open SourceSemantics.CaptureBinders (copiedBinder?)
open Frontend.SourceCoreSourceCells (copyRenaming scopeCopyRenaming)

/-- The positions a copy chain copies, in copy order, for the remaining slots
`rest` starting at scope index `index`. -/
def chainPositions (source : TypedSource) (base : Nat → Nat) : SourceCoreLocalCell.Scope → Nat → List Nat
  | [], _ => []
  | (id, _) :: rest, index =>
      match copiedBinder? source id with
      | none => chainPositions source base rest (index + 1)
      | some _ => base index :: chainPositions source base rest (index + 1)

private theorem chainPositions_eq_filterMap (source : TypedSource) (base : Nat → Nat) :
    ∀ (rest : SourceCoreLocalCell.Scope) (index : Nat),
      chainPositions source base rest index =
        ((rest.zipIdx index).filterMap fun ((id, type), position) =>
          (copiedBinder? source id).map fun binder => (position, binder, type)).map fun slot => base slot.1
  | [], _ => rfl
  | (id, type) :: rest, index => by
      rw [List.zipIdx_cons, List.filterMap_cons]
      cases copied : copiedBinder? source id with
      | none => simp [chainPositions, copied, chainPositions_eq_filterMap source base rest (index + 1)]
      | some binder => simp [chainPositions, copied, chainPositions_eq_filterMap source base rest (index + 1)]

/-- A scope's copy renaming is the copy renaming of its chain positions. -/
theorem scopeCopyRenaming_eq (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (base : Nat → Nat) :
    scopeCopyRenaming source scope base = copyRenaming (chainPositions source base scope 0) := by
  rw [chainPositions_eq_filterMap]
  rfl

theorem copyRenaming_nil (index : Nat) : copyRenaming [] index = index := by
  simp [copyRenaming]

private theorem findIdx?_none {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    positions.findIdx? (fun position => decide (position = index)) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro position member
  simp only [decide_eq_false_iff_not]
  rintro rfl
  exact absent member

/-- An uncopied index moves past every copy. -/
theorem copyRenaming_of_not_mem {positions : List Nat} {index : Nat} (absent : index ∉ positions) :
    copyRenaming positions index = index + positions.length := by
  simp only [copyRenaming, findIdx?_none absent]

/-- The newest copy of a fresh position is the first slot. -/
theorem copyRenaming_snoc_self {positions : List Nat} {position : Nat} (fresh : position ∉ positions) :
    copyRenaming (positions ++ [position]) position = 0 := by
  simp [copyRenaming, List.findIdx?_append, findIdx?_none fresh]

private theorem copyRenaming_snoc_of_found {positions : List Nat} {position index ordinal : Nat}
    (found : positions.findIdx? (fun position => decide (position = index)) = some ordinal) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  have bound : ordinal < positions.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
  simp only [copyRenaming, List.findIdx?_append, found, Option.some_or, List.length_append,
    List.length_singleton]
  omega

/-- A further copy moves an index that already has a copy one slot further. -/
theorem copyRenaming_snoc_of_mem {positions : List Nat} {position index : Nat} (member : index ∈ positions) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  cases found : positions.findIdx? (fun position => decide (position = index)) with
  | none =>
      rw [List.findIdx?_eq_none_iff] at found
      simpa using found index member
  | some ordinal => exact copyRenaming_snoc_of_found found

/-- A further copy of another position moves every index one slot further. -/
theorem copyRenaming_snoc_of_ne {positions : List Nat} {position index : Nat} (different : index ≠ position) :
    copyRenaming (positions ++ [position]) index = copyRenaming positions index + 1 := by
  cases found : positions.findIdx? (fun position => decide (position = index)) with
  | none =>
      have other : [position].findIdx? (fun position => decide (position = index)) = none := by
        simp [Ne.symm different]
      simp only [copyRenaming, List.findIdx?_append, found, other, Option.none_or, Option.map_none,
        List.length_append, List.length_singleton]
      omega
  | some ordinal => exact copyRenaming_snoc_of_found found

/-- Lookup agreement along a renaming. `ReadOnly.EnvironmentsAgree` and
`Renaming.Respects` are this relation on environments and contexts. -/
def Agrees {α : Type} (mapping : Renaming) (source target : List α) : Prop :=
  ∀ ⦃index : Nat⦄ ⦃value : α⦄, source[index]? = some value → target[mapping index]? = some value

namespace Agrees

theorem respects {mapping : Renaming} {source target : Core.Context} :
    Agrees mapping source target ↔ Renaming.Respects mapping source target :=
  ⟨fun agree _ _ found => agree found, fun respects _ _ found => respects found⟩

private theorem getElem?_replace {α : Type} {before after : List α} {old new : α} {index : Nat}
    (different : index ≠ before.length) :
    ((before ++ [new]) ++ after)[index]? = (before ++ old :: after)[index]? := by
  rcases Nat.lt_or_gt_of_ne different with lower | upper
  · rw [List.append_assoc, List.getElem?_append_left lower, List.getElem?_append_left lower]
  · obtain ⟨offset, shifted⟩ : ∃ offset, index = before.length + (offset + 1) :=
      ⟨index - before.length - 1, by omega⟩
    subst shifted
    rw [List.append_assoc, List.singleton_append, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    simp

/-- The first unprocessed slot is read at its own position past the earlier
copies. -/
theorem read {α : Type} {mapping : Renaming} {done : List Nat} {before after target : List α} {old : α}
    (agree : Agrees (Renaming.comp mapping (copyRenaming done)) (before ++ old :: after) target)
    (fresh : before.length ∉ done) :
    target[mapping (before.length + done.length)]? = some old := by
  have found := agree (index := before.length) (value := old) (by simp)
  simpa only [Renaming.comp, copyRenaming_of_not_mem fresh] using found

/-- Copying the first unprocessed slot: the copy becomes the newest value
and takes that slot's place. -/
theorem copy {α : Type} {mapping : Renaming} {done : List Nat} {before after target : List α} {old : α}
    (agree : Agrees (Renaming.comp mapping (copyRenaming done)) (before ++ old :: after) target)
    (fresh : before.length ∉ done) (new : α) :
    Agrees (Renaming.comp mapping.lift (copyRenaming (done ++ [before.length])))
      ((before ++ [new]) ++ after) (new :: target) := by
  intro index value found
  by_cases same : index = before.length
  · subst index
    simp only [Renaming.comp, copyRenaming_snoc_self fresh, Renaming.lift]
    simpa using found
  · simp only [Renaming.comp, copyRenaming_snoc_of_ne same, Renaming.lift, List.getElem?_cons_succ]
    exact agree (by rwa [← getElem?_replace (new := new) same])

/-- Skipping the first unprocessed slot moves it into the processed prefix. -/
theorem skip {α : Type} {mapping : Renaming} {before after target : List α} {old : α}
    (agree : Agrees mapping (before ++ old :: after) target) :
    Agrees mapping ((before ++ [old]) ++ after) target := by
  intro index value found
  exact agree (by simpa only [List.append_assoc, List.singleton_append] using found)

end Agrees

end Solcore.SourceSemantics.CoreLowering.CaptureCopyRenaming
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CaptureCopyTyping
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionCodeCertificates
/-! Static certificates for the actual function-expression compiler.  A body
certificate is extracted from the supplied body compiler's accepted output;
it contains no execution premise here.  This layer exposes the exact emitted
parameter wrapper and lambda body, without asserting source frame validity,
stage-guard correctness, or call semantics. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCode

open Frontend Frontend.SourceInference

/-- Ordered results of the real parameter binder compiler. -/
inductive Parameters (policy : SourceCoreFunctions.Policy) (source : TypedSource) :
    SourceCoreLocalCell.Scope → List TypedBinder → List (TypedBinder × Core.Ty) →
      SourceCoreLocalCell.Scope → Prop where
  | nil {scope} : Parameters policy source scope [] [] scope
  | cons {scope finalScope parameter parameters type lowered}
      (head : policy.lowerBinder source scope parameter = .ok type)
      (tail : Parameters policy source ((parameter.id, type) :: scope) parameters lowered finalScope) :
      Parameters policy source scope (parameter :: parameters) ((parameter, type) :: lowered) finalScope

theorem Parameters.of_accepted {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (lowered, finalScope)) :
    Parameters policy source scope parameters lowered finalScope := by
  induction parameters generalizing scope lowered with
  | nil =>
    simp only [SourceCoreFunctions.lambdaParameters, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact .nil
  | cons parameter parameters ih =>
    cases head : policy.lowerBinder source scope parameter with
    | error error => simp [SourceCoreFunctions.lambdaParameters, head, bind, Except.bind] at accepted
    | ok type =>
      cases tail : SourceCoreFunctions.lambdaParameters policy source ((parameter.id, type) :: scope) parameters with
      | error error => simp [SourceCoreFunctions.lambdaParameters, head, tail, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨rest, bodyScope⟩ := pair
        simp only [SourceCoreFunctions.lambdaParameters, head, tail, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact .cons head (ih tail)

theorem Parameters.binders {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (certificate : Parameters policy source scope parameters lowered finalScope) :
    lowered.map Prod.fst = parameters := by
  induction certificate <;> simp_all

theorem Parameters.scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Core.Ty)}
    (certificate : Parameters policy source scope parameters lowered finalScope) :
    finalScope = (lowered.map fun entry => (entry.1.id, entry.2)).reverse ++ scope := by
  induction certificate with
  | nil => rfl
  | cons head tail ih => simpa [List.reverse_cons, List.append_assoc] using ih

abbrev BodyCertificate := TypedSource → SourceCoreLocalCell.Scope → List StatementId → Core.Ty → Core.Expr → Prop

/-- Exact recursive expression callback passed by the existing compiler. -/
def children (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) : SourceCoreFunctions.ExpressionLowerer :=
  fun budget source scope id reasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context source scope id reasonAt

structure LambdaCertificate (bodyCertificate : BodyCertificate)
    (policy : SourceCoreFunctions.Policy) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : TypeSystem.Ty) (statements : List StatementId)
    (reportedType : Core.Ty) (lowered : SourceCoreBasic.LoweredExpr) where
  parameterType : TypeSystem.Ty
  parameterCore : Core.Ty
  resultCore : Core.Ty
  loweredParameters : List (TypedBinder × Core.Ty)
  bodyScope : SourceCoreLocalCell.Scope
  bodyCode : Core.Expr
  found : source.lookupExpression? id = some node
  read : policy.readExpression source id = .ok (node, reportedType)
  form : node.form = .lambda parameters resultType statements
  sourceType : node.type = .function parameterType resultType
  bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameterType
  parameterProjection : policy.projectType (.occurrence id.occurrence) parameterType = .ok parameterCore
  resultProjection : policy.projectType (.occurrence id.occurrence) resultType = .ok resultCore
  parametersTree : Parameters policy source scope parameters loweredParameters bodyScope
  bodyTree : bodyCertificate source bodyScope statements resultCore bodyCode
  emitted : lowered = ⟨reportedType, SourceCoreSourceCells.copyScopePlain source scope (fun index => index)
    (Core.LanguageResult.success (Core.TaggedFunction.anonymous
      (.lambda parameterCore (Core.LanguageResult.resultType resultCore)
        (SourceCoreSourceCells.copyScopePlain source scope (· + 1)
          (SourceCoreFunctions.bindParameters loweredParameters resultCore
            (bodyCode.weakenAt loweredParameters.length))))))⟩

/-- Static extraction is relative to the chosen metadata policy and body
compiler.  Their certificates are kept explicit, and no child evaluation is
assumed. This certificate uses the default tagged callable representation,
ordinary source-cell allocation, the unchanged lambda-body hook, an absent
special-expression hook and a creation-time copy of the captures. -/
theorem lambda_of_accepted
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : policy.lowerSpecial? = none)
    (ordinaryCells : policy.sourceCells = none)
    (ordinaryBody : policy.rawLambdaBody = SourceCoreFunctions.unchangedLambdaBody)
    (ordinaryExpression : policy.rawLambdaExpression = SourceCoreFunctions.unchangedLambdaExpression)
    (defaultCallables : policy.callables = {})
    (snapshot : policy.snapshotLambda id = true)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reportedType))
    (form : node.form = .lambda parameters resultType statements)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    Nonempty (LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, ordinary, ordinaryCells, read, form,
        bind, Except.bind, pure, Except.pure] at accepted
      cases type : node.type with
      | function parameter result =>
        simp only [type] at accepted
        by_cases bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
        · by_cases resultSame : resultType = result
          · subst result
            simp only [bundle, not_true_eq_false, ↓reduceIte] at accepted
            cases parameterProjection : policy.projectType (.occurrence id.occurrence) parameter with
            | error error => simp [parameterProjection] at accepted
            | ok parameterCore =>
              cases resultProjection : policy.projectType (.occurrence id.occurrence) resultType with
              | error error => simp [parameterProjection, resultProjection] at accepted
              | ok resultCore =>
                cases compiledParameters : SourceCoreFunctions.lambdaParameters policy source scope parameters with
                | error error => simp [parameterProjection, resultProjection, compiledParameters] at accepted
                | ok pair =>
                  obtain ⟨loweredParameters, bodyScope⟩ := pair
                  simp only [parameterProjection, resultProjection, compiledParameters] at accepted
                  cases compiledBody : lowerBody (children policy lowerBody fuel context) fuel source bodyScope
                      statements resultCore reasonAt context.internalReason context.internalReason with
                  | error error =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp [compiledBody] at accepted
                  | ok bodyCode =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp only [compiledBody, pure, Except.pure, defaultCallables, ordinaryBody,
                      SourceCoreFunctions.unchangedLambdaBody, ordinaryExpression, SourceCoreFunctions.unchangedLambdaExpression,
                      SourceCoreSourceCells.copyScope_none, snapshot, ↓reduceIte] at accepted
                    cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
                        (Core.TaggedFunction.functionType parameterCore resultCore) with
                    | error error => simp [checked] at accepted
                    | ok doneUnit =>
                      cases doneUnit
                      simp only [checked] at accepted
                      cases accepted
                      exact ⟨⟨parameter, parameterCore, resultCore, loweredParameters, bodyScope, bodyCode,
                      found, read, form, type, bundle, parameterProjection, resultProjection,
                      Parameters.of_accepted compiledParameters, extractBody _ _ _ _ compiledBody, rfl⟩⟩
          · simp [bundle, resultSame, throw] at accepted
        · simp [bundle, throw] at accepted
      | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
        simp [type] at accepted
    · simp [owned, bind, Except.bind, throw] at accepted

/-- The successful ordinary lambda branch itself supplies the metadata read.
The policy law only authenticates which source occurrence that read denotes. -/
theorem lambda_of_accepted_metadata
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : policy.lowerSpecial? = none)
    (ordinaryCells : policy.sourceCells = none)
    (ordinaryBody : policy.rawLambdaBody = SourceCoreFunctions.unchangedLambdaBody)
    (ordinaryExpression : policy.rawLambdaExpression = SourceCoreFunctions.unchangedLambdaExpression)
    (defaultCallables : policy.callables = {})
    (snapshot : policy.snapshotLambda id = true)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType statements)
    (readSound : ∀ selected type, policy.readExpression source id = .ok (selected, type) →
      source.lookupExpression? id = some selected)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    ∃ reportedType, Nonempty
      (LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) := by
  cases read : policy.readExpression source id with
  | error error =>
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      by_cases owned : id.occurrence.owner = source.owner <;>
        simp [owned, found, ordinary, form, read, bind, Except.bind, throw, pure, Except.pure] at accepted
  | ok pair =>
    obtain ⟨selected, type⟩ := pair
    have same := Option.some.inj ((readSound selected type read).symm.trans found)
    subst selected
    exact ⟨type, lambda_of_accepted ordinary ordinaryCells ordinaryBody ordinaryExpression defaultCallables
      snapshot found read form extractBody accepted⟩

def LambdaCertificate.rawBody
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) : Core.Expr :=
  SourceCoreSourceCells.copyScopePlain source scope (· + 1)
    (SourceCoreFunctions.bindParameters certificate.loweredParameters certificate.resultCore
      (certificate.bodyCode.weakenAt certificate.loweredParameters.length))

/-- The callable created at the lambda, before its creation-time copies. -/
def LambdaCertificate.callable
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) : Core.Expr :=
  Core.LanguageResult.success (Core.TaggedFunction.anonymous
    (.lambda certificate.parameterCore (Core.LanguageResult.resultType certificate.resultCore)
      certificate.rawBody))

theorem LambdaCertificate.emitted_callable
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered) :
    lowered = ⟨reportedType, SourceCoreSourceCells.copyScopePlain source scope (fun index => index)
      certificate.callable⟩ :=
  certificate.emitted

/-- Whole-output Core checking supplies wrapper typing independently of the
body certificate's semantic interpretation. The creation-time copies have the
types of the slots they copy, so they leave the body's typing unchanged. -/
theorem LambdaCertificate.rawBody_hasType
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : LambdaCertificate bodyCertificate policy source scope id node parameters resultType statements reportedType lowered)
    {context : Core.Context} {definitions : Core.DataEnvironment}
    (typed : Core.HasType context lowered.expression
      (Core.LanguageResult.resultType (Core.TaggedFunction.functionType certificate.parameterCore certificate.resultCore)) definitions) :
    Core.HasType (certificate.parameterCore :: context) certificate.rawBody
      (Core.LanguageResult.resultType certificate.resultCore) definitions := by
  have emitted := congrArg SourceCoreBasic.LoweredExpr.expression certificate.emitted
  rw [emitted] at typed
  dsimp only at typed
  have callable := CaptureCopyTyping.copyScopePlain_body_hasType (fun _ _ same => same) typed
  rw [Core.LanguageResult.success, Core.TaggedFunction.anonymous] at callable
  cases callable with
  | inRight _ function =>
    cases function with
    | pair _ closure =>
      cases closure with
      | lambda _ _ body => exact body

end Solcore.SourceSemantics.CoreLowering.FunctionCode
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.FunctionCaptures
/-! Finite capture certificates for generated functions.  A closure keeps
locations, so neither the source nor Core certificate recursively unfolds
heap values.  Source metadata validity is a separate heap-indexed fact; Core
world typing alone does not imply it.  Actual captured layouts retain every
administrative slot, with an explicit renaming from the lexical layout.

This module authenticates locations and types, not function code or calls.
It does not change the legacy input policy or normalize arbitrary captures.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.FunctionCaptures

open Frontend Frontend.SourceInference GeneralHeap

/-- The emitted body is interpreted under the actual captured environment.
The canonical lexical environment is only a proof index. -/
structure Layout (catalog : SourceCoreDataCatalog.Catalog)
    (mapping : LocationMap) (world : Core.StoreTyping)
    (scope : SourceCoreLocalCell.Scope) (source : Dynamic.Environment)
    (actual : Core.Environment) where
  administrativeContext : Core.Context
  canonical : Core.Environment
  actualContext : Core.Context
  embedding : Core.Renaming
  represented : DataHeap.EnvRepresents catalog mapping world administrativeContext scope source canonical
  lookups : Core.ReadOnly.EnvironmentsAgree embedding canonical actual
  types : Core.Renaming.Respects embedding
    (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext
  actualTyped : Core.RuntimeEnvironmentHasTypes world actual actualContext catalog.definitions

variable {catalog : SourceCoreDataCatalog.Catalog} {mapping futureMapping : LocationMap}
  {world futureWorld : Core.StoreTyping} {scope : SourceCoreLocalCell.Scope}
  {source : Dynamic.Environment} {actual : Core.Environment}

def Layout.direct {administrativeContext : Core.Context}
    (represented : DataHeap.EnvRepresents catalog mapping world administrativeContext scope source actual) :
    Layout catalog mapping world scope source actual where
  administrativeContext := administrativeContext
  canonical := actual
  actualContext := SourceCoreLocalCell.coreContext scope ++ administrativeContext
  embedding := Core.Renaming.id
  represented := represented
  lookups := fun found => found
  types := Core.Renaming.respects_id _
  actualTyped := represented.runtime_hasTypes

/-- Extension retains both the actual closure environment and its renaming.
No equality between closures created in different environments is asserted. -/
def Layout.extend (layout : Layout catalog mapping world scope source actual)
    (maps : LocationMap.Extends mapping futureMapping)
    (worlds : Core.WorldExtends world futureWorld) :
    Layout catalog futureMapping futureWorld scope source actual where
  administrativeContext := layout.administrativeContext
  canonical := layout.canonical
  actualContext := layout.actualContext
  embedding := layout.embedding
  represented := layout.represented.extend maps worlds
  lookups := layout.lookups
  types := layout.types
  actualTyped := layout.actualTyped.weaken worlds

theorem Layout.lookup (layout : Layout catalog mapping world scope source actual)
    {id : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp source id location) :
    ∃ index payload target,
      SourceCoreLocalCell.lookup? scope id = some (index, payload) ∧
      actual[layout.embedding index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨index, payload, target, slot, reference, represented⟩ := layout.represented.lookup_source found
  exact ⟨index, payload, target, slot, layout.lookups reference, represented⟩

/-- The same captured source location remains the same Core location even
when multiple lexical names alias it. -/
theorem references_same_location {location : Dynamic.Location}
    {left right : Core.Location} {leftType rightType : Core.Ty}
    (first : ReferenceRepresents mapping world location left leftType)
    (second : ReferenceRepresents mapping world location right rightType) :
    left = right ∧ leftType = rightType := by
  have same := Option.some.inj (first.mapped.symm.trans second.mapped)
  subst right
  exact ⟨rfl, Core.Ty.sum.inj (Option.some.inj (first.typed.symm.trans second.typed)) |>.2⟩

/-- Strong lexical agreement belongs to the source heap, independently of
the Core representation.  It allows uninitialized cells and shared aliases;
the stored payloads are not required to be eagerly readable values. -/
structure Certificate (catalog : SourceCoreDataCatalog.Catalog)
    (mapping : LocationMap) (world : Core.StoreTyping) (heap : Dynamic.Heap)
    (context : Context) (scope : SourceCoreLocalCell.Scope)
    (source : Dynamic.Environment) (actual : Core.Environment) where
  layout : Layout catalog mapping world scope source actual
  sourceMetadata : Dynamic.EnvironmentAgrees heap context.locals source

def Certificate.extend {heap futureHeap : Dynamic.Heap} {context : Context}
    (certificate : Certificate catalog mapping world heap context scope source actual)
    (metadata : Dynamic.HeapMetadataExtend heap futureHeap)
    (maps : LocationMap.Extends mapping futureMapping)
    (worlds : Core.WorldExtends world futureWorld) :
    Certificate catalog futureMapping futureWorld futureHeap context scope source actual where
  layout := certificate.layout.extend maps worlds
  sourceMetadata := certificate.sourceMetadata.mono metadata

/-- Static lexical lookup recovers the exact source cell metadata and its
mapped reference in the actual closure environment. -/
theorem Certificate.lookup {heap : Dynamic.Heap} {context : Context}
    (certificate : Certificate catalog mapping world heap context scope source actual)
    {id : Resolved.LocalId} {scheme : TypeSystem.Scheme}
    (found : Resolved.LocalScope.Lookup context.locals id scheme) :
    ∃ location cell index payload target,
      Dynamic.Environment.LooksUp source id location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = scheme.body ∧
      Dynamic.LocalCellStorage id scheme cell ∧
      SourceCoreLocalCell.lookup? scope id = some (index, payload) ∧
      actual[certificate.layout.embedding index]? =
        some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨location, cell, lookup, read, type, storage⟩ := certificate.sourceMetadata.lookup found
  obtain ⟨index, payload, target, slot, captured, reference⟩ := certificate.layout.lookup lookup
  exact ⟨location, cell, index, payload, target, lookup, read, type, storage, slot, captured, reference⟩

end Solcore.SourceSemantics.CoreLowering.FunctionCaptures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
/-! Native typing of the actual imperative compiler traversal. The static
admission predicate and callback laws retain the source and lexical scope.
No execution judgment or whole emitted-body typing is a field of the policy.
Concrete frontend profiles must establish these callback laws separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
open Core Frontend SourceInference
abbrev Scope := SourceCoreLoops.Scope
abbrev Admission := TypedSource → Scope → Prop

def context (scope : Scope) (administrative : Core.Context) : Core.Context :=
  SourceCoreLocalCell.coreContext scope ++ administrative

def FlowNative (definitions : DataEnvironment) (administrative : Core.Context)
    (admitted : Admission) (flow : SourceCoreLoops.FlowLowerer) : Prop :=
  ∀ fuel source scope statements type reasonAt selfReason code,
    admitted source scope → type.WellFormed definitions →
    flow fuel source scope statements type reasonAt selfReason = .ok code →
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions

/-- These are laws about the actual supplied callbacks. Admission includes the
source typing, metadata and lexical invariants needed by a concrete profile.
The match law consumes the exact recursive child callback, including its
independently admitted child sources and scopes. -/
structure PolicyLaws (definitions : DataEnvironment) (administrative : Core.Context)
    (admitted : Admission) (policy : SourceCoreLoops.Policy) : Prop where
  expression : ∀ fuel source scope id reasonAt lowered,
    admitted source scope →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    HasType (context scope administrative) lowered.expression
      (LanguageResult.resultType lowered.type) definitions
  binder : ∀ source scope binder type,
    admitted source scope → policy.lowerBinder source scope binder = .ok type →
    type.WellFormed definitions ∧ admitted source ((binder.id, type) :: scope)
  uninitialized : ∀ source scope binder payload output body code,
    admitted source scope → payload.WellFormed definitions → output.WellFormed definitions →
    HasType (context ((binder.id, payload) :: scope) administrative) body
      (LanguageResult.resultType output) definitions →
    SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id
      binder payload body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  initialized : ∀ source scope binder payload output initializer body code,
    admitted source scope → payload.WellFormed definitions → output.WellFormed definitions →
    HasType (context scope administrative) initializer (LanguageResult.resultType payload) definitions →
    HasType (context ((binder.id, payload) :: scope) administrative) body
      (LanguageResult.resultType output) definitions →
    SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id
      binder output payload initializer body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  /-- A generalized local copies its scope around its initializer and binder. -/
  initializedSnapshot : ∀ source scope binder payload output initializer body code,
    admitted source scope → payload.WellFormed definitions → output.WellFormed definitions →
    HasType (context scope administrative) initializer (LanguageResult.resultType payload) definitions →
    HasType (context ((binder.id, payload) :: scope) administrative) body
      (LanguageResult.resultType output) definitions →
    SourceCoreSourceCells.letInitializedSnapshot policy.sourceCells source scope
      binder output payload initializer body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  assignment : ∀ fuel source scope site assignment operator rhs output body reasonAt code,
    admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs output body reasonAt = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  bitNot : ∀ callback source scope site assignment output body code,
    policy.assignBitNot = some callback → admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    callback source scope site assignment output body = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  bitNotWithExpression : ∀ callback fuel source scope site assignment output body reasonAt code,
    policy.assignBitNotWithExpression = some callback → admitted source scope → output.WellFormed definitions →
    HasType (context scope administrative) body (LanguageResult.resultType output) definitions →
    callback policy.lowerExpression fuel source scope site assignment output body reasonAt = .ok code →
    HasType (context scope administrative) code (LanguageResult.resultType output) definitions
  matchWith : ∀ callback flow fuel source scope id resolution type reasonAt selfReason code,
    policy.lowerMatch = some callback → FlowNative definitions administrative admitted flow →
    admitted source scope → type.WellFormed definitions →
    callback policy.lowerExpression flow fuel source scope id resolution type reasonAt selfReason = .ok code →
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty} {returned : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok returned) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted <;> simp_all

/-- The actual header fold preserves native typing for any typed continuation
at the resulting admitted scope. Its parent diagnostic site remains exact. -/
theorem header_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {items : List ForItemForm}
    {type : Ty} {reasonAt : ExpressionId → Word} {site : SourceCoreElaboration.ErrorSite}
    {next : Scope → Except SourceCoreBasic.Error Expr} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (continuation : ∀ finalScope body, admitted source finalScope → next finalScope = .ok body →
      HasType (context finalScope administrative) body (LocalLoop.resultType type) definitions)
    (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items type reasonAt next = .ok code) :
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions := by
  induction fuel generalizing scope items code with
  | zero =>
    cases items with
    | nil => exact continuation scope code allowed accepted
    | cons item rest => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact continuation scope code allowed accepted
    | cons item rest =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      have controlWF := LocalLoop.controlType_wellFormed wellFormed
      cases item with
      | letDecl binder initializer =>
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, accepted⟩ := bind_ok accepted
        obtain ⟨payloadWF, extended⟩ := laws.binder source scope binder payload allowed projected
        have bodyTyped := ih extended compiled
        cases initializer with
        | none => exact laws.uninitialized source scope binder payload _ body code allowed payloadWF controlWF bodyTyped accepted
        | some initializer =>
          obtain ⟨lowered, loweredAccepted, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          have same := ensure_same checked
          have initializerTyped := laws.expression fuel source scope initializer reasonAt lowered allowed loweredAccepted
          rw [← same] at initializerTyped
          split at emitted
          · exact laws.initialized source scope binder payload _ lowered.expression body code
              allowed payloadWF controlWF initializerTyped bodyTyped emitted
          · exact laws.initializedSnapshot source scope binder payload _ lowered.expression body code
              allowed payloadWF controlWF initializerTyped bodyTyped emitted
      | expression expression =>
        obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalSequence.discard_hasType controlWF
          (laws.expression fuel source scope expression reasonAt lowered allowed generated)
          (ih allowed compiled)
      | assignValue assignment operator rhs =>
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        exact laws.assignment fuel source scope site assignment operator rhs _ body reasonAt code
          allowed controlWF (ih allowed compiled) emitted
      | assignBitNot assignment =>
        cases selectedWith : policy.assignBitNotWithExpression with
        | some callback =>
          simp only [selectedWith] at accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.bitNotWithExpression callback fuel source scope site assignment _ body reasonAt code
            selectedWith allowed controlWF (ih allowed compiled) emitted
        | none =>
          simp only [selectedWith] at accepted
          cases selected : policy.assignBitNot with
          | none => simp [selected] at accepted
          | some callback =>
            simp only [selected] at accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            exact laws.bitNot callback source scope site assignment _ body code
              selected allowed controlWF (ih allowed compiled) emitted

/-- Every recursive statement, header, post and match child is typed by the
same actual compiler's fuel induction. Callback laws do not contain the
statement traversal or its final code as an assumed theorem. -/
theorem flow_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {statements : List StatementId}
    {type : Ty} {reasonAt : ExpressionId → Word} {tailReturns : Bool} {selfReason : Word} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements
      type reasonAt tailReturns selfReason = .ok code) :
    HasType (context scope administrative) code (LocalLoop.resultType type) definitions := by
  induction fuel generalizing source scope statements type reasonAt tailReturns selfReason code with
  | zero =>
    cases statements with
    | nil => cases accepted; exact LocalLoop.fallthrough_hasType wellFormed
    | cons id rest => cases accepted
  | succ fuel ih =>
    cases statements with
    | nil => cases accepted; exact LocalLoop.fallthrough_hasType wellFormed
    | cons id rest =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨pair, _, accepted⟩ := bind_ok accepted
      rcases pair with ⟨node, statementType⟩
      have controlWF := LocalLoop.controlType_wellFormed wellFormed
      cases form : node.form with
      | letDecl binder initializer =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨payloadWF, extended⟩ := laws.binder source scope binder payload allowed projected
        cases initializer with
        | none =>
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.uninitialized source scope binder payload _ body code allowed payloadWF controlWF
            (ih extended wellFormed compiled) emitted
        | some initializer =>
          obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          have typed := laws.expression fuel source scope initializer reasonAt lowered allowed generated
          rw [← ensure_same checked] at typed
          split at emitted
          · exact laws.initialized source scope binder payload _ lowered.expression body code
              allowed payloadWF controlWF typed (ih extended wellFormed compiled) emitted
          · exact laws.initializedSnapshot source scope binder payload _ lowered.expression body code
              allowed payloadWF controlWF typed (ih extended wellFormed compiled) emitted
      | assignValue assignment operator rhs =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
        exact laws.assignment fuel source scope (.occurrence id.occurrence) assignment operator rhs _ body reasonAt code
          allowed controlWF (ih allowed wellFormed compiled) emitted
      | assignBitNot assignment =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        cases selectedWith : policy.assignBitNotWithExpression with
        | some callback =>
          simp only [selectedWith] at accepted
          obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
          exact laws.bitNotWithExpression callback fuel source scope (.occurrence id.occurrence) assignment _ body reasonAt code
            selectedWith allowed controlWF (ih allowed wellFormed compiled) emitted
        | none =>
          simp only [selectedWith] at accepted
          cases selected : policy.assignBitNot with
          | none => simp [selected] at accepted
          | some callback =>
            simp only [selected] at accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            exact laws.bitNot callback source scope (.occurrence id.occurrence) assignment _ body code
              selected allowed controlWF (ih allowed wellFormed compiled) emitted
      | returnStmt expression =>
        simp only [form] at accepted
        cases expression with
        | none =>
          obtain ⟨_, resultChecked, accepted⟩ := bind_ok accepted
          obtain ⟨_, unitChecked, emitted⟩ := bind_ok accepted
          cases emitted
          have same : type = .unit := (ensure_same resultChecked).trans (ensure_same unitChecked).symm
          rw [same]
          exact LocalLoop.returned_hasType .unit
        | some expression =>
          obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          cases emitted
          have typed := laws.expression fuel source scope expression reasonAt lowered allowed generated
          rw [← ensure_same checked] at typed
          exact LocalLoop.returnValue_hasType wellFormed typed
      | expression expression semicolon =>
        simp only [form] at accepted
        obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
        have typed := laws.expression fuel source scope expression reasonAt lowered allowed generated
        split at accepted
        · obtain ⟨_, _, accepted⟩ := bind_ok accepted
          obtain ⟨_, checked, emitted⟩ := bind_ok accepted
          cases emitted
          rw [← ensure_same checked] at typed
          exact LocalLoop.returnValue_hasType wellFormed typed
        · split at accepted
          all_goals
            obtain ⟨_, _, accepted⟩ := bind_ok accepted
            obtain ⟨body, compiled, emitted⟩ := bind_ok accepted
            cases emitted
            exact LocalSequence.discard_hasType controlWF typed (ih allowed wellFormed compiled)
      | block statements =>
        simp only [form] at accepted
        obtain ⟨block, compiledBlock, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.sequence_hasType wellFormed
          (ih allowed wellFormed compiledBlock) (ih allowed wellFormed compiledBody)
      | ifThen condition thenBody elseBody =>
        simp only [form] at accepted
        obtain ⟨conditionCode, generated, accepted⟩ := bind_ok accepted
        obtain ⟨_, checked, accepted⟩ := bind_ok accepted
        obtain ⟨thenCode, compiledThen, accepted⟩ := bind_ok accepted
        have conditionTyped := laws.expression fuel source scope condition reasonAt conditionCode allowed generated
        rw [← ensure_same checked] at conditionTyped
        cases elseBody with
        | none =>
          obtain ⟨elseCode, compiledElse, accepted⟩ := bind_ok accepted
          cases compiledElse
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          exact LocalLoop.sequence_hasType wellFormed
            (LocalLoop.conditional_hasType wellFormed conditionTyped (ih allowed wellFormed compiledThen)
              (LocalLoop.fallthrough_hasType wellFormed))
            (ih allowed wellFormed compiledBody)
        | some statements =>
          obtain ⟨elseCode, compiledElse, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          exact LocalLoop.sequence_hasType wellFormed
            (LocalLoop.conditional_hasType wellFormed conditionTyped (ih allowed wellFormed compiledThen)
              (ih allowed wellFormed compiledElse))
            (ih allowed wellFormed compiledBody)
      | whileLoop condition statements =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨conditionCode, generated, accepted⟩ := bind_ok accepted
        obtain ⟨_, checked, accepted⟩ := bind_ok accepted
        obtain ⟨loopCode, compiledLoop, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        have conditionTyped := laws.expression fuel source scope condition reasonAt conditionCode allowed generated
        rw [← ensure_same checked] at conditionTyped
        exact LocalLoop.sequence_hasType wellFormed
          (LocalLoop.whileLoop_hasType selfReason wellFormed conditionTyped (ih allowed wellFormed compiledLoop))
          (ih allowed wellFormed compiledBody)
      | forLoop initializer condition post statements =>
        simp only [form] at accepted
        obtain ⟨_, _, accepted⟩ := bind_ok accepted
        obtain ⟨loopCode, compiledLoop, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
        cases emitted
        apply LocalLoop.sequence_hasType wellFormed ?_ (ih allowed wellFormed compiledBody)
        apply header_native laws allowed wellFormed ?_ compiledLoop
        intro loopScope loopBody loopAllowed continued
        obtain ⟨conditionCode, generated, continued⟩ := bind_ok continued
        obtain ⟨_, checked, continued⟩ := bind_ok continued
        obtain ⟨bodyCode, bodyAccepted, continued⟩ := bind_ok continued
        obtain ⟨postCode, postAccepted, emitted⟩ := bind_ok continued
        cases emitted
        have conditionTyped := laws.expression fuel source loopScope condition reasonAt conditionCode loopAllowed generated
        rw [← ensure_same checked] at conditionTyped
        apply LocalLoop.iterate_hasType selfReason wellFormed conditionTyped (ih loopAllowed wellFormed bodyAccepted)
        apply header_native laws loopAllowed wellFormed ?_ postAccepted
        intro postScope postBody _ compiledPost
        cases compiledPost
        exact LocalLoop.fallthrough_hasType wellFormed
      | matchWith resolution =>
        simp only [form] at accepted
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some callback =>
          simp only [selected] at accepted
          obtain ⟨matched, compiledMatch, accepted⟩ := bind_ok accepted
          obtain ⟨body, compiledBody, emitted⟩ := bind_ok accepted
          cases emitted
          apply LocalLoop.sequence_hasType wellFormed ?_ (ih allowed wellFormed compiledBody)
          apply laws.matchWith callback _ fuel source scope id resolution type reasonAt selfReason matched
            selected ?_ allowed wellFormed compiledMatch
          intro childFuel childSource childScope childStatements childType childReason childSelf childCode childAllowed childWF childAccepted
          exact ih childAllowed childWF childAccepted
      | breakStmt =>
        simp only [form] at accepted
        obtain ⟨_, _, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.breaking_hasType wellFormed
      | continueStmt =>
        simp only [form] at accepted
        obtain ⟨_, _, emitted⟩ := bind_ok accepted
        cases emitted
        exact LocalLoop.continuing_hasType wellFormed

/-- Finish and escaped-loop handling are the actual compiler wrappers. The
fallback is typed for both Unit and non-Unit results without weakening fuel
exhaustion into a completed source execution. -/
theorem body_native {definitions : DataEnvironment} {administrative : Core.Context}
    {admitted : Admission} {policy : SourceCoreLoops.Policy}
    (laws : PolicyLaws definitions administrative admitted policy)
    {fuel : Nat} {source : TypedSource} {scope : Scope} {statements : List StatementId}
    {type : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (allowed : admitted source scope) (wellFormed : type.WellFormed definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      type reasonAt fellThrough escaped = .ok code) :
    HasType (context scope administrative) code (LanguageResult.resultType type) definitions := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := bind_ok accepted
  cases emitted
  apply LocalControl.finish_hasType wellFormed
    (LocalLoop.toControl_hasType escaped wellFormed (flow_native laws allowed wellFormed generated))
  split
  · rename_i same
    simpa only [same] using (LanguageResult.success_hasType (HasType.unit
      (context := context scope administrative) (definitions := definitions)))
  · exact LanguageResult.failure_hasType wellFormed .word

end Solcore.SourceSemantics.CoreLowering.ImperativeNativePolicyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary
/-! Audit of the existing typed-source input predicate.  These theorems
describe its current domain; they do not strengthen that domain or certify
source lexical typing.  In particular, readable captures alone do not ensure
that the binders needed by a checked closure body are present.  The public
runner also applies `validateTypeFuel`, which rejects raw closure inputs;
this predicate gap alone therefore does not exhibit an admitted bad call. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary

open Frontend Frontend.SourceInference TypeSystem
open Frontend.SourceTypedRuntime

/-- The public runner's earlier structural input check rejects raw closures.
Thus replacing a readable capture list does not make such a public input
admissible, even though the subsequent deep-safety predicate accepts it. -/
theorem validateTypeFuel_closure_notValid
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan) (expected : Ty)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (captured : SourceTypedRuntime.Environment) (evidence : RuntimeEvidenceEnvironment) :
    (Value.closure parameters resultType body source owner captured evidence).validateTypeFuel fuel signatures plan expected ≠ .valid := by
  cases fuel with
  | zero => intro impossible; cases impossible
  | succ fuel =>
    rw [Value.validateTypeFuel.eq_12] <;> simp

theorem capturesReadable_empty (state : RuntimeState) :
    CapturesReadable state [] := by
  intro binding member
  cases member

/-- Code/evidence authenticity and the outer function type survive arbitrary
capture replacement, as long as every replacement location is readable. -/
theorem deeplySafe_replaceCaptures
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {parameters : List TypedBinder} {resultType expected : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {captured replacement : SourceTypedRuntime.Environment}
    {evidence : RuntimeEvidenceEnvironment}
    (safe : (Value.closure parameters resultType body source owner captured evidence).DeeplySafe signatures plan state expected)
    (readable : CapturesReadable state replacement) :
    (Value.closure parameters resultType body source owner replacement evidence).DeeplySafe signatures plan state expected := by
  refine ⟨?_, ?_⟩
  · cases safe.typed with
    | closure outer expected _ => exact .closure outer expected readable
  · cases safe.code_and_evidence with
    | closure valid => exact .closure valid

/-- Thus the legacy predicate cannot imply capture completeness, even for an
otherwise authentic and accepted closure. -/
theorem deeplySafe_emptyCaptures
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {parameters : List TypedBinder} {resultType expected : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {captured : SourceTypedRuntime.Environment}
    {evidence : RuntimeEvidenceEnvironment}
    (safe : (Value.closure parameters resultType body source owner captured evidence).DeeplySafe signatures plan state expected) :
    (Value.closure parameters resultType body source owner [] evidence).DeeplySafe signatures plan state expected :=
  deeplySafe_replaceCaptures safe (capturesReadable_empty state)

/-- The executable validator has the same limited observation: two capture
lists with equal readability checks are indistinguishable to it. -/
theorem isDeeplySafe_capture_observation
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState)
    (parameters : List TypedBinder) (resultType expected : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (captured replacement : SourceTypedRuntime.Environment)
    (evidence : RuntimeEvidenceEnvironment)
    (same : capturesReadable state captured = capturesReadable state replacement) :
    (Value.closure parameters resultType body source owner captured evidence).isDeeplySafe fuel signatures plan state expected =
      (Value.closure parameters resultType body source owner replacement evidence).isDeeplySafe fuel signatures plan state expected := by
  cases fuel <;>
    simp only [Value.isDeeplySafe, Value.hasLocalTypeFuel,
      Value.hasValidCodeAndEvidenceFuel, Value.type?, same]
  rfl

end Solcore.SourceSemantics.CoreLowering.LegacyClosureBoundary
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
/-! Actual lambda compilation with a callable representation hook. The raw
lambda code certificate is retained beneath the hook's exact accepted result,
and the creation-time copies of the captures wrap the decorated callable.
The parameter wrapper uses ordinary source-cell allocation and the unchanged
raw lambda-body hook. The hook is not
assumed to preserve meaning: the concrete representation layer
must authenticate its decoration separately. Special-expression handling must
fall through at this occurrence; a successful special hook is another branch. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
open Frontend Frontend.SourceInference FunctionCode

/-- Exact static fallthrough from the optional special-expression compiler. -/
def SpecialPasses (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) : Prop :=
  (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower context (children policy lowerBody fuel context) (fuel + 1) source scope id reasonAt) = .ok none

structure LambdaCertificate (bodyCertificate : BodyCertificate)
    (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : TypeSystem.Ty) (statements : List StatementId)
    (reportedType : Core.Ty) (lowered : SourceCoreBasic.LoweredExpr) where
  rawLowered : SourceCoreBasic.LoweredExpr
  raw : FunctionCode.LambdaCertificate bodyCertificate policy source scope id node parameters resultType
    statements reportedType rawLowered
  expression : Core.Expr
  checkedType : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
    (policy.callables.functionType raw.parameterCore raw.resultCore) = .ok ()
  decoration : policy.callables.decorateCallable context source node (.lambda id)
    raw.parameterCore raw.resultCore raw.callable = .ok expression
  emitted : lowered = ⟨reportedType,
    SourceCoreSourceCells.copyScopePlain source scope (fun index => index) expression⟩

/-- Successful ordinary traversal supplies the real metadata, parameter/body
certificates and exact hook result. No child execution is a premise. -/
theorem lambda_of_accepted
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reportedType : Core.Ty} {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : SpecialPasses policy lowerBody fuel context source scope id reasonAt)
    (ordinaryCells : policy.sourceCells = none)
    (ordinaryBody : policy.rawLambdaBody = SourceCoreFunctions.unchangedLambdaBody)
    (ordinaryExpression : policy.rawLambdaExpression = SourceCoreFunctions.unchangedLambdaExpression)
    (snapshot : policy.snapshotLambda id = true)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, reportedType))
    (form : node.form = .lambda parameters resultType statements)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Nonempty (LambdaCertificate bodyCertificate policy context source scope id node parameters resultType statements reportedType lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  change (match policy.lowerSpecial? with
    | none => pure none
    | some lower => lower context (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
          childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
  simp only [pure, Except.pure] at ordinary
  cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
  all_goals
    try rw [ordinary] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, read, form,
        bind, Except.bind, pure, Except.pure] at accepted
      cases type : node.type with
      | function parameter result =>
        simp only [type] at accepted
        by_cases bundle : TypeSystem.Ty.productMany (parameters.map (·.scheme.body)) = parameter
        · by_cases resultSame : resultType = result
          · subst result
            simp only [bundle, not_true_eq_false, ↓reduceIte] at accepted
            cases parameterProjection : policy.projectType (.occurrence id.occurrence) parameter with
            | error error => simp [parameterProjection] at accepted
            | ok parameterCore =>
              cases resultProjection : policy.projectType (.occurrence id.occurrence) resultType with
              | error error => simp [parameterProjection, resultProjection] at accepted
              | ok resultCore =>
                cases compiledParameters : SourceCoreFunctions.lambdaParameters policy source scope parameters with
                | error error => simp [parameterProjection, resultProjection, compiledParameters] at accepted
                | ok pair =>
                  obtain ⟨loweredParameters, bodyScope⟩ := pair
                  simp only [parameterProjection, resultProjection, compiledParameters] at accepted
                  cases compiledBody : lowerBody (children policy lowerBody fuel context) fuel source bodyScope
                      statements resultCore reasonAt context.internalReason context.internalReason with
                  | error error =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp [compiledBody] at accepted
                  | ok bodyCode =>
                    change lowerBody (fun budget childSource childScope childId childReasonAt =>
                      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
                        childSource childScope childId childReasonAt) fuel source bodyScope statements resultCore
                          reasonAt context.internalReason context.internalReason = _ at compiledBody
                    simp only [compiledBody, ordinaryCells, ordinaryBody, SourceCoreFunctions.unchangedLambdaBody, ordinaryExpression, SourceCoreFunctions.unchangedLambdaExpression,
                      SourceCoreSourceCells.copyScope_none, snapshot, ↓reduceIte, pure, Except.pure] at accepted
                    cases checked : SourceCoreBasic.ensureType (.occurrence id.occurrence) reportedType
                        (policy.callables.functionType parameterCore resultCore) with
                    | error error => simp [checked] at accepted
                    | ok doneUnit =>
                      cases doneUnit
                      simp only [checked] at accepted
                      let rawExpression := Core.LanguageResult.success (Core.TaggedFunction.anonymous
                        (.lambda parameterCore (Core.LanguageResult.resultType resultCore)
                          (SourceCoreSourceCells.copyScopePlain source scope (· + 1)
                            (SourceCoreFunctions.bindParameters loweredParameters resultCore
                              (bodyCode.weakenAt loweredParameters.length)))))
                      cases decorated : policy.callables.decorateCallable context source node (.lambda id)
                          parameterCore resultCore rawExpression with
                      | error error => simp [rawExpression] at decorated; simp [decorated] at accepted
                      | ok expression =>
                        simp only [rawExpression] at decorated
                        simp only [decorated, Except.ok.injEq] at accepted
                        subst lowered
                        exact ⟨⟨_, ⟨parameter, parameterCore, resultCore, loweredParameters, bodyScope, bodyCode,
                          found, read, form, type, bundle, parameterProjection, resultProjection,
                          Parameters.of_accepted compiledParameters, extractBody _ _ _ _ compiledBody, rfl⟩,
                          expression, checked, decorated, rfl⟩⟩
          · simp [bundle, resultSame, throw] at accepted
        · simp [bundle, throw] at accepted
      | «variable» | parameter | constructor | application | product | mapping | proxy | comptime | error =>
        simp [type] at accepted
    · simp [owned, bind, Except.bind, throw] at accepted


/-- The successful branch supplies its own metadata read. The profile's read
soundness law identifies that metadata with the actual occurrence. -/
theorem lambda_of_accepted_metadata
    {bodyCertificate : BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {resultType : TypeSystem.Ty} {statements : List StatementId}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}
    (ordinary : SpecialPasses policy lowerBody fuel context source scope id reasonAt)
    (ordinaryCells : policy.sourceCells = none)
    (ordinaryBody : policy.rawLambdaBody = SourceCoreFunctions.unchangedLambdaBody)
    (ordinaryExpression : policy.rawLambdaExpression = SourceCoreFunctions.unchangedLambdaExpression)
    (snapshot : policy.snapshotLambda id = true)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType statements)
    (readSound : ∀ selected type, policy.readExpression source id = .ok (selected, type) →
      source.lookupExpression? id = some selected)
    (extractBody : ∀ budget bodyScope type code,
      lowerBody (children policy lowerBody budget context) budget source bodyScope statements type
        reasonAt context.internalReason context.internalReason = .ok code →
      bodyCertificate source bodyScope statements type code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ reportedType, Nonempty
      (LambdaCertificate bodyCertificate policy context source scope id node parameters resultType statements reportedType lowered) := by
  cases read : policy.readExpression source id with
  | error error =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    change (match policy.lowerSpecial? with
      | none => pure none
      | some lower => lower context (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
            childSource childScope childId childReasonAt) (fuel + 1) source scope id reasonAt) = .ok none at ordinary
    simp only [pure, Except.pure] at ordinary
    cases hook : policy.lowerSpecial? <;> simp only [hook] at ordinary accepted
    all_goals
      try rw [ordinary] at accepted
      by_cases owned : id.occurrence.owner = source.owner <;>
        simp [owned, found, form, read, bind, Except.bind, throw, pure, Except.pure] at accepted
  | ok pair =>
    obtain ⟨selected, type⟩ := pair
    have same := Option.some.inj ((readSound selected type read).symm.trans found)
    subst selected
    exact ⟨type, lambda_of_accepted ordinary ordinaryCells ordinaryBody ordinaryExpression snapshot found read form
      extractBody accepted⟩

end Solcore.SourceSemantics.CoreLowering.DecoratedFunctionCode
end
