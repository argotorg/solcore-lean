import Solcore.Frontend.ProgramSignatures

/-!
# Root types

The types a root's signature may hold: those with a public value. A memory array, a slice and a memref
have none, so a root whose parameter or result type holds one anywhere is rejected, as the memory
arrays note's decision 5 states. Main declarations: `SourceCoreRootTypes.holdsView` and its laws for
the proofs, `ViewFree`.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRootTypes
open TypeSystem

/-- Whether a type constructor of a memory array, a slice, a memref or an array object occurs in a type,
in any position. -/
def mentionsView : Ty → Bool
  | .constructor (.builtin .memoryArray)
  | .constructor (.builtin .arraySlice)
  | .constructor (.builtin .memref)
  | .constructor (.builtin .arrayObject) => true
  | .application leftPart rightPart
  | .function leftPart rightPart
  | .product leftPart rightPart
  | .mapping leftPart rightPart => mentionsView leftPart || mentionsView rightPart
  | .proxy inner
  | .comptime inner => mentionsView inner
  | .variable _
  | .parameter _
  | .constructor _
  | .error => false

/-- The declarations a type names, in any position. -/
def declarations : Ty → List Resolved.DeclarationId
  | .constructor (.declaration declaration) => [declaration]
  | .application leftPart rightPart
  | .function leftPart rightPart
  | .product leftPart rightPart
  | .mapping leftPart rightPart => declarations leftPart ++ declarations rightPart
  | .proxy inner
  | .comptime inner => declarations inner
  | .variable _
  | .parameter _
  | .constructor (.builtin _)
  | .error => []

/-- The payload types of a data declaration's constructors, as declared, over its own parameters. -/
def payloadTypes (data : ProgramDataSignature) : List Ty :=
  data.constructors.flatMap (·.payloadTypes)

/-- Whether a payload of `data` mentions a view or names one of `found`. -/
def holdsInPayloads (found : List Resolved.DeclarationId) (data : ProgramDataSignature) : Bool :=
  (payloadTypes data).any fun payload =>
    mentionsView payload || (declarations payload).any fun declaration => found.contains declaration

/-- The data declarations whose payloads hold a view, directly or through other declarations: a
fixpoint reached from `found` within `fuel` rounds, or `none`. -/
def viewDeclarations (signatures : ProgramSignatures) : Nat → List Resolved.DeclarationId →
    Option (List Resolved.DeclarationId)
  | 0, _ => none
  | fuel + 1, found =>
    let next := (signatures.dataTypes.filter fun data =>
      !found.contains data.id && holdsInPayloads found data).map (·.id)
    if next.isEmpty then some found else viewDeclarations signatures fuel (found ++ next)

/-- Whether one of `named` holds a view in its payloads. A fixpoint that is not reached counts as
holding one. -/
def heldBy (signatures : ProgramSignatures) (named : List Resolved.DeclarationId) : Bool :=
  match viewDeclarations signatures (signatures.dataTypes.length + 1) [] with
  | none => true
  | some found => named.any fun declaration => found.contains declaration

/-- Whether a type has no public value: a memory array, a slice or a memref occurs in it, in a type
argument, a tuple, a function type or a mapping, or in a constructor payload of an enum it names,
directly or through other enums. -/
def holdsView (signatures : ProgramSignatures) (type : Ty) : Bool :=
  mentionsView type || heldBy signatures (declarations type)

/-- A type with a public value: it holds no memory array, slice or memref anywhere. -/
abbrev ViewFree (signatures : ProgramSignatures) (type : Ty) : Prop :=
  holdsView signatures type = false

variable {signatures : ProgramSignatures}

theorem heldBy_append (first second : List Resolved.DeclarationId) :
    heldBy signatures (first ++ second) = (heldBy signatures first || heldBy signatures second) := by
  unfold heldBy
  split <;> simp

private theorem holdsView_pair {combined : Ty} (left right : Ty)
    (mentions : mentionsView (combined : Ty) = (mentionsView left || mentionsView right))
    (named : declarations combined = declarations left ++ declarations right) :
    holdsView signatures combined = (holdsView signatures left || holdsView signatures right) := by
  unfold holdsView
  rw [mentions, named, heldBy_append]
  cases mentionsView left <;> cases mentionsView right <;>
    cases heldBy signatures (declarations left) <;> cases heldBy signatures (declarations right) <;> rfl

theorem holdsView_application (function argument : Ty) :
    holdsView signatures (.application function argument) =
      (holdsView signatures function || holdsView signatures argument) :=
  holdsView_pair function argument rfl rfl

theorem holdsView_function (parameter result : Ty) :
    holdsView signatures (.function parameter result) =
      (holdsView signatures parameter || holdsView signatures result) :=
  holdsView_pair parameter result rfl rfl

theorem holdsView_product (left right : Ty) :
    holdsView signatures (.product left right) =
      (holdsView signatures left || holdsView signatures right) :=
  holdsView_pair left right rfl rfl

theorem holdsView_mapping (key value : Ty) :
    holdsView signatures (.mapping key value) = (holdsView signatures key || holdsView signatures value) :=
  holdsView_pair key value rfl rfl

theorem holdsView_proxy (inner : Ty) : holdsView signatures (.proxy inner) = holdsView signatures inner := rfl

theorem holdsView_comptime (inner : Ty) :
    holdsView signatures (.comptime inner) = holdsView signatures inner := rfl

namespace ViewFree

theorem application {function argument : Ty} (free : ViewFree signatures (.application function argument)) :
    ViewFree signatures function ∧ ViewFree signatures argument := by
  simpa [ViewFree, holdsView_application] using free

theorem function {parameter result : Ty} (free : ViewFree signatures (.function parameter result)) :
    ViewFree signatures parameter ∧ ViewFree signatures result := by
  simpa [ViewFree, holdsView_function] using free

theorem product {left right : Ty} (free : ViewFree signatures (.product left right)) :
    ViewFree signatures left ∧ ViewFree signatures right := by
  simpa [ViewFree, holdsView_product] using free

theorem mapping {key value : Ty} (free : ViewFree signatures (.mapping key value)) :
    ViewFree signatures key ∧ ViewFree signatures value := by
  simpa [ViewFree, holdsView_mapping] using free

theorem comptime {inner : Ty} (free : ViewFree signatures (.comptime inner)) : ViewFree signatures inner := free

theorem proxy {inner : Ty} (free : ViewFree signatures (.proxy inner)) : ViewFree signatures inner := free

theorem not_array (element : Ty) : ¬ ViewFree signatures (Ty.array element) := by
  simp [ViewFree, Ty.array, holdsView, mentionsView]

theorem not_arraySlice (base : Ty) : ¬ ViewFree signatures (Ty.arraySlice base) := by
  simp [ViewFree, Ty.arraySlice, holdsView, mentionsView]

theorem not_memref (element : Ty) : ¬ ViewFree signatures (Ty.memref element) := by
  simp [ViewFree, Ty.memref, holdsView, mentionsView]

theorem applyMany {head : Ty} {arguments : List Ty} (free : ViewFree signatures (Ty.applyMany head arguments)) :
    ViewFree signatures head ∧ ∀ argument ∈ arguments, ViewFree signatures argument := by
  induction arguments generalizing head with
  | nil => exact ⟨free, by simp⟩
  | cons argument rest ih =>
    obtain ⟨headFree, restFree⟩ := ih (head := .application head argument) free
    obtain ⟨headFree, argumentFree⟩ := headFree.application
    refine ⟨headFree, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with same | inRest
    · exact same ▸ argumentFree
    · exact restFree other inRest

private theorem lookup_member {substitution : ParameterSubstitution} {parameter : TypeParameterId}
    {replacement : Ty} (found : substitution.lookup? parameter = some replacement) :
    ∃ entry ∈ substitution, entry.2 = replacement := by
  induction substitution with
  | nil => simp [ParameterSubstitution.lookup?] at found
  | cons entry rest ih =>
    obtain ⟨candidate, value⟩ := entry
    by_cases same : candidate = parameter
    · simp only [ParameterSubstitution.lookup?, same, ↓reduceIte, Option.some.injEq] at found
      exact ⟨(candidate, value), List.mem_cons_self .., found⟩
    · simp only [ParameterSubstitution.lookup?, same, ↓reduceIte] at found
      obtain ⟨other, member, same⟩ := ih found
      exact ⟨other, List.mem_cons_of_mem _ member, same⟩

/-- A substitution of view-free types keeps a view-free type view-free. -/
theorem apply {substitution : ParameterSubstitution}
    (replacements : ∀ entry ∈ substitution, ViewFree signatures entry.2) :
    ∀ {type : Ty}, ViewFree signatures type → ViewFree signatures (substitution.apply type)
  | .variable _, free => free
  | .parameter parameter, free => by
    show ViewFree signatures ((substitution.lookup? parameter).getD (.parameter parameter))
    cases found : substitution.lookup? parameter with
    | none => exact free
    | some replacement =>
      obtain ⟨entry, member, same⟩ := lookup_member found
      exact same ▸ replacements entry member
  | .constructor _, free => free
  | .application function argument, free => by
    obtain ⟨functionFree, argumentFree⟩ := free.application
    show ViewFree signatures (.application (substitution.apply function) (substitution.apply argument))
    simp [ViewFree, holdsView_application, apply replacements functionFree, apply replacements argumentFree]
  | .function parameter result, free => by
    obtain ⟨parameterFree, resultFree⟩ := free.function
    show ViewFree signatures (.function (substitution.apply parameter) (substitution.apply result))
    simp [ViewFree, holdsView_function, apply replacements parameterFree, apply replacements resultFree]
  | .product left right, free => by
    obtain ⟨leftFree, rightFree⟩ := free.product
    show ViewFree signatures (.product (substitution.apply left) (substitution.apply right))
    simp [ViewFree, holdsView_product, apply replacements leftFree, apply replacements rightFree]
  | .mapping key value, free => by
    obtain ⟨keyFree, valueFree⟩ := free.mapping
    show ViewFree signatures (.mapping (substitution.apply key) (substitution.apply value))
    simp [ViewFree, holdsView_mapping, apply replacements keyFree, apply replacements valueFree]
  | .proxy inner, free => apply replacements (type := inner) free
  | .comptime inner, free => apply replacements (type := inner) free
  | .error, free => free

/-- The fixpoint, once reached, holds every declaration whose payloads hold a view. -/
private theorem viewDeclarations_closed :
    ∀ {fuel : Nat} {start found : List Resolved.DeclarationId},
      viewDeclarations signatures fuel start = some found →
      ∀ data ∈ signatures.dataTypes, found.contains data.id = false → holdsInPayloads found data = false
  | 0, _, _, reached => by simp [viewDeclarations] at reached
  | fuel + 1, start, found, reached => by
    unfold viewDeclarations at reached
    simp only at reached
    split at reached
    · rename_i empty
      cases reached
      intro data member absent
      have noneNext := List.isEmpty_iff.mp empty
      have filtered := List.map_eq_nil_iff.mp noneNext
      have excluded := List.filter_eq_nil_iff.mp filtered data member
      cases held : holdsInPayloads start data with
      | false => rfl
      | true =>
        simp [held] at excluded
        simp [excluded] at absent
    · exact viewDeclarations_closed reached

/-- A view-free enum's declared payloads are view-free. -/
theorem payload {declaration : Resolved.DeclarationId} {data : ProgramDataSignature}
    (free : ViewFree signatures (.constructor (.declaration declaration)))
    (member : data ∈ signatures.dataTypes) (same : data.id = declaration)
    {payload : Ty} (payloadMember : payload ∈ payloadTypes data) : ViewFree signatures payload := by
  cases reached : viewDeclarations signatures (signatures.dataTypes.length + 1) [] with
  | none =>
    have held : heldBy signatures [declaration] = true := by unfold heldBy; rw [reached]
    simp [ViewFree, holdsView, mentionsView, declarations, held] at free
  | some found =>
    have heldEq : ∀ named, heldBy signatures named = named.any fun other => found.contains other := by
      intro named; unfold heldBy; rw [reached]
    have absent : found.contains data.id = false := by
      have named := free
      simp only [ViewFree, holdsView, mentionsView, declarations, heldEq, Bool.false_or] at named
      simpa [same] using named
    have closed := viewDeclarations_closed reached data member absent
    have excluded := List.any_eq_false.mp closed payload payloadMember
    simp only [ViewFree, holdsView, heldEq]
    simpa using excluded

/-- Each type that the check passes is view-free. -/
theorem of_all {types : List Ty} (passed : (types.all fun type => !holdsView signatures type) = true) :
    ∀ type ∈ types, ViewFree signatures type := by
  intro type member
  simpa using List.all_eq_true.mp passed type member

end ViewFree

end Solcore.Frontend.SourceCoreRootTypes
