import Solcore.Workspace.Path

set_option autoImplicit false

namespace Solcore.Workspace

/-- A structural error discovered while validating a caller workspace. -/
inductive ValidationError where
  | invalidEntryPath (rawEntry : String)
  | invalidExternalLibraryName (rawName : String)
  | duplicateExternalLibraryName (rawName : String)
  | invalidMainSourcePath (rawPath : String)
  | invalidExternalSourcePath (rawLibraryName : String) (rawPath : String)
  | duplicateMainSourcePath (path : CanonicalSourcePath)
  | duplicateExternalSourcePath
      (libraryName : ExternalLibraryName)
      (path : CanonicalSourcePath)
  | missingEntry (path : CanonicalSourcePath)
  deriving Repr, DecidableEq

namespace ValidationError

/-- The constructor precedence fixed by ADR-0014. -/
def rank : ValidationError → Nat
  | .invalidEntryPath _ => 0
  | .invalidExternalLibraryName _ => 1
  | .duplicateExternalLibraryName _ => 2
  | .invalidMainSourcePath _ => 3
  | .invalidExternalSourcePath _ _ => 4
  | .duplicateMainSourcePath _ => 5
  | .duplicateExternalSourcePath _ _ => 6
  | .missingEntry _ => 7

/-- Canonical diagnostic arguments in their constructor-local comparison order. -/
def arguments : ValidationError → List String
  | .invalidEntryPath rawEntry => [rawEntry]
  | .invalidExternalLibraryName rawName => [rawName]
  | .duplicateExternalLibraryName rawName => [rawName]
  | .invalidMainSourcePath rawPath => [rawPath]
  | .invalidExternalSourcePath rawLibraryName rawPath => [rawLibraryName, rawPath]
  | .duplicateMainSourcePath path => [path.render]
  | .duplicateExternalSourcePath libraryName path => [libraryName.render, path.render]
  | .missingEntry path => [path.render]

private def orderKey (error : ValidationError) : Nat × List String :=
  (error.rank, error.arguments)

@[simp] private theorem canonicalSourcePath_render_eq_iff
    {left right : CanonicalSourcePath} :
    left.render = right.render ↔ left = right :=
  ⟨fun equality => CanonicalSourcePath.render_injective equality,
    congrArg CanonicalSourcePath.render⟩

@[simp] private theorem externalLibraryName_render_eq_iff
    {left right : ExternalLibraryName} :
    left.render = right.render ↔ left = right :=
  ⟨fun equality => ExternalLibraryName.render_injective equality,
    congrArg ExternalLibraryName.render⟩

private theorem orderKey_injective : Function.Injective orderKey := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all [orderKey, rank, arguments]

private def compareRank (left right : ValidationError) : Ordering :=
  compare left.rank right.rank

private def compareArguments (left right : ValidationError) : Ordering :=
  List.compareLex compareUnicodeScalar left.arguments right.arguments

/--
Compares structural errors by constructor rank and then lexicographically by
their Unicode-scalar argument spellings.
-/
def compare (left right : ValidationError) : Ordering :=
  compareLex compareRank compareArguments left right

private instance : Std.TransCmp compareRank where
  eq_swap := by
    intro left right
    simpa only [compareRank] using
      (Std.OrientedOrd.eq_swap (a := left.rank) (b := right.rank))
  isLE_trans := by
    intro left second right leftSecond secondRight
    simpa only [compareRank] using
      (Std.TransOrd.isLE_trans leftSecond secondRight)

private instance : Std.TransCmp compareArguments where
  eq_swap := by
    intro left right
    exact Std.OrientedCmp.eq_swap
      (cmp := List.compareLex compareUnicodeScalar)
      (a := left.arguments)
      (b := right.arguments)
  isLE_trans := by
    intro left second right leftSecond secondRight
    exact Std.TransCmp.isLE_trans
      (cmp := List.compareLex compareUnicodeScalar)
      leftSecond
      secondRight

instance : Std.TransCmp ValidationError.compare := by
  unfold ValidationError.compare
  infer_instance

instance : Std.LawfulEqCmp ValidationError.compare where
  eq_of_compare := by
    intro left right equality
    have components := compareLex_eq_eq.mp equality
    apply orderKey_injective
    apply Prod.ext
    · exact Std.LawfulEqOrd.eq_of_compare components.1
    · exact Std.LawfulEqCmp.eq_of_compare
        (cmp := List.compareLex compareUnicodeScalar)
        components.2

instance : Ord ValidationError where
  compare := ValidationError.compare

instance : Std.OrientedOrd ValidationError := by
  change Std.OrientedCmp ValidationError.compare
  infer_instance

instance : Std.TransOrd ValidationError := by
  change Std.TransCmp ValidationError.compare
  infer_instance

instance : Std.LawfulEqOrd ValidationError := by
  change Std.LawfulEqCmp ValidationError.compare
  infer_instance

/-- Equal comparison coincides exactly with structural error equality. -/
@[simp] theorem compare_eq_iff_eq {left right : ValidationError} :
    ValidationError.compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

/-- Boolean equality agrees with the canonical comparator. -/
instance : BEq ValidationError where
  beq left right := (ValidationError.compare left right).isEq

instance : LawfulBEq ValidationError where
  rfl {error} := by
    change (ValidationError.compare error error).isEq = true
    rw [Std.ReflCmp.compare_self
      (cmp := ValidationError.compare)
      (a := error)]
    rfl
  eq_of_beq {left right} equality := by
    apply compare_eq_iff_eq.mp
    change (ValidationError.compare left right).isEq = true at equality
    exact Ordering.isEq_iff_eq_eq.mp equality

/-- Comparing an error with itself yields equality. -/
@[simp] theorem compare_self (error : ValidationError) :
    ValidationError.compare error error = .eq :=
  Std.ReflCmp.compare_self

/-- Reversing comparator arguments swaps the comparison result. -/
theorem compare_swap (left right : ValidationError) :
    ValidationError.compare left right =
      (ValidationError.compare right left).swap :=
  Std.OrientedCmp.eq_swap

/-- The non-strict comparison result is transitive. -/
theorem compare_isLE_trans (first second third : ValidationError) :
    (ValidationError.compare first second).isLE →
    (ValidationError.compare second third).isLE →
    (ValidationError.compare first third).isLE :=
  Std.TransCmp.isLE_trans

/-- Strict comparison is transitive. -/
theorem compare_lt_trans {first second third : ValidationError}
    (firstSecond : ValidationError.compare first second = .lt)
    (secondThird : ValidationError.compare second third = .lt) :
    ValidationError.compare first third = .lt :=
  Std.TransCmp.lt_trans firstSecond secondThird

/-- Boolean non-strict order used by canonical list sorting. -/
def le (left right : ValidationError) : Bool :=
  (ValidationError.compare left right).isLE

/-- Boolean strict order induced by the canonical comparator. -/
def lt (left right : ValidationError) : Bool :=
  (ValidationError.compare left right).isLT

/-- Canonical non-strict order is reflexive. -/
@[simp] theorem le_refl (error : ValidationError) : le error error := by
  simp [le]

/-- Canonical non-strict order is transitive. -/
theorem le_trans (first second third : ValidationError) :
    le first second → le second third → le first third := by
  simpa only [le] using compare_isLE_trans first second third

/-- Canonical non-strict order compares every pair. -/
theorem le_total (left right : ValidationError) : le left right || le right left := by
  cases comparison : ValidationError.compare left right with
  | lt => simp [le, comparison]
  | eq => simp [le, comparison]
  | gt =>
      have reverse : ValidationError.compare right left = .lt :=
        Std.OrientedCmp.lt_of_gt comparison
      simp [le, comparison, reverse]

/-- Mutual non-strict comparison implies equality. -/
theorem le_antisymm {left right : ValidationError}
    (leftRight : le left right)
    (rightLeft : le right left) :
    left = right := by
  apply compare_eq_iff_eq.mp
  exact Std.OrientedCmp.isLE_antisymm leftRight rightLeft

/-- Canonical strict order is irreflexive. -/
@[simp] theorem lt_irrefl (error : ValidationError) : ¬lt error error := by
  simp [lt]

/-- Canonical strict order is transitive. -/
theorem lt_trans {first second third : ValidationError}
    (firstSecond : lt first second)
    (secondThird : lt second third) :
    lt first third := by
  rw [lt, Ordering.isLT_iff_eq_lt] at firstSecond secondThird ⊢
  exact compare_lt_trans firstSecond secondThird

end ValidationError

end Solcore.Workspace
