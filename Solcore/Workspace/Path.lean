import Std

set_option autoImplicit false

namespace Solcore.Workspace

private def isAsciiLower (character : Char) : Bool :=
  'a' <= character && character <= 'z'

private def isAsciiUpper (character : Char) : Bool :=
  'A' <= character && character <= 'Z'

private def isAsciiLetter (character : Char) : Bool :=
  isAsciiLower character || isAsciiUpper character

private def isAsciiDigit (character : Char) : Bool :=
  '0' <= character && character <= '9'

private def isSegmentTailCharacter (character : Char) : Bool :=
  isAsciiLetter character || isAsciiDigit character || character == '_'

/-- The executable ASCII grammar predicate for one logical path segment. -/
def pathSegmentTextValid (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest =>
      isAsciiLetter first && rest.all isSegmentTailCharacter

/-- One canonical ASCII component of a logical workspace path. -/
structure PathSegment where
  text : String
  valid : pathSegmentTextValid text = true
  deriving Repr, DecidableEq

namespace PathSegment

instance : BEq PathSegment :=
  ⟨fun left right => left.text == right.text⟩

/-- Parse one canonical ASCII path segment. -/
def parse (text : String) : Option PathSegment :=
  if valid : pathSegmentTextValid text = true then
    some { text, valid }
  else
    none

/-- Render a segment without normalization. -/
def render (segment : PathSegment) : String :=
  segment.text

@[simp] theorem parse_render (segment : PathSegment) :
    parse segment.render = some segment := by
  cases segment with
  | mk text valid => simp [parse, render, valid]

theorem text_eq_of_parse_eq_some {text : String} {segment : PathSegment}
    (parsed : parse text = some segment) :
    segment.text = text := by
  unfold parse at parsed
  split at parsed
  · exact congrArg PathSegment.text (Option.some.inj parsed)
      |>.symm
  · simp at parsed

theorem render_injective : Function.Injective render := by
  intro left right equality
  cases left
  cases right
  simp only [render] at equality
  simp_all

private theorem character_valid (segment : PathSegment) {character : Char}
    (member : character ∈ segment.text.toList) :
    isSegmentTailCharacter character = true := by
  rcases segment with ⟨text, valid⟩
  cases equation : text.toList with
  | nil => simp [pathSegmentTextValid, equation] at valid
  | cons first rest =>
      simp only [pathSegmentTextValid, equation, Bool.and_eq_true,
        List.all_eq_true] at valid
      rw [equation] at member
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst character
        simp [isSegmentTailCharacter, valid.1]
      · exact valid.2 character member

theorem slash_not_mem (segment : PathSegment) :
    '/' ∉ segment.text.toList := by
  intro member
  have valid := character_valid segment member
  simp [isSegmentTailCharacter, isAsciiLetter, isAsciiLower, isAsciiUpper,
    isAsciiDigit] at valid

end PathSegment

/-- A nonempty sequence of canonical logical path segments. -/
structure ModulePath where
  segments : List PathSegment
  nonempty : segments ≠ []
  deriving Repr, DecidableEq

namespace ModulePath

instance : BEq ModulePath :=
  ⟨fun left right => left.segments == right.segments⟩

private def charLists (path : ModulePath) : List (List Char) :=
  path.segments.map fun segment => segment.text.toList

private def renderChars (path : ModulePath) : List Char :=
  ['/'].intercalate path.charLists

private theorem charLists_injective : Function.Injective
    (fun segments : List PathSegment =>
      segments.map fun segment => segment.text.toList) := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right with
      | nil => rfl
      | cons head tail => simp at equality
  | cons head tail inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp at equality
      | cons otherHead otherTail =>
          simp only [List.map_cons, List.cons.injEq] at equality
          have headEqual : head = otherHead := by
            apply PathSegment.render_injective
            apply String.toList_inj.mp
            exact equality.1
          have tailEqual : tail = otherTail :=
            inductionHypothesis equality.2
          simp [headEqual, tailEqual]

/-- Render a module path with `/` separators. -/
def render (path : ModulePath) : String :=
  String.ofList path.renderChars

@[simp] private theorem render_toList (path : ModulePath) :
    path.render.toList = path.renderChars := by
  simp [render]

theorem render_injective : Function.Injective render := by
  intro left right equality
  have charsEqual : left.renderChars = right.renderChars := by
    simpa only [← render_toList] using congrArg String.toList equality
  have leftSplit : left.renderChars.splitOn '/' = left.charLists := by
    apply List.splitOn_intercalate
    · intro characters member
      simp only [charLists, List.mem_map] at member
      rcases member with ⟨segment, _, rfl⟩
      exact segment.slash_not_mem
    · simpa [charLists] using left.nonempty
  have rightSplit : right.renderChars.splitOn '/' = right.charLists := by
    apply List.splitOn_intercalate
    · intro characters member
      simp only [charLists, List.mem_map] at member
      rcases member with ⟨segment, _, rfl⟩
      exact segment.slash_not_mem
    · simpa [charLists] using right.nonempty
  have listsEqual : left.charLists = right.charLists := by
    rw [← leftSplit, ← rightSplit, charsEqual]
  have segmentsEqual : left.segments = right.segments := by
    exact charLists_injective listsEqual
  cases left
  cases right
  simp_all

end ModulePath

/-- A canonical source path represented by its module path. -/
structure CanonicalSourcePath where
  modulePath : ModulePath
  deriving Repr, DecidableEq

namespace CanonicalSourcePath

instance : BEq CanonicalSourcePath :=
  ⟨fun left right => left.modulePath == right.modulePath⟩

private def suffix : List Char := ['.', 's', 'o', 'l', 'c']

private def renderChars (path : CanonicalSourcePath) : List Char :=
  path.modulePath.render.toList ++ suffix

/-- Render a canonical source path with one lowercase `.solc` suffix. -/
def render (path : CanonicalSourcePath) : String :=
  String.ofList path.renderChars

@[simp] private theorem render_toList (path : CanonicalSourcePath) :
    path.render.toList = path.renderChars := by
  simp [render]

end CanonicalSourcePath

private def parseSegmentLists :
    List (List Char) -> Option (List PathSegment)
  | [] => some []
  | characters :: rest =>
      match PathSegment.parse (String.ofList characters),
          parseSegmentLists rest with
      | some segment, some segments => some (segment :: segments)
      | _, _ => none

@[simp] private theorem parseSegmentLists_render
    (segments : List PathSegment) :
    parseSegmentLists
        (segments.map fun segment => segment.text.toList) =
      some segments := by
  induction segments with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, parseSegmentLists]
      rw [String.ofList_toList]
      rw [show PathSegment.parse head.text = some head by
        simpa [PathSegment.render] using PathSegment.parse_render head]
      rw [inductionHypothesis]

private theorem parseSegmentLists_sound
    {raw : List (List Char)} {segments : List PathSegment}
    (parsed : parseSegmentLists raw = some segments) :
    raw = segments.map fun segment => segment.text.toList := by
  induction raw generalizing segments with
  | nil =>
      simp [parseSegmentLists] at parsed
      subst segments
      rfl
  | cons characters rest inductionHypothesis =>
      simp only [parseSegmentLists] at parsed
      cases headResult : PathSegment.parse (String.ofList characters) with
      | none => simp [headResult] at parsed
      | some head =>
          cases tailResult : parseSegmentLists rest with
          | none => simp [headResult, tailResult] at parsed
          | some tail =>
              simp [headResult, tailResult] at parsed
              subst segments
              have headText := PathSegment.text_eq_of_parse_eq_some headResult
              have headCharacters : characters = head.text.toList := by
                rw [headText, String.toList_ofList]
              have tailCharacters := inductionHypothesis tailResult
              simp [headCharacters, tailCharacters]

private def parseModuleChars (characters : List Char) : Option ModulePath :=
  match parseSegmentLists (characters.splitOn '/') with
  | none => none
  | some segments =>
      if nonempty : segments ≠ [] then
        some { segments, nonempty }
      else
        none

@[simp] private theorem parseModuleChars_render (path : ModulePath) :
    parseModuleChars path.render.toList = some path := by
  rw [ModulePath.render_toList]
  have split : path.renderChars.splitOn '/' = path.charLists := by
    apply List.splitOn_intercalate
    · intro characters member
      simp only [ModulePath.charLists, List.mem_map] at member
      rcases member with ⟨segment, _, rfl⟩
      exact segment.slash_not_mem
    · simpa [ModulePath.charLists] using path.nonempty
  unfold parseModuleChars
  rw [split]
  change (match parseSegmentLists
      (path.segments.map fun segment => segment.text.toList) with
    | none => none
    | some segments =>
        if nonempty : segments ≠ [] then
          some { segments, nonempty }
        else none) = some path
  rw [parseSegmentLists_render]
  simp [path.nonempty]

private theorem parseModuleChars_sound
    {characters : List Char} {path : ModulePath}
    (parsed : parseModuleChars characters = some path) :
    characters = path.render.toList := by
  unfold parseModuleChars at parsed
  split at parsed
  · simp at parsed
  · rename_i segments parsedSegments
    split at parsed
    · rename_i nonempty
      have pathEqual :
          ({ segments, nonempty } : ModulePath) = path :=
        Option.some.inj parsed
      have partsEqual := parseSegmentLists_sound parsedSegments
      rw [← List.intercalate_splitOn '/' (xs := characters)]
      rw [partsEqual]
      subst path
      rw [ModulePath.render_toList]
      rfl
    · simp at parsed

namespace CanonicalSourcePath

private def parseChars (characters : List Char) : Option CanonicalSourcePath :=
  let stem := characters.take (characters.length - suffix.length)
  match parseModuleChars stem with
  | none => none
  | some modulePath =>
      let path : CanonicalSourcePath := { modulePath }
      if path.renderChars == characters then some path else none

/-- Parse an exact canonical source path. -/
def parse (text : String) : Option CanonicalSourcePath :=
  parseChars text.toList

@[simp] theorem parse_render (path : CanonicalSourcePath) :
    parse path.render = some path := by
  cases path with
  | mk modulePath =>
      unfold parse parseChars
      rw [render_toList]
      simp only [renderChars]
      have takeStem :
          (modulePath.render.toList ++ suffix).take
              ((modulePath.render.toList ++ suffix).length - suffix.length) =
            modulePath.render.toList := by
        simp [suffix]
      rw [takeStem, parseModuleChars_render]
      simp

theorem text_eq_render_of_parse_eq_some
    {text : String} {path : CanonicalSourcePath}
    (parsed : parse text = some path) :
    text = path.render := by
  unfold parse parseChars at parsed
  dsimp only at parsed
  cases parsedModule : parseModuleChars
      (text.toList.take (text.toList.length - suffix.length)) with
  | none => simp [parsedModule] at parsed
  | some modulePath =>
    simp only [parsedModule] at parsed
    split at parsed
    · rename_i equal
      have pathEqual : ({ modulePath } : CanonicalSourcePath) = path :=
        Option.some.inj parsed
      have charsEqual : ({ modulePath } : CanonicalSourcePath).renderChars =
          text.toList := by
        exact beq_iff_eq.mp equal
      subst path
      apply String.toList_inj.mp
      simpa using charsEqual.symm
    · simp at parsed

theorem render_injective : Function.Injective render := by
  intro left right equality
  have parsedEqual := congrArg parse equality
  simpa using parsedEqual

theorem parse_eq_some_iff {text : String} {path : CanonicalSourcePath} :
    parse text = some path <-> text = path.render := by
  constructor
  · exact text_eq_render_of_parse_eq_some
  · intro equality
    subst text
    exact parse_render path

end CanonicalSourcePath

/-- A canonical name for one external source library. -/
structure ExternalLibraryName where
  segment : PathSegment
  deriving Repr, DecidableEq

namespace ExternalLibraryName

instance : BEq ExternalLibraryName :=
  ⟨fun left right => left.segment == right.segment⟩

/-- Render an external library name as its single segment. -/
def render (name : ExternalLibraryName) : String :=
  name.segment.render

/-- Parse one canonical external library name. -/
def parse (text : String) : Option ExternalLibraryName :=
  (PathSegment.parse text).map fun segment => { segment }

@[simp] theorem parse_render (name : ExternalLibraryName) :
    parse name.render = some name := by
  cases name with
  | mk segment => simp [parse, render]

theorem render_injective : Function.Injective render := by
  intro left right equality
  cases left with
  | mk left =>
      cases right with
      | mk right =>
          simp only [render] at equality
          exact congrArg ExternalLibraryName.mk
            (PathSegment.render_injective equality)

theorem text_eq_render_of_parse_eq_some
    {text : String} {name : ExternalLibraryName}
    (parsed : parse text = some name) :
    text = name.render := by
  unfold parse at parsed
  cases parsedSegment : PathSegment.parse text with
  | none => simp [parsedSegment] at parsed
  | some segment =>
      simp [parsedSegment] at parsed
      subst name
      exact (PathSegment.text_eq_of_parse_eq_some parsedSegment).symm

theorem parse_eq_some_iff {text : String} {name : ExternalLibraryName} :
    parse text = some name ↔ text = name.render := by
  constructor
  · exact text_eq_render_of_parse_eq_some
  · intro equality
    subst text
    exact parse_render name

end ExternalLibraryName

/-- Compare decoded strings lexicographically by Unicode scalar value. -/
def compareUnicodeScalar (left right : String) : Ordering :=
  compare left.toList right.toList

instance compareUnicodeScalarOriented :
    Std.OrientedCmp compareUnicodeScalar where
  eq_swap := by
    intro left right
    simpa [compareUnicodeScalar] using
      (Std.OrientedCmp.eq_swap
        (cmp := (compare : List Char -> List Char -> Ordering))
        (a := left.toList) (b := right.toList))

instance compareUnicodeScalarTransitive :
    Std.TransCmp compareUnicodeScalar where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro left middle right leftMiddle middleRight
    exact Std.TransCmp.isLE_trans
      (cmp := (compare : List Char -> List Char -> Ordering))
      leftMiddle middleRight

instance compareUnicodeScalarLawfulEq :
    Std.LawfulEqCmp compareUnicodeScalar where
  compare_self := Std.ReflCmp.compare_self
  eq_of_compare := by
    intro left right equality
    apply String.toList_inj.mp
    exact Std.LawfulEqCmp.eq_of_compare
      (cmp := (compare : List Char -> List Char -> Ordering)) equality

@[simp] theorem compareUnicodeScalar_eq_iff_eq {left right : String} :
    compareUnicodeScalar left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

private theorem compareByUnicodeScalar_oriented {α : Type}
    (key : α -> String) :
    Std.OrientedCmp (fun left right => compareUnicodeScalar (key left) (key right)) where
  eq_swap := Std.OrientedCmp.eq_swap

private theorem compareByUnicodeScalar_transitive {α : Type}
    (key : α -> String) :
    Std.TransCmp (fun left right => compareUnicodeScalar (key left) (key right)) where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans := Std.TransCmp.isLE_trans

private theorem compareByUnicodeScalar_lawfulEq {α : Type}
    (key : α -> String) (injective : Function.Injective key) :
    Std.LawfulEqCmp
      (fun left right => compareUnicodeScalar (key left) (key right)) where
  compare_self := Std.ReflCmp.compare_self
  eq_of_compare equality :=
    injective (compareUnicodeScalar_eq_iff_eq.mp equality)

private theorem comparisonLeRefl {α : Type} (cmp : α -> α -> Ordering)
    [Std.ReflCmp cmp] (value : α) :
    (cmp value value).isLE = true :=
  Std.ReflCmp.isLE_rfl

private theorem comparisonLeTrans {α : Type} (cmp : α -> α -> Ordering)
    [Std.TransCmp cmp] {first second third : α}
    (firstSecond : (cmp first second).isLE = true)
    (secondThird : (cmp second third).isLE = true) :
    (cmp first third).isLE = true :=
  Std.TransCmp.isLE_trans firstSecond secondThird

private theorem comparisonLeTotal {α : Type} (cmp : α -> α -> Ordering)
    [Std.OrientedCmp cmp] (left right : α) :
    (cmp left right).isLE = true ∨ (cmp right left).isLE = true := by
  rw [Std.OrientedCmp.eq_swap (cmp := cmp)]
  cases cmp right left <;> simp

private theorem comparisonLeAntisymm {α : Type} (cmp : α -> α -> Ordering)
    [Std.OrientedCmp cmp] [Std.LawfulEqCmp cmp] {left right : α}
    (leftRight : (cmp left right).isLE = true)
    (rightLeft : (cmp right left).isLE = true) :
    left = right := by
  apply Std.LawfulEqCmp.eq_of_compare (cmp := cmp)
  exact Std.OrientedCmp.isLE_antisymm leftRight rightLeft

namespace PathSegment

/-- Compare segments by their rendered ASCII text. -/
def compare (left right : PathSegment) : Ordering :=
  compareUnicodeScalar left.render right.render

instance : Ord PathSegment := ⟨compare⟩
instance : Std.OrientedCmp compare := compareByUnicodeScalar_oriented render
instance : Std.TransCmp compare := compareByUnicodeScalar_transitive render
instance : Std.LawfulEqCmp compare :=
  compareByUnicodeScalar_lawfulEq render render_injective
instance : Std.OrientedOrd PathSegment := by
  change Std.OrientedCmp compare
  infer_instance
instance : Std.TransOrd PathSegment := by
  change Std.TransCmp compare
  infer_instance
instance : Std.LawfulEqOrd PathSegment := by
  change Std.LawfulEqCmp compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : PathSegment} :
    compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

def le (left right : PathSegment) : Bool :=
  (compare left right).isLE

instance : LE PathSegment := ⟨fun left right => le left right = true⟩

theorem le_refl (value : PathSegment) : le value value = true :=
  comparisonLeRefl compare value

theorem le_trans {first second third : PathSegment} :
    le first second = true -> le second third = true -> le first third = true :=
  comparisonLeTrans compare

theorem le_total (left right : PathSegment) :
    le left right = true ∨ le right left = true :=
  comparisonLeTotal compare left right

theorem le_antisymm {left right : PathSegment} :
    le left right = true -> le right left = true -> left = right :=
  comparisonLeAntisymm compare

end PathSegment

namespace ModulePath

/-- Compare module paths by their canonical rendering. -/
def compare (left right : ModulePath) : Ordering :=
  compareUnicodeScalar left.render right.render

instance : Ord ModulePath := ⟨compare⟩
instance : Std.OrientedCmp compare := compareByUnicodeScalar_oriented render
instance : Std.TransCmp compare := compareByUnicodeScalar_transitive render
instance : Std.LawfulEqCmp compare :=
  compareByUnicodeScalar_lawfulEq render render_injective
instance : Std.OrientedOrd ModulePath := by
  change Std.OrientedCmp compare
  infer_instance
instance : Std.TransOrd ModulePath := by
  change Std.TransCmp compare
  infer_instance
instance : Std.LawfulEqOrd ModulePath := by
  change Std.LawfulEqCmp compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : ModulePath} :
    compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

def le (left right : ModulePath) : Bool :=
  (compare left right).isLE

instance : LE ModulePath := ⟨fun left right => le left right = true⟩

theorem le_refl (value : ModulePath) : le value value = true :=
  comparisonLeRefl compare value

theorem le_trans {first second third : ModulePath} :
    le first second = true -> le second third = true -> le first third = true :=
  comparisonLeTrans compare

theorem le_total (left right : ModulePath) :
    le left right = true ∨ le right left = true :=
  comparisonLeTotal compare left right

theorem le_antisymm {left right : ModulePath} :
    le left right = true -> le right left = true -> left = right :=
  comparisonLeAntisymm compare

end ModulePath

namespace CanonicalSourcePath

/-- Compare source paths by their canonical ASCII rendering. -/
def compare (left right : CanonicalSourcePath) : Ordering :=
  compareUnicodeScalar left.render right.render

instance : Ord CanonicalSourcePath := ⟨compare⟩
instance : Std.OrientedCmp compare := compareByUnicodeScalar_oriented render
instance : Std.TransCmp compare := compareByUnicodeScalar_transitive render
instance : Std.LawfulEqCmp compare :=
  compareByUnicodeScalar_lawfulEq render render_injective
instance : Std.OrientedOrd CanonicalSourcePath := by
  change Std.OrientedCmp compare
  infer_instance
instance : Std.TransOrd CanonicalSourcePath := by
  change Std.TransCmp compare
  infer_instance
instance : Std.LawfulEqOrd CanonicalSourcePath := by
  change Std.LawfulEqCmp compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : CanonicalSourcePath} :
    compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

def le (left right : CanonicalSourcePath) : Bool :=
  (compare left right).isLE

instance : LE CanonicalSourcePath := ⟨fun left right => le left right = true⟩

theorem le_refl (value : CanonicalSourcePath) : le value value = true :=
  comparisonLeRefl compare value

theorem le_trans {first second third : CanonicalSourcePath} :
    le first second = true -> le second third = true -> le first third = true :=
  comparisonLeTrans compare

theorem le_total (left right : CanonicalSourcePath) :
    le left right = true ∨ le right left = true :=
  comparisonLeTotal compare left right

theorem le_antisymm {left right : CanonicalSourcePath} :
    le left right = true -> le right left = true -> left = right :=
  comparisonLeAntisymm compare

end CanonicalSourcePath

namespace ExternalLibraryName

/-- Compare external library names by their canonical ASCII rendering. -/
def compare (left right : ExternalLibraryName) : Ordering :=
  compareUnicodeScalar left.render right.render

instance : Ord ExternalLibraryName := ⟨compare⟩
instance : Std.OrientedCmp compare := compareByUnicodeScalar_oriented render
instance : Std.TransCmp compare := compareByUnicodeScalar_transitive render
instance : Std.LawfulEqCmp compare :=
  compareByUnicodeScalar_lawfulEq render render_injective
instance : Std.OrientedOrd ExternalLibraryName := by
  change Std.OrientedCmp compare
  infer_instance
instance : Std.TransOrd ExternalLibraryName := by
  change Std.TransCmp compare
  infer_instance
instance : Std.LawfulEqOrd ExternalLibraryName := by
  change Std.LawfulEqCmp compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : ExternalLibraryName} :
    compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

def le (left right : ExternalLibraryName) : Bool :=
  (compare left right).isLE

instance : LE ExternalLibraryName := ⟨fun left right => le left right = true⟩

theorem le_refl (value : ExternalLibraryName) : le value value = true :=
  comparisonLeRefl compare value

theorem le_trans {first second third : ExternalLibraryName} :
    le first second = true -> le second third = true -> le first third = true :=
  comparisonLeTrans compare

theorem le_total (left right : ExternalLibraryName) :
    le left right = true ∨ le right left = true :=
  comparisonLeTotal compare left right

theorem le_antisymm {left right : ExternalLibraryName} :
    le left right = true -> le right left = true -> left = right :=
  comparisonLeAntisymm compare

end ExternalLibraryName

/-- The declarative graph of canonical source-path rendering. -/
inductive CanonicalPathOf : String -> CanonicalSourcePath -> Prop where
  | rendered (path : CanonicalSourcePath) : CanonicalPathOf path.render path

namespace CanonicalPathOf

theorem iff_eq_render {text : String} {path : CanonicalSourcePath} :
    CanonicalPathOf text path ↔ text = path.render := by
  constructor
  · intro graph
    cases graph
    rfl
  · intro equality
    subst text
    exact .rendered path

theorem functional {text : String} {first second : CanonicalSourcePath}
    (firstGraph : CanonicalPathOf text first)
    (secondGraph : CanonicalPathOf text second) :
    first = second := by
  apply CanonicalSourcePath.render_injective
  exact (iff_eq_render.mp firstGraph).symm.trans
    (iff_eq_render.mp secondGraph)

end CanonicalPathOf

/-- The executable canonical source-path parser. -/
def parseCanonicalPath (text : String) : Option CanonicalSourcePath :=
  CanonicalSourcePath.parse text

theorem parseCanonicalPath_sound
    {text : String} {path : CanonicalSourcePath}
    (parsed : parseCanonicalPath text = some path) :
    CanonicalPathOf text path := by
  apply CanonicalPathOf.iff_eq_render.mpr
  exact CanonicalSourcePath.text_eq_render_of_parse_eq_some parsed

theorem parseCanonicalPath_complete
    {text : String} {path : CanonicalSourcePath}
    (graph : CanonicalPathOf text path) :
    parseCanonicalPath text = some path := by
  rw [CanonicalPathOf.iff_eq_render.mp graph]
  exact CanonicalSourcePath.parse_render path

/-- The declarative graph of canonical external-library-name rendering. -/
inductive ExternalLibraryNameOf : String -> ExternalLibraryName -> Prop where
  | rendered (name : ExternalLibraryName) :
      ExternalLibraryNameOf name.render name

namespace ExternalLibraryNameOf

theorem iff_eq_render {text : String} {name : ExternalLibraryName} :
    ExternalLibraryNameOf text name ↔ text = name.render := by
  constructor
  · intro graph
    cases graph
    rfl
  · intro equality
    subst text
    exact .rendered name

theorem functional {text : String} {first second : ExternalLibraryName}
    (firstGraph : ExternalLibraryNameOf text first)
    (secondGraph : ExternalLibraryNameOf text second) :
    first = second := by
  apply ExternalLibraryName.render_injective
  exact (iff_eq_render.mp firstGraph).symm.trans
    (iff_eq_render.mp secondGraph)

end ExternalLibraryNameOf

namespace ExternalLibraryName

theorem parse_sound {text : String} {name : ExternalLibraryName}
    (parsed : parse text = some name) :
    ExternalLibraryNameOf text name := by
  apply ExternalLibraryNameOf.iff_eq_render.mpr
  exact text_eq_render_of_parse_eq_some parsed

theorem parse_complete {text : String} {name : ExternalLibraryName}
    (graph : ExternalLibraryNameOf text name) :
    parse text = some name := by
  rw [ExternalLibraryNameOf.iff_eq_render.mp graph]
  exact parse_render name

end ExternalLibraryName

end Solcore.Workspace
