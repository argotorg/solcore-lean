import Solcore.Surface.Multi.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- A closed lexical diagnostic with its exact primary source span. -/
inductive LexicalDiagnostic where
  | invalidCharacter (span : SourceSpan) (character : Char)
  | unterminatedBlockComment (span : SourceSpan)
  | unterminatedString (span : SourceSpan)
  | invalidStringEscape (span : SourceSpan) (character : Option Char)
  | unterminatedAssemblyString (span : SourceSpan)
  | unterminatedAssemblyComment (span : SourceSpan)
  | unterminatedAssemblyBlock (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- The closed terminal classes reported at the complete parse frontier. -/
inductive Expected where
  | hardKeyword (keyword : HardKeyword)
  | contextualKeyword (keyword : ContextualKeyword)
  | pragmaName (kind : PragmaKind)
  | symbol (symbol : Symbol)
  | identifier
  | pathComponent
  | literal
  | assemblyBlock
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- The token class found at a failing parse cursor. -/
inductive Found where
  | token (kind : TokenKind)
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- The two nonassociative infix precedence levels. -/
inductive NonAssociativeLevel where
  | relational
  | equality
  deriving Repr, BEq, DecidableEq

/-- A closed parse diagnostic with its exact primary source span. -/
inductive ParseDiagnostic where
  | unexpected
      (span : SourceSpan)
      (found : Found)
      (expected : NonemptyList Expected)
  | repeatedNonAssociative
      (span : SourceSpan)
      (level : NonAssociativeLevel)
      (operator : Located InfixOperator)
  deriving Repr, BEq, DecidableEq

/-- The two loop-control statement kinds. -/
inductive ControlKind where
  | breakControl
  | continueControl
  deriving Repr, BEq, DecidableEq

/-- Declaration positions in which a modifier can be rejected. -/
inductive ModifierContext where
  | topLevelFunction
  | classMethod
  | instanceMethod
  | fallback
  | contractConstructor
  deriving Repr, BEq, DecidableEq

/-- Declaration positions in which a parameter type is required. -/
inductive ParameterContext where
  | topLevelFunction
  | contractFunction
  | classMethod
  | instanceMethod
  | contractConstructor
  deriving Repr, BEq, DecidableEq

/-- A closed structural diagnostic with its exact primary source span. -/
inductive StructuralDiagnostic where
  | emptyImportSelection (span : SourceSpan)
  | mixedImportWildcard (span : SourceSpan)
  | duplicateImportSourceName
      (span : SourceSpan)
      (identifier : Identifier)
  | duplicateImportLocalName
      (span : SourceSpan)
      (identifier : Identifier)
  | emptyHidingClause (span : SourceSpan)
  | duplicateHiddenName
      (span : SourceSpan)
      (identifier : Identifier)
  | emptyLocalExportList (span : SourceSpan)
  | emptyRemoteExportList (span : SourceSpan)
  | mixedExportWildcard (span : SourceSpan)
  | duplicateExportName
      (span : SourceSpan)
      (identifier : Identifier)
  | duplicateExportModuleReference
      (span : SourceSpan)
      (reference : ModuleReferenceShape)
  | duplicateExportConstructor
      (span : SourceSpan)
      (identifier : Identifier)
  | matchPatternArityMismatch
      (span : SourceSpan)
      (expected : Nat)
      (actual : Nat)
  | emptyGenericPragmaTargets (span : SourceSpan)
  | duplicatePragmaTarget
      (span : SourceSpan)
      (identifier : Identifier)
  | modifierNotAllowed
      (span : SourceSpan)
      (context : ModifierContext)
      (marker : SyntaxMarker)
  | fallbackHasParameters (span : SourceSpan) (count : Nat)
  | fallbackHasNonUnitReturn (span : SourceSpan)
  | requiredParameterTypeMissing
      (span : SourceSpan)
      (context : ParameterContext)
  | controlOutsideLoop
      (span : SourceSpan)
      (control : ControlKind)
  deriving Repr, BEq, DecidableEq

/-- The first-failing parser phase and its structured diagnostic. -/
inductive SurfaceDiagnostic where
  | lexical (diagnostic : LexicalDiagnostic)
  | parse (diagnostic : ParseDiagnostic)
  | structural (diagnostic : StructuralDiagnostic)
  deriving Repr, BEq, DecidableEq

namespace LexicalDiagnostic

/-- The exact primary span of a lexical diagnostic. -/
def span : LexicalDiagnostic → SourceSpan
  | .invalidCharacter span _ => span
  | .unterminatedBlockComment span => span
  | .unterminatedString span => span
  | .invalidStringEscape span _ => span
  | .unterminatedAssemblyString span => span
  | .unterminatedAssemblyComment span => span
  | .unterminatedAssemblyBlock span => span

/-- The stable code assigned to a lexical diagnostic constructor. -/
def code : LexicalDiagnostic → String
  | .invalidCharacter _ _ => "MSL0001"
  | .unterminatedBlockComment _ => "MSL0002"
  | .unterminatedString _ => "MSL0003"
  | .invalidStringEscape _ _ => "MSL0004"
  | .unterminatedAssemblyString _ => "MSL0005"
  | .unterminatedAssemblyComment _ => "MSL0006"
  | .unterminatedAssemblyBlock _ => "MSL0007"

end LexicalDiagnostic

namespace ParseDiagnostic

/-- The exact primary span of a parse diagnostic. -/
def span : ParseDiagnostic → SourceSpan
  | .unexpected span _ _ => span
  | .repeatedNonAssociative span _ _ => span

/-- The stable code assigned to a parse diagnostic constructor. -/
def code : ParseDiagnostic → String
  | .unexpected _ _ _ => "MSP0001"
  | .repeatedNonAssociative _ _ _ => "MSP0002"

end ParseDiagnostic

namespace StructuralDiagnostic

/-- The exact primary span of a structural diagnostic. -/
def span : StructuralDiagnostic → SourceSpan
  | .emptyImportSelection span => span
  | .mixedImportWildcard span => span
  | .duplicateImportSourceName span _ => span
  | .duplicateImportLocalName span _ => span
  | .emptyHidingClause span => span
  | .duplicateHiddenName span _ => span
  | .emptyLocalExportList span => span
  | .emptyRemoteExportList span => span
  | .mixedExportWildcard span => span
  | .duplicateExportName span _ => span
  | .duplicateExportModuleReference span _ => span
  | .duplicateExportConstructor span _ => span
  | .matchPatternArityMismatch span _ _ => span
  | .emptyGenericPragmaTargets span => span
  | .duplicatePragmaTarget span _ => span
  | .modifierNotAllowed span _ _ => span
  | .fallbackHasParameters span _ => span
  | .fallbackHasNonUnitReturn span => span
  | .requiredParameterTypeMissing span _ => span
  | .controlOutsideLoop span _ => span

/-- The constructor precedence fixed by ADR-0015 diagnostic codes. -/
def rank : StructuralDiagnostic → Nat
  | .emptyImportSelection _ => 0
  | .mixedImportWildcard _ => 1
  | .duplicateImportSourceName _ _ => 2
  | .duplicateImportLocalName _ _ => 3
  | .emptyHidingClause _ => 4
  | .duplicateHiddenName _ _ => 5
  | .emptyLocalExportList _ => 6
  | .emptyRemoteExportList _ => 7
  | .mixedExportWildcard _ => 8
  | .duplicateExportName _ _ => 9
  | .duplicateExportModuleReference _ _ => 10
  | .duplicateExportConstructor _ _ => 11
  | .matchPatternArityMismatch _ _ _ => 12
  | .emptyGenericPragmaTargets _ => 13
  | .duplicatePragmaTarget _ _ => 14
  | .modifierNotAllowed _ _ _ => 15
  | .fallbackHasParameters _ _ => 16
  | .fallbackHasNonUnitReturn _ => 17
  | .requiredParameterTypeMissing _ _ => 18
  | .controlOutsideLoop _ _ => 19

private def nonemptyListToList {α : Type}
    (values : NonemptyList α) : List α :=
  values.head :: values.tail

private def moduleReferencePaths : ModuleReferenceShape → List PathSegment
  | .relative components => nonemptyListToList components
  | .libraryRoot tail => nonemptyListToList tail
  | .standard tail => tail
  | .external _ tail => nonemptyListToList tail

private def moduleReferenceLibraries :
    ModuleReferenceShape → List ExternalLibraryName
  | .external library _ => [library]
  | _ => []

private def moduleReferenceRank : ModuleReferenceShape → Nat
  | .relative _ => 0
  | .libraryRoot _ => 1
  | .standard _ => 2
  | .external _ _ => 3

private def modifierContextRank : ModifierContext → Nat
  | .topLevelFunction => 0
  | .classMethod => 1
  | .instanceMethod => 2
  | .fallback => 3
  | .contractConstructor => 4

private def syntaxMarkerRank : SyntaxMarker → Nat
  | .libraryRoot => 0
  | .standardRoot => 1
  | .externalSigil => 2
  | .wildcard => 3
  | .fallbackName => 4
  | .contractConstructorName => 5
  | .publicModifier => 6
  | .payableModifier => 7
  | .comptimeModifier => 8
  | .defaultModifier => 9

private def parameterContextRank : ParameterContext → Nat
  | .topLevelFunction => 0
  | .contractFunction => 1
  | .classMethod => 2
  | .instanceMethod => 3
  | .contractConstructor => 4

private def controlKindRank : ControlKind → Nat
  | .breakControl => 0
  | .continueControl => 1

/-- Numeric payload fields in their constructor-local comparison order. -/
private def payloadNats : StructuralDiagnostic → List Nat
  | .duplicateExportModuleReference _ reference => [moduleReferenceRank reference]
  | .matchPatternArityMismatch _ expected actual => [expected, actual]
  | .modifierNotAllowed _ context marker =>
      [modifierContextRank context, syntaxMarkerRank marker]
  | .fallbackHasParameters _ count => [count]
  | .requiredParameterTypeMissing _ context => [parameterContextRank context]
  | .controlOutsideLoop _ control => [controlKindRank control]
  | _ => []

/-- External-library payload fields in their constructor-local order. -/
private def payloadLibraries :
    StructuralDiagnostic → List ExternalLibraryName
  | .duplicateExportModuleReference _ reference =>
      moduleReferenceLibraries reference
  | _ => []

/-- Module-path payload fields in their constructor-local order. -/
private def payloadPaths : StructuralDiagnostic → List PathSegment
  | .duplicateExportModuleReference _ reference =>
      moduleReferencePaths reference
  | _ => []

/-- Identifier spellings in their constructor-local comparison order. -/
private def payloadTexts : StructuralDiagnostic → List String
  | .duplicateImportSourceName _ identifier
  | .duplicateImportLocalName _ identifier
  | .duplicateHiddenName _ identifier
  | .duplicateExportName _ identifier
  | .duplicateExportConstructor _ identifier
  | .duplicatePragmaTarget _ identifier => [identifier.text]
  | _ => []

private structure OrderKey where
  rank : Nat
  span : SourceSpan
  payloadNats : List Nat
  payloadLibraries : List ExternalLibraryName
  payloadPaths : List PathSegment
  payloadTexts : List String

private theorem OrderKey.eq_of_fields
    {left right : OrderKey}
    (rankEquality : left.rank = right.rank)
    (spanEquality : left.span = right.span)
    (natsEquality : left.payloadNats = right.payloadNats)
    (librariesEquality : left.payloadLibraries = right.payloadLibraries)
    (pathsEquality : left.payloadPaths = right.payloadPaths)
    (textsEquality : left.payloadTexts = right.payloadTexts) :
    left = right := by
  cases left
  cases right
  simp_all

private def orderKey (diagnostic : StructuralDiagnostic) : OrderKey := {
  rank := diagnostic.rank
  span := diagnostic.span
  payloadNats := payloadNats diagnostic
  payloadLibraries := payloadLibraries diagnostic
  payloadPaths := payloadPaths diagnostic
  payloadTexts := payloadTexts diagnostic
}

@[simp] private theorem identifier_text_eq_iff
    {left right : Identifier} :
    left.text = right.text ↔ left = right :=
  ⟨fun equality => Identifier.render_injective equality,
    fun equality => congrArg Identifier.render equality⟩

private theorem nonemptyListToList_injective {α : Type} :
    Function.Injective (nonemptyListToList (α := α)) := by
  intro left right equality
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [nonemptyListToList, List.cons.injEq] at equality
          cases equality.1
          cases equality.2
          rfl

@[simp] private theorem nonemptyListToList_eq_iff
    {α : Type} {left right : NonemptyList α} :
    nonemptyListToList left = nonemptyListToList right ↔ left = right :=
  ⟨fun equality => nonemptyListToList_injective equality,
    congrArg nonemptyListToList⟩

@[simp] private theorem modifierContextRank_eq_iff
    {left right : ModifierContext} :
    modifierContextRank left = modifierContextRank right ↔ left = right := by
  cases left <;> cases right <;> simp [modifierContextRank]

@[simp] private theorem syntaxMarkerRank_eq_iff
    {left right : SyntaxMarker} :
    syntaxMarkerRank left = syntaxMarkerRank right ↔ left = right := by
  cases left <;> cases right <;> simp [syntaxMarkerRank]

@[simp] private theorem parameterContextRank_eq_iff
    {left right : ParameterContext} :
    parameterContextRank left = parameterContextRank right ↔ left = right := by
  cases left <;> cases right <;> simp [parameterContextRank]

@[simp] private theorem controlKindRank_eq_iff
    {left right : ControlKind} :
    controlKindRank left = controlKindRank right ↔ left = right := by
  cases left <;> cases right <;> simp [controlKindRank]

private theorem moduleReferenceComponents_injective
    {left right : ModuleReferenceShape}
    (rankEquality : moduleReferenceRank left = moduleReferenceRank right)
    (librariesEquality :
      moduleReferenceLibraries left = moduleReferenceLibraries right)
    (pathsEquality : moduleReferencePaths left = moduleReferencePaths right) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [moduleReferenceRank, moduleReferenceLibraries,
      moduleReferencePaths]

@[simp] private theorem moduleReferenceComponents_eq_iff
    {left right : ModuleReferenceShape} :
    (moduleReferenceRank left = moduleReferenceRank right ∧
      moduleReferenceLibraries left = moduleReferenceLibraries right ∧
      moduleReferencePaths left = moduleReferencePaths right) ↔
      left = right := by
  constructor
  · rintro ⟨rankEquality, librariesEquality, pathsEquality⟩
    exact moduleReferenceComponents_injective
      rankEquality librariesEquality pathsEquality
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl⟩

private theorem orderKey_injective : Function.Injective orderKey := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all [orderKey, span, rank, payloadNats, payloadLibraries, payloadPaths,
      payloadTexts]

private theorem sourceSpan_eq_of_fields
    {left right : SourceSpan}
    (sourceEquality : left.source = right.source)
    (startEquality : left.startByte = right.startByte)
    (endEquality : left.endByte = right.endByte) :
    left = right := by
  cases left
  cases right
  simp_all

private def compareRank (left right : StructuralDiagnostic) : Ordering :=
  compareOn StructuralDiagnostic.rank left right

private def compareSource (left right : StructuralDiagnostic) : Ordering :=
  compareOn (fun diagnostic => diagnostic.span.source) left right

private def compareStartByte
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn (fun diagnostic => diagnostic.span.startByte) left right

private def compareEndByte
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn (fun diagnostic => diagnostic.span.endByte) left right

private def comparePayloadNats
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn payloadNats left right

private def comparePayloadLibraries
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn payloadLibraries left right

private def comparePayloadPaths
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn payloadPaths left right

private def comparePayloadTexts
    (left right : StructuralDiagnostic) : Ordering :=
  compareOn payloadTexts left right

/-- Compare constructor-local payloads in their displayed field order. -/
def comparePayload (left right : StructuralDiagnostic) : Ordering :=
  compareLex comparePayloadNats
    (compareLex comparePayloadLibraries
      (compareLex comparePayloadPaths comparePayloadTexts))
    left right

/--
Canonical structural-diagnostic order: code constructor, source identity,
primary byte range, then constructor-local payload fields.
-/
def compare (left right : StructuralDiagnostic) : Ordering :=
  compareLex compareRank
    (compareLex compareSource
      (compareLex compareStartByte
        (compareLex compareEndByte comparePayload)))
    left right

private instance : Std.TransCmp compareRank := by
  unfold compareRank
  infer_instance

private instance : Std.TransCmp compareSource := by
  unfold compareSource
  infer_instance

private instance : Std.TransCmp compareStartByte := by
  unfold compareStartByte
  infer_instance

private instance : Std.TransCmp compareEndByte := by
  unfold compareEndByte
  infer_instance

private instance : Std.TransCmp comparePayloadNats := by
  unfold comparePayloadNats
  infer_instance

private instance : Std.TransCmp comparePayloadLibraries := by
  unfold comparePayloadLibraries
  infer_instance

private instance : Std.TransCmp comparePayloadPaths := by
  unfold comparePayloadPaths
  infer_instance

private instance : Std.TransCmp comparePayloadTexts := by
  unfold comparePayloadTexts
  infer_instance

instance : Std.TransCmp StructuralDiagnostic.comparePayload := by
  unfold StructuralDiagnostic.comparePayload
  infer_instance

instance : Std.TransCmp StructuralDiagnostic.compare := by
  unfold StructuralDiagnostic.compare
  infer_instance

instance : Std.LawfulEqCmp StructuralDiagnostic.compare where
  eq_of_compare := by
    intro left right equality
    have rankAndRest := compareLex_eq_eq.mp equality
    have sourceAndRest := compareLex_eq_eq.mp rankAndRest.2
    have startAndRest := compareLex_eq_eq.mp sourceAndRest.2
    have endAndPayload := compareLex_eq_eq.mp startAndRest.2
    have natsAndRest := compareLex_eq_eq.mp endAndPayload.2
    have librariesAndRest := compareLex_eq_eq.mp natsAndRest.2
    have pathsAndTexts := compareLex_eq_eq.mp librariesAndRest.2
    have rankEquality : left.rank = right.rank := by
      exact Std.LawfulEqOrd.eq_of_compare rankAndRest.1
    have sourceEquality : left.span.source = right.span.source := by
      exact SourceId.compare_eq_iff_eq.mp sourceAndRest.1
    have startEquality : left.span.startByte = right.span.startByte := by
      exact Std.LawfulEqOrd.eq_of_compare startAndRest.1
    have endEquality : left.span.endByte = right.span.endByte := by
      exact Std.LawfulEqOrd.eq_of_compare endAndPayload.1
    have natsEquality : payloadNats left = payloadNats right := by
      exact Std.LawfulEqOrd.eq_of_compare natsAndRest.1
    have librariesEquality :
        payloadLibraries left = payloadLibraries right := by
      exact Std.LawfulEqOrd.eq_of_compare librariesAndRest.1
    have pathsEquality : payloadPaths left = payloadPaths right := by
      exact Std.LawfulEqOrd.eq_of_compare pathsAndTexts.1
    have textsEquality : payloadTexts left = payloadTexts right := by
      exact Std.LawfulEqOrd.eq_of_compare pathsAndTexts.2
    have spanEquality : left.span = right.span :=
      sourceSpan_eq_of_fields sourceEquality startEquality endEquality
    apply orderKey_injective
    apply OrderKey.eq_of_fields
    · exact rankEquality
    · exact spanEquality
    · exact natsEquality
    · exact librariesEquality
    · exact pathsEquality
    · exact textsEquality

instance : Ord StructuralDiagnostic where
  compare := StructuralDiagnostic.compare

instance : Std.OrientedOrd StructuralDiagnostic := by
  change Std.OrientedCmp StructuralDiagnostic.compare
  infer_instance

instance : Std.TransOrd StructuralDiagnostic := by
  change Std.TransCmp StructuralDiagnostic.compare
  infer_instance

instance : Std.LawfulEqOrd StructuralDiagnostic := by
  change Std.LawfulEqCmp StructuralDiagnostic.compare
  infer_instance

/-- Equal comparison coincides exactly with structural diagnostic equality. -/
@[simp] theorem compare_eq_iff_eq {left right : StructuralDiagnostic} :
    StructuralDiagnostic.compare left right = .eq ↔ left = right :=
  Std.LawfulEqCmp.compare_eq_iff_eq

/-- Non-strict canonical comparison for deterministic list sorting. -/
def le (left right : StructuralDiagnostic) : Bool :=
  (StructuralDiagnostic.compare left right).isLE

instance : LE StructuralDiagnostic where
  le left right := StructuralDiagnostic.le left right = true

theorem le_refl (diagnostic : StructuralDiagnostic) :
    StructuralDiagnostic.le diagnostic diagnostic = true :=
  Std.ReflCmp.isLE_rfl (cmp := StructuralDiagnostic.compare)

theorem le_trans {first second third : StructuralDiagnostic}
    (firstSecond : StructuralDiagnostic.le first second = true)
    (secondThird : StructuralDiagnostic.le second third = true) :
    StructuralDiagnostic.le first third = true :=
  Std.TransCmp.isLE_trans
    (cmp := StructuralDiagnostic.compare) firstSecond secondThird

theorem le_total (left right : StructuralDiagnostic) :
    StructuralDiagnostic.le left right = true ∨
      StructuralDiagnostic.le right left = true := by
  cases order : StructuralDiagnostic.compare left right with
  | lt => exact Or.inl (by simp [StructuralDiagnostic.le, order])
  | eq => exact Or.inl (by simp [StructuralDiagnostic.le, order])
  | gt =>
      have swapped : StructuralDiagnostic.compare right left = .lt :=
        Std.OrientedCmp.lt_of_gt
          (cmp := StructuralDiagnostic.compare) order
      exact Or.inr (by simp [StructuralDiagnostic.le, swapped])

theorem le_antisymm {left right : StructuralDiagnostic}
    (forward : StructuralDiagnostic.le left right = true)
    (backward : StructuralDiagnostic.le right left = true) :
    left = right := by
  apply StructuralDiagnostic.compare_eq_iff_eq.mp
  exact Std.OrientedCmp.isLE_antisymm
    (cmp := StructuralDiagnostic.compare) forward backward

/-- The stable code assigned to a structural diagnostic constructor. -/
def code : StructuralDiagnostic → String
  | .emptyImportSelection _ => "MSS0001"
  | .mixedImportWildcard _ => "MSS0002"
  | .duplicateImportSourceName _ _ => "MSS0003"
  | .duplicateImportLocalName _ _ => "MSS0004"
  | .emptyHidingClause _ => "MSS0005"
  | .duplicateHiddenName _ _ => "MSS0006"
  | .emptyLocalExportList _ => "MSS0007"
  | .emptyRemoteExportList _ => "MSS0008"
  | .mixedExportWildcard _ => "MSS0009"
  | .duplicateExportName _ _ => "MSS0010"
  | .duplicateExportModuleReference _ _ => "MSS0011"
  | .duplicateExportConstructor _ _ => "MSS0012"
  | .matchPatternArityMismatch _ _ _ => "MSS0013"
  | .emptyGenericPragmaTargets _ => "MSS0014"
  | .duplicatePragmaTarget _ _ => "MSS0015"
  | .modifierNotAllowed _ _ _ => "MSS0016"
  | .fallbackHasParameters _ _ => "MSS0017"
  | .fallbackHasNonUnitReturn _ => "MSS0018"
  | .requiredParameterTypeMissing _ _ => "MSS0019"
  | .controlOutsideLoop _ _ => "MSS0020"

end StructuralDiagnostic

/-- The total exact primary-span projection for every surface diagnostic. -/
def diagnosticSpan : SurfaceDiagnostic → SourceSpan
  | .lexical diagnostic => diagnostic.span
  | .parse diagnostic => diagnostic.span
  | .structural diagnostic => diagnostic.span

/-- The total structured source-identity projection for every diagnostic. -/
def diagnosticSource (diagnostic : SurfaceDiagnostic) : SourceId :=
  (diagnosticSpan diagnostic).source

/-- The total stable-code projection for every surface diagnostic. -/
def diagnosticCode : SurfaceDiagnostic → String
  | .lexical diagnostic => diagnostic.code
  | .parse diagnostic => diagnostic.code
  | .structural diagnostic => diagnostic.code

end Solcore.Surface.Multi
