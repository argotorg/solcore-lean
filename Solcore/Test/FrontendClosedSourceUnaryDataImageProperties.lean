import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Resolved.LocalScope

set_option autoImplicit false
namespace Tests.ClosedSourceUnaryDataImages
open Solcore Solcore.Frontend

private def nest (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, leaf => leaf
  | n + 1, leaf => ⟨spans (3 * n), .group
      ⟨spans (3 * n + 1), .unary ⟨spans (3 * n + 2), op⟩ (nest op spans n leaf)⟩⟩

private def bval : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => !(bval n b)

private def wval : Nat → Core.Word → Core.Word
  | 0, w => w
  | n + 1, w => (wval n w).bitNot

private def resolvedNest (op : Core.UnaryOp) (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .var id
  | n + 1 => .unary op (resolvedNest op id n)

private def coreNest (op : Core.UnaryOp) (index : Nat) : Nat → Core.Expr
  | 0 => .var index
  | n + 1 => .unary op (coreNest op index n)

private def source (spans : Nat → Syntax.SourceSpan) (nb nw : Nat)
    (boolName wordName payloadName : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 0, .tuple ⟨spans 1, [
    nest .logicalNot (fun i => spans (8 + 2 * i)) nb ⟨spans 4, .identifier boolName⟩,
    ⟨spans 2, .tuple ⟨spans 3, [
      nest .bitNot (fun i => spans (9 + 2 * i)) nw ⟨spans 5, .identifier wordName⟩,
      ⟨spans 6, .group ⟨spans 7, .identifier payloadName⟩⟩]⟩⟩]⟩⟩

private def result (nb nw : Nat) (b : Bool) (w : Core.Word) (payload : Core.Value) : Core.Value :=
  .pair (.bool (bval nb b)) (.pair (.word (wval nw w)) payload)

private def resolvedSource (nb nw : Nat) (boolId wordId payloadId : Resolved.LocalId) : Resolved.Expr :=
  .pair (resolvedNest .boolNot boolId nb) (.pair (resolvedNest .wordNot wordId nw) (.var payloadId))

private def coreSource (nb nw boolIndex wordIndex payloadIndex : Nat) : Core.Expr :=
  .pair (coreNest .boolNot boolIndex nb) (.pair (coreNest .wordNot wordIndex nw) (.var payloadIndex))

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem bool_paths (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) (input : Bool) (index : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id (.bool input))
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index)
    (atValue : (Resolved.LocalScope.values environment)[index]? = some (.bool input)) :
    ClosedSourceDataExpression (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (.bool (bval n input)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (.bool (bval n input)) store ∧
    ResolvesLocalExpression names (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .boolNot id n) ∧
    Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedNest .boolNot id n) (coreNest .boolNot index n) ∧
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreNest .boolNot index n) (.bool (bval n input)) store := by
  induction n with
  | zero =>
      exact ⟨.reference, .reference named (by simpa only [RuntimeValue.ofCore, bval] using mapped_lookup found), .identifier named found,
        .identifier named, .var indexed, .var atValue⟩
  | succ n ih =>
      rcases ih with ⟨gate, closed, localPath, resolution, lowering, corePath⟩
      exact ⟨.group (.logicalNot gate), .group (.logicalNot closed), .group (.logicalNot localPath),
        .group (.logicalNot resolution), .unary lowering, .unary corePath rfl⟩

private theorem word_paths (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store) (input : Core.Word) (index : Nat)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup environment id (.word input))
    (indexed : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index)
    (atValue : (Resolved.LocalScope.values environment)[index]? = some (.word input)) :
    ClosedSourceDataExpression (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (.word (wval n input)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (.word (wval n input)) store ∧
    ResolvesLocalExpression names (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .wordNot id n) ∧
    Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedNest .wordNot id n) (coreNest .wordNot index n) ∧
    Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreNest .wordNot index n) (.word (wval n input)) store := by
  induction n with
  | zero =>
      exact ⟨.reference, .reference named (by simpa only [RuntimeValue.ofCore, wval] using mapped_lookup found), .identifier named found,
        .identifier named, .var indexed, .var atValue⟩
  | succ n ih =>
      rcases ih with ⟨gate, closed, localPath, resolution, lowering, corePath⟩
      exact ⟨.group (.bitNot gate), .group (.bitNot closed), .group (.bitNot localPath),
        .group (.bitNot resolution), .unary lowering, .unary corePath rfl⟩

private theorem all_images {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {store : Core.Store} {original : Syntax.Expr}
    {expected : Core.Value} {resolved : Resolved.Expr} {core : Core.Expr}
    (gate : ClosedSourceDataExpression original)
    (localPath : LocalExpressionEvaluates names environment store original expected store)
    (resolution : ResolvesLocalExpression names original resolved)
    (lowering : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    (corePath : Core.Evaluates (Resolved.LocalScope.values environment) store core expected store) :
    ∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
      ClosedSourceExpressionEvaluates owner names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
        (store.map RuntimeValue.ofCore) original actual actualFinal ↔
      actual = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore := by
  intro actual actualFinal
  constructor
  · intro evaluated
    obtain ⟨lv, ls, localValue, _, localActual⟩ := gate.local_evaluates_iff.mp evaluated
    obtain ⟨rfl, rfl⟩ := localActual.deterministic localPath
    obtain ⟨cv, cs, _, coreStore, coreActual⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp evaluated
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic coreActual corePath
    exact ⟨localValue, coreStore⟩
  · intro images
    have localActual : ClosedSourceExpressionEvaluates owner names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
        (store.map RuntimeValue.ofCore) original actual actualFinal :=
      gate.local_evaluates_iff.mpr ⟨expected, store, images.1, images.2, localPath⟩
    obtain ⟨value, finalStore, sameValue, sameStore, reflectedCore⟩ :=
      (gate.core_evaluates_iff resolution lowering).mp localActual
    obtain ⟨valueSame, storeSame⟩ := Core.evaluation_deterministic reflectedCore corePath
    rw [valueSame] at sameValue
    rw [storeSame] at sameStore
    exact (gate.core_evaluates_iff resolution lowering).mpr
      ⟨expected, store, sameValue, sameStore, corePath⟩

theorem mixed_nesting_original_and_all_actual_images
    (spans : Nat → Syntax.SourceSpan) (nb nw : Nat)
    (boolName wordName payloadName : Syntax.Identifier)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (boolId wordId payloadId : Resolved.LocalId)
    (inputBool : Bool) (inputWord : Core.Word) (payload : Core.Value)
    (boolNamed : LocalNameTable.Lookup names boolName.value boolId)
    (wordNamed : LocalNameTable.Lookup names wordName.value wordId)
    (payloadNamed : LocalNameTable.Lookup names payloadName.value payloadId)
    (boolFound : Resolved.LocalScope.Lookup environment boolId (.bool inputBool))
    (wordFound : Resolved.LocalScope.Lookup environment wordId (.word inputWord))
    (payloadFound : Resolved.LocalScope.Lookup environment payloadId payload) :
    let original := source spans nb nw boolName wordName payloadName
    let expected := result nb nw inputBool inputWord payload
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) original
      (RuntimeValue.ofCore expected) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store ∧
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store ∧
      (∀ (actual : RuntimeValue) (actualFinal : List RuntimeValue),
        ClosedSourceExpressionEvaluates owner names
          (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (store.map RuntimeValue.ofCore) original actual actualFinal ↔
        actual = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore) := by
  dsimp only
  obtain ⟨bi, boolAt, boolValue⟩ := boolFound.indexed
  obtain ⟨wi, wordAt, wordValue⟩ := wordFound.indexed
  obtain ⟨qi, payloadAt, payloadValue⟩ := payloadFound.indexed
  obtain ⟨bg, bc, bl, br, blo, bcore⟩ :=
    bool_paths nb (fun i => spans (8 + 2 * i)) (spans 4) boolName boolId
      owner names environment store inputBool bi boolNamed boolFound boolAt boolValue
  obtain ⟨wg, wc, wl, wr, wlo, wcore⟩ :=
    word_paths nw (fun i => spans (9 + 2 * i)) (spans 5) wordName wordId
      owner names environment store inputWord wi wordNamed wordFound wordAt wordValue
  have gate : ClosedSourceDataExpression (source spans nb nw boolName wordName payloadName) :=
    .pair bg (.pair wg (.group .reference))
  have closed : ClosedSourceExpressionEvaluates owner names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) (source spans nb nw boolName wordName payloadName)
      (RuntimeValue.ofCore (result nb nw inputBool inputWord payload))
      (store.map RuntimeValue.ofCore) := by
    simp only [result, RuntimeValue.ofCore]
    exact .pair bc (.pair wc (.group (.reference payloadNamed (mapped_lookup payloadFound))))
  have localPath : LocalExpressionEvaluates names environment store
      (source spans nb nw boolName wordName payloadName) (result nb nw inputBool inputWord payload) store :=
    .pair bl (.pair wl (.group (.identifier payloadNamed payloadFound)))
  have resolution : ResolvesLocalExpression names (source spans nb nw boolName wordName payloadName)
      (resolvedSource nb nw boolId wordId payloadId) :=
    .pair br (.pair wr (.group (.identifier payloadNamed)))
  have lowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      (resolvedSource nb nw boolId wordId payloadId) (coreSource nb nw bi wi qi) :=
    .pair blo (.pair wlo (.var payloadAt))
  have corePath : Core.Evaluates (Resolved.LocalScope.values environment) store
      (coreSource nb nw bi wi qi) (result nb nw inputBool inputWord payload) store :=
    .pair bcore (.pair wcore (.var payloadValue))
  exact ⟨gate, closed, localPath, resolvedSource nb nw boolId wordId payloadId,
    coreSource nb nw bi wi qi, resolution, lowering, corePath,
    all_images gate localPath resolution lowering corePath⟩

end Tests.ClosedSourceUnaryDataImages
