import Solcore.Frontend.ClosedSourceUnaryProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.LocalScopeProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence

/- Independent old-API unary costs precede original mixed-value image and depth laws.
Complete Core and mixed tails/stores remain separate; no projection is asserted. -/
set_option autoImplicit false
namespace Tests.ClosedSourceUnary
open Solcore Solcore.Frontend

private def nest (op : Syntax.UnaryOp) (spans : Nat → Syntax.SourceSpan) :
    Nat → Syntax.Expr → Syntax.Expr
  | 0, leaf => leaf
  | n + 1, leaf =>
      ⟨spans (2 * n), .unary ⟨spans (2 * n + 1), op⟩ (nest op spans n leaf)⟩

private def bval : Nat → Bool → Bool
  | 0, input => input
  | n + 1, input => !(bval n input)

private def wval : Nat → Core.Word → Core.Word
  | 0, input => input
  | n + 1, input => (wval n input).bitNot

private def coreNest (op : Core.UnaryOp) : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .unary op (coreNest op n)

private def resolvedNest (op : Core.UnaryOp) (id : Resolved.LocalId) : Nat → Resolved.Expr
  | 0 => .var id
  | n + 1 => .unary op (resolvedNest op id n)

private theorem bool_resolution (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (named : LocalNameTable.Lookup names name.value id) :
    ResolvesLocalExpression names (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .boolNot id n) := by
  induction n with
  | zero => exact .identifier named
  | succ n ih => exact .logicalNot ih

private theorem word_resolution (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (named : LocalNameTable.Lookup names name.value id) :
    ResolvesLocalExpression names (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (resolvedNest .wordNot id n) := by
  induction n with
  | zero => exact .identifier named
  | succ n ih => exact .bitNot ih

private theorem nesting_lowered (op : Core.UnaryOp) (id : Resolved.LocalId)
    (scope : List Resolved.LocalId) (n : Nat) :
    Resolved.Lowers (id :: scope) (resolvedNest op id n) (coreNest op n) := by
  induction n with
  | zero => exact .var .head
  | succ n ih => exact .unary ih

private theorem independent_bool_cost (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (input : Bool) (coreTail : Resolved.Environment)
    (coreStore : Core.Store) (named : LocalNameTable.Lookup names name.value id) :
    let original := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore original (.bool (bval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .boolNot n)
        (.bool input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.bool (bval n input)) coreStore) := by
  have cost : LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩)
      (.bool (bval n input)) coreStore (2 * n + 1) := by
    induction n with
    | zero => exact .identifier named .head
    | succ n ih =>
        simpa [nest, bval, Nat.mul_add, Nat.add_assoc] using
          LocalExpressionEvaluatesWithCost.logicalNot ih
  exact ⟨cost, cost.toSteps (bool_resolution n spans leafSpan name id names named)
    (nesting_lowered .boolNot id (Resolved.LocalScope.ids coreTail) n)⟩

private theorem independent_word_cost (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (names : LocalNameTable) (input : Core.Word) (coreTail : Resolved.Environment)
    (coreStore : Core.Store) (named : LocalNameTable.Lookup names name.value id) :
    let original := nest .bitNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore original (.word (wval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .wordNot n)
        (.word input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.word (wval n input)) coreStore) := by
  have cost : LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore (nest .bitNot spans n ⟨leafSpan, .identifier name⟩)
      (.word (wval n input)) coreStore (2 * n + 1) := by
    induction n with
    | zero => exact .identifier named .head
    | succ n ih =>
        simpa [nest, wval, Nat.mul_add, Nat.add_assoc] using
          LocalExpressionEvaluatesWithCost.bitNot ih
  exact ⟨cost, cost.toSteps (word_resolution n spans leafSpan name id names named)
    (nesting_lowered .wordNot id (Resolved.LocalScope.ids coreTail) n)⟩

private theorem original_bool (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (.bool (bval n input)) store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .logicalNot ih

private theorem original_word (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    ClosedSourceExpressionEvaluates owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (.word (wval n input)) store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .bitNot ih

private theorem bool_images (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) actual final ↔
      actual = .bool (bval n input) ∧ final = store := by
  induction n with
  | zero =>
      intro actual final
      constructor
      · intro evaluated
        cases evaluated with
        | reference otherNamed otherFound =>
            cases named.id_unique otherNamed
            exact ⟨otherFound.value_unique found, rfl⟩
        | creation shape => cases shape
      · rintro ⟨rfl, rfl⟩; exact .reference named found
  | succ n ih =>
      intro actual final
      have image := closedSourceExpressionEvaluates_logicalNot_iff
        (owner := owner) (names := names) (captured := captured) (initialStore := store)
        (finalStore := final) (span := spans (2 * n)) (operatorSpan := spans (2 * n + 1))
        (operand := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) (value := actual)
      constructor
      · intro evaluated
        obtain ⟨value, child, same⟩ := image.mp evaluated
        obtain ⟨valueEq, storeEq⟩ := (ih _ _).mp child
        rw [RuntimeValue.bool.inj valueEq] at same
        exact ⟨same, storeEq⟩
      · rintro ⟨same, storeEq⟩
        refine image.mpr ⟨bval n input, ?_, same⟩
        rw [storeEq]
        exact original_bool n spans leafSpan name id owner names captured store input named found

private theorem word_images (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) actual final ↔
      actual = .word (wval n input) ∧ final = store := by
  induction n with
  | zero =>
      intro actual final
      constructor
      · intro evaluated
        cases evaluated with
        | reference otherNamed otherFound =>
            cases named.id_unique otherNamed
            exact ⟨otherFound.value_unique found, rfl⟩
        | creation shape => cases shape
      · rintro ⟨rfl, rfl⟩; exact .reference named found
  | succ n ih =>
      intro actual final
      have image := closedSourceExpressionEvaluates_bitNot_iff
        (owner := owner) (names := names) (captured := captured) (initialStore := store)
        (finalStore := final) (span := spans (2 * n)) (operatorSpan := spans (2 * n + 1))
        (operand := nest .bitNot spans n ⟨leafSpan, .identifier name⟩) (value := actual)
      constructor
      · intro evaluated
        obtain ⟨value, child, same⟩ := image.mp evaluated
        obtain ⟨valueEq, storeEq⟩ := (ih _ _).mp child
        rw [RuntimeValue.word.inj valueEq] at same
        exact ⟨same, storeEq⟩
      · rintro ⟨same, storeEq⟩
        refine image.mpr ⟨wval n input, ?_, same⟩
        rw [storeEq]
        exact original_word n spans leafSpan name id owner names captured store input named found

private theorem bool_depth (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Bool)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) = some (.bool (bval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store
      (nest .logicalNot spans n ⟨leafSpan, .identifier name⟩) = none := by
  induction n with
  | zero =>
      simp [nest, bval, evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      simp only [nest, bval, evaluateClosedSourceExpression?_logicalNot, ih.1, ih.2,
        bind, Option.bind_some, Option.bind_none, pure, and_self]

private theorem word_depth (n : Nat) (spans : Nat → Syntax.SourceSpan)
    (leafSpan : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (input : Core.Word)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    evaluateClosedSourceExpression? (n + 1) owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) = some (.word (wval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store
      (nest .bitNot spans n ⟨leafSpan, .identifier name⟩) = none := by
  induction n with
  | zero =>
      simp [nest, wval, evaluateClosedSourceExpression?, LocalNameTable.lookup?_iff.mpr named,
        Resolved.LocalScope.lookup?_iff.mpr found]
  | succ n ih =>
      simp only [nest, wval, evaluateClosedSourceExpression?_bitNot, ih.1, ih.2,
        bind, Option.bind_some, Option.bind_none, pure, and_self]

theorem bool_nesting_original_images_and_cost
    (n : Nat) (spans : Nat → Syntax.SourceSpan) (leafSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (input : Bool) (coreTail : Resolved.Environment) (coreStore : Core.Store)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.bool input)) :
    let original := nest .logicalNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .bool input) :: coreTail)
      coreStore original (.bool (bval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .boolNot n)
        (.bool input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.bool (bval n input)) coreStore) ∧
    ClosedSourceExpressionEvaluates owner names captured store original
      (.bool (bval n input)) store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      original actual final ↔ actual = .bool (bval n input) ∧ final = store) ∧
    evaluateClosedSourceExpression? (n + 1) owner names captured store original =
      some (.bool (bval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store original = none := by
  have cost := independent_bool_cost n spans leafSpan name id names input coreTail coreStore named
  have original := original_bool n spans leafSpan name id owner names captured store input named found
  exact ⟨cost.1, cost.2, original,
    bool_images n spans leafSpan name id owner names captured store input named found,
    bool_depth n spans leafSpan name id owner names captured store input named found⟩

theorem word_nesting_original_images_and_cost
    (n : Nat) (spans : Nat → Syntax.SourceSpan) (leafSpan : Syntax.SourceSpan)
    (name : Syntax.Identifier) (id : Resolved.LocalId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (input : Core.Word) (coreTail : Resolved.Environment) (coreStore : Core.Store)
    (named : LocalNameTable.Lookup names name.value id)
    (found : Resolved.LocalScope.Lookup captured id (.word input)) :
    let original := nest .bitNot spans n ⟨leafSpan, .identifier name⟩
    LocalExpressionEvaluatesWithCost names ((id, .word input) :: coreTail)
      coreStore original (.word (wval n input)) coreStore (2 * n + 1) ∧
    Core.Steps (2 * n + 1)
      (Core.State.initial (coreNest .wordNot n)
        (.word input :: Resolved.LocalScope.values coreTail) coreStore)
      (Core.State.final (.word (wval n input)) coreStore) ∧
    ClosedSourceExpressionEvaluates owner names captured store original
      (.word (wval n input)) store ∧
    (∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      original actual final ↔ actual = .word (wval n input) ∧ final = store) ∧
    evaluateClosedSourceExpression? (n + 1) owner names captured store original =
      some (.word (wval n input), store) ∧
    evaluateClosedSourceExpression? n owner names captured store original = none := by
  have cost := independent_word_cost n spans leafSpan name id names input coreTail coreStore named
  have original := original_word n spans leafSpan name id owner names captured store input named found
  exact ⟨cost.1, cost.2, original,
    word_images n spans leafSpan name id owner names captured store input named found,
    word_depth n spans leafSpan name id owner names captured store input named found⟩

end Tests.ClosedSourceUnary
