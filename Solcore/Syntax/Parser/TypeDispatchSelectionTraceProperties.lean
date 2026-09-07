import Solcore.Syntax.DeclarativeTypeDispatchSelectionProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Type

/-! Executable lookahead selects exactly one independent branch on every
state. These proof-side projections do not change the recursive parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

namespace TypeDispatchTraceInternals

def selectedBranch (input : State) : TypeDispatchBranch :=
  if isKeyword input .functionKw then .function
  else if isContextual input .comptime && (input.peekOffsetKind? 1 == some (.symbol .less)) then .comptime
  else if isContextual input .mapping && (input.peekOffsetKind? 1 == some (.symbol .leftParen)) then .mapping
  else if isSymbol input .at then .proxy
  else if isSymbol input .leftParen then .tuple
  else if isIdentifier input then .named
  else .final

def rawParser (nested : Parser TypeExpr) (branch : TypeDispatchBranch) : Parser TypeExpr :=
  match branch with
  | .function => parseFunctionType nested
  | .comptime => parseComptimeType nested
  | .mapping => parseMappingType nested
  | .proxy => parseProxyType nested
  | .tuple => parseTupleType nested
  | .named => parseNamedType nested
  | .final => fun input => rejectAt input { head := .typeExpr, tail := [] } .typeExpr

private theorem pair_present_of_guard {input : State}
    (word : ContextualKeyword) (symbolValue : Symbol)
    (guard : (isContextual input word && (input.peekOffsetKind? 1 == some (.symbol symbolValue))) = true) :
    TypeDispatchPairPresent input.declarativeRemainder word symbolValue := by
  rcases Bool.and_eq_true_iff.mp guard with ⟨wordPresent, symbolPresent⟩
  rcases contextual_eq_ok_of_isContextual_eq_true word .typeExpr wordPresent with ⟨marker, markerResult⟩
  have advanced := isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true symbolValue symbolPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true symbolValue .typeExpr advanced with ⟨opening, openingResult⟩
  exact ⟨marker.span, opening.span,
    (contextual_success_exactTokenParses word .typeExpr markerResult).1,
    (symbol_success_exactTokenParses symbolValue .typeExpr openingResult).1⟩

theorem selectedBranch_selects (input : State) :
    TypeDispatchSelects input.declarativeRemainder (selectedBranch input) := by
  unfold selectedBranch
  split
  next present =>
    rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .typeExpr present with ⟨marker, result⟩
    exact .function ⟨marker.span, (keyword_success_exactTokenParses .functionKw .typeExpr result).1⟩
  next absent =>
    have functionAbsent := keywordAbsentAt_of_isKeyword_eq_false .functionKw (Bool.eq_false_iff.mpr absent)
    split
    next present => exact .comptime functionAbsent (pair_present_of_guard .comptime .less present)
    next absent =>
      have comptimeAbsent := contextualSymbolPairAbsentAt_of_guard_eq_false .comptime .less
        (Bool.eq_false_iff.mpr absent)
      split
      next present => exact .mapping functionAbsent comptimeAbsent (pair_present_of_guard .mapping .leftParen present)
      next absent =>
        have mappingAbsent := contextualSymbolPairAbsentAt_of_guard_eq_false .mapping .leftParen
          (Bool.eq_false_iff.mpr absent)
        split
        next present =>
          rcases symbol_eq_ok_of_isSymbol_eq_true .at .typeExpr present with ⟨marker, result⟩
          exact .proxy functionAbsent comptimeAbsent mappingAbsent
            ⟨marker.span, (symbol_success_exactTokenParses .at .typeExpr result).1⟩
        next absent =>
          have atAbsent := symbolAbsentAt_of_isSymbol_eq_false .at (Bool.eq_false_iff.mpr absent)
          split
          next present =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with ⟨marker, result⟩
            exact .tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
              ⟨marker.span, (symbol_success_exactTokenParses .leftParen .typeExpr result).1⟩
          next absent =>
            have leftParenAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr absent)
            split
            next present =>
              exact .named functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent
                (identifierPresentAt_of_isIdentifier_eq_true present)
            next absent =>
              exact .final functionAbsent comptimeAbsent mappingAbsent atAbsent leftParenAbsent
                (identifierAbsentAt_of_isIdentifier_eq_false (Bool.eq_false_iff.mpr absent))

theorem selectedBranch_eq_iff {input : State} {branch : TypeDispatchBranch} :
    selectedBranch input = branch ↔ TypeDispatchSelects input.declarativeRemainder branch := by
  constructor
  · intro same; rw [← same]; exact selectedBranch_selects input
  · exact (selectedBranch_selects input).branch_unique

theorem typeExprWithFuel_eq_selected_raw (fuel : Nat) (input : State) :
    typeExprWithFuel (fuel + 1) input = rawParser (typeExprWithFuel fuel) (selectedBranch input) input := by
  change (if isKeyword input .functionKw then parseFunctionType (typeExprWithFuel fuel) input
    else if isContextual input .comptime && (input.peekOffsetKind? 1 == some (.symbol .less)) then
      parseComptimeType (typeExprWithFuel fuel) input
    else if isContextual input .mapping && (input.peekOffsetKind? 1 == some (.symbol .leftParen)) then
      parseMappingType (typeExprWithFuel fuel) input
    else if isSymbol input .at then parseProxyType (typeExprWithFuel fuel) input
    else if isSymbol input .leftParen then parseTupleType (typeExprWithFuel fuel) input
    else if isIdentifier input then parseNamedType (typeExprWithFuel fuel) input
    else rejectAt input { head := .typeExpr, tail := [] } .typeExpr) = _
  simp only [selectedBranch]
  repeat' first | split | rfl

end TypeDispatchTraceInternals

theorem typeExprWithFuel_eq_raw_of_selection (fuel : Nat) {input : State} {branch : TypeDispatchBranch}
    (selection : TypeDispatchSelects input.declarativeRemainder branch) :
    typeExprWithFuel (fuel + 1) input = TypeDispatchTraceInternals.rawParser (typeExprWithFuel fuel) branch input := by
  rw [TypeDispatchTraceInternals.typeExprWithFuel_eq_selected_raw,
    TypeDispatchTraceInternals.selectedBranch_eq_iff.mpr selection]

end Solcore.Syntax.Parser
