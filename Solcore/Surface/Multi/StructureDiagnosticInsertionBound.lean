import Solcore.Surface.Multi.StructureDiagnosticInsertionUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

private theorem flatMap_length_le_measureList
    {alpha beta : Type} (collect : alpha → List beta)
    (measure : alpha → Nat)
    (bound : ∀ value, (collect value).length ≤ measure value)
    (values : List alpha) :
    (values.flatMap collect).length ≤ measureList measure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      simpa [measureList, Nat.add_comm] using
        Nat.add_le_add (bound head) induction

@[simp] private theorem measureList_expressionMeasure_eq
    (values : List Expression) :
    measureList expressionMeasure values = expressionListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, expressionListMeasure, induction]

@[simp] private theorem measureList_patternMeasure_eq
    (values : List Pattern) :
    measureList patternMeasure values = patternListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, patternListMeasure, induction]

@[simp] private theorem measureList_statementMeasure_eq
    (values : List Statement) :
    measureList statementMeasure values = statementListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, statementListMeasure, induction]

@[simp] private theorem measureList_forInitItemMeasure_eq
    (values : List ForInitItem) :
    measureList forInitItemMeasure values = forInitItemListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, forInitItemListMeasure, induction]

@[simp] private theorem measureList_forPostItemMeasure_eq
    (values : List ForPostItem) :
    measureList forPostItemMeasure values = forPostItemListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, forPostItemListMeasure, induction]

@[simp] private theorem measureList_matchArmMeasure_eq
    (values : List MatchArm) :
    measureList matchArmMeasure values = matchArmListMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [measureList] at induction ⊢
      simp only [List.map_cons, List.sum_cons, matchArmListMeasure, induction]

@[simp] private theorem measureList_nonempty_expressionMeasure_eq
  (values : NonemptyList Expression) :
    measureList expressionMeasure (nonemptyToList values) =
      expressionNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      calc
        measureList expressionMeasure (nonemptyToList ⟨head, tail⟩) =
            expressionMeasure head + measureList expressionMeasure tail := by
          simp [nonemptyToList, measureList]
        _ = expressionMeasure head + expressionListMeasure tail := by
          rw [measureList_expressionMeasure_eq]
        _ = expressionNonemptyMeasure ⟨head, tail⟩ := rfl

@[simp] private theorem measureList_nonempty_patternMeasure_eq
  (values : NonemptyList Pattern) :
    measureList patternMeasure (nonemptyToList values) =
      patternNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      calc
        measureList patternMeasure (nonemptyToList ⟨head, tail⟩) =
            patternMeasure head + measureList patternMeasure tail := by
          simp [nonemptyToList, measureList]
        _ = patternMeasure head + patternListMeasure tail := by
          rw [measureList_patternMeasure_eq]
        _ = patternNonemptyMeasure ⟨head, tail⟩ := rfl

@[simp] private theorem measureList_nonempty_matchArmMeasure_eq
  (values : NonemptyList MatchArm) :
    measureList matchArmMeasure (nonemptyToList values) =
      matchArmNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      calc
        measureList matchArmMeasure (nonemptyToList ⟨head, tail⟩) =
            matchArmMeasure head + measureList matchArmMeasure tail := by
          simp [nonemptyToList, measureList]
        _ = matchArmMeasure head + matchArmListMeasure tail := by
          rw [measureList_matchArmMeasure_eq]
        _ = matchArmNonemptyMeasure ⟨head, tail⟩ := rfl

private def DiagnosticFuelBounds (fuel : Nat) : Prop :=
  (∀ expression : Expression,
    (expressionDiagnosticsFuel fuel expression).length ≤
      expressionMeasure expression) ∧
  (∀ pattern : Pattern,
    (patternDiagnosticsFuel fuel pattern).length ≤ patternMeasure pattern) ∧
  (∀ loopDepth body,
    (bodyDiagnosticsFuel fuel loopDepth body).length ≤ bodyMeasure body) ∧
  (∀ loopDepth statement,
    (statementDiagnosticsFuel fuel loopDepth statement).length ≤
      statementMeasure statement) ∧
  (∀ item : ForInitItem,
    (forInitDiagnosticsFuel fuel item).length ≤ forInitItemMeasure item) ∧
  (∀ item : ForPostItem,
    (forPostDiagnosticsFuel fuel item).length ≤ forPostItemMeasure item)

private theorem diagnosticFuelBounds (fuel : Nat) : DiagnosticFuelBounds fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro expression
        simp [expressionDiagnosticsFuel]
      · intro pattern
        simp [patternDiagnosticsFuel]
      · intro loopDepth body
        simp [bodyDiagnosticsFuel]
      · intro loopDepth statement
        simp [statementDiagnosticsFuel]
      · intro item
        simp [forInitDiagnosticsFuel]
      · intro item
        simp [forPostDiagnosticsFuel]
  | succ fuel induction =>
      rcases induction with
        ⟨expressionBound, patternBound, bodyBound, statementBound,
          forInitBound, forPostBound⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro expression
        rcases expression with ⟨span, payload⟩
        cases payload with
        | name name =>
            simp [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
        | call callee arguments =>
            have calleeBound := expressionBound callee
            have argumentsBound := flatMap_length_le_measureList
              (expressionDiagnosticsFuel fuel) expressionMeasure
              expressionBound arguments
            simp only [measureList_expressionMeasure_eq] at argumentsBound
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure, List.length_append]
            omega
        | select receiver field =>
            have receiverBound := expressionBound receiver
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
        | dotConstructor marker name arguments =>
            cases arguments with
            | none =>
                simp [expressionDiagnosticsFuel, expressionMeasure,
                  expressionPayloadMeasure, expressionListOptionMeasure]
            | some values =>
                have valuesBound := flatMap_length_le_measureList
                  (expressionDiagnosticsFuel fuel) expressionMeasure
                  expressionBound values
                simp only [measureList_expressionMeasure_eq] at valuesBound
                simp only [expressionDiagnosticsFuel, expressionMeasure,
                  expressionPayloadMeasure, expressionListOptionMeasure]
                omega
        | proxy marker typeExpression =>
            simp [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
        | literal literal =>
            simp [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
        | lambda parameters returnType body =>
            have nestedBound := bodyBound 0 body
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
        | annotation inner typeExpression =>
            have innerBound := expressionBound inner
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
        | keywordConditional condition thenBranch elseBranch =>
            have conditionBound := expressionBound condition
            have thenBound := expressionBound thenBranch
            have elseBound := expressionBound elseBranch
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure, List.length_append]
            omega
        | ternaryConditional condition thenBranch elseBranch =>
            have conditionBound := expressionBound condition
            have thenBound := expressionBound thenBranch
            have elseBound := expressionBound elseBranch
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure, List.length_append]
            omega
        | index receiver index =>
            have receiverBound := expressionBound receiver
            have indexBound := expressionBound index
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure, List.length_append]
            omega
        | «prefix» operator operand =>
            have operandBound := expressionBound operand
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
        | «infix» operator left right =>
            have leftBound := expressionBound left
            have rightBound := expressionBound right
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure, List.length_append]
            omega
        | tuple elements =>
            have elementsBound := flatMap_length_le_measureList
              (expressionDiagnosticsFuel fuel) expressionMeasure
              expressionBound elements
            simp only [measureList_expressionMeasure_eq] at elementsBound
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
        | group inner =>
            have innerBound := expressionBound inner
            simp only [expressionDiagnosticsFuel, expressionMeasure,
              expressionPayloadMeasure]
            omega
      · intro pattern
        rcases pattern with ⟨span, payload⟩
        cases payload with
        | named name arguments =>
            cases arguments with
            | none =>
                simp [patternDiagnosticsFuel, patternMeasure,
                  patternPayloadMeasure, patternArgumentsMeasure]
            | some values =>
                have valuesBound := flatMap_length_le_measureList
                  (patternDiagnosticsFuel fuel) patternMeasure
                  patternBound (nonemptyToList values)
                simp only [measureList_nonempty_patternMeasure_eq] at valuesBound
                simp only [patternDiagnosticsFuel, patternMeasure,
                  patternPayloadMeasure, patternArgumentsMeasure]
                omega
        | dotConstructor marker name arguments =>
            cases arguments with
            | none =>
                simp [patternDiagnosticsFuel, patternMeasure,
                  patternPayloadMeasure, patternArgumentsMeasure]
            | some values =>
                have valuesBound := flatMap_length_le_measureList
                  (patternDiagnosticsFuel fuel) patternMeasure
                  patternBound (nonemptyToList values)
                simp only [measureList_nonempty_patternMeasure_eq] at valuesBound
                simp only [patternDiagnosticsFuel, patternMeasure,
                  patternPayloadMeasure, patternArgumentsMeasure]
                omega
        | wildcard marker =>
            simp [patternDiagnosticsFuel, patternMeasure, patternPayloadMeasure]
        | literal literal =>
            simp [patternDiagnosticsFuel, patternMeasure, patternPayloadMeasure]
        | comptime marker expression =>
            have nestedBound := expressionBound expression
            simp only [patternDiagnosticsFuel, patternMeasure,
              patternPayloadMeasure]
            omega
        | tuple elements =>
            have elementsBound := flatMap_length_le_measureList
              (patternDiagnosticsFuel fuel) patternMeasure patternBound elements
            simp only [measureList_patternMeasure_eq] at elementsBound
            simp only [patternDiagnosticsFuel, patternMeasure,
              patternPayloadMeasure]
            omega
        | group inner =>
            have innerBound := patternBound inner
            simp only [patternDiagnosticsFuel, patternMeasure,
              patternPayloadMeasure]
            omega
      · intro loopDepth body
        rcases body with ⟨span, payload⟩
        rcases payload with ⟨origin, statements⟩
        have statementsBound := flatMap_length_le_measureList
          (statementDiagnosticsFuel fuel loopDepth) statementMeasure
          (statementBound loopDepth) statements
        simp only [measureList_statementMeasure_eq] at statementsBound
        simp only [bodyDiagnosticsFuel, bodyMeasure, bodyPayloadMeasure]
        omega
      · intro loopDepth statement
        rcases statement with ⟨span, payload⟩
        cases payload with
        | assignment operator left right =>
            have leftBound := expressionBound left
            have rightBound := expressionBound right
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure, List.length_append]
            omega
        | letBinding binding =>
            rcases binding with ⟨bindingSpan, bindingPayload⟩
            rcases bindingPayload with
              ⟨comptime, name, typeExpression, initializer⟩
            cases initializer with
            | none =>
                simp [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, letBindingMeasure,
                  letBindingPayloadMeasure, expressionOptionMeasure]
            | some expression =>
                have nestedBound := expressionBound expression
                simp only [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, letBindingMeasure,
                  letBindingPayloadMeasure, expressionOptionMeasure]
                omega
        | block body =>
            have nestedBound := bodyBound loopDepth body
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
            omega
        | expression expression terminator =>
            have nestedBound := expressionBound expression
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
            omega
        | «return» value terminator =>
            cases value with
            | none =>
                simp [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, expressionOptionMeasure]
            | some expression =>
                have nestedBound := expressionBound expression
                simp only [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, expressionOptionMeasure]
                omega
        | «match» scrutinees arms terminator =>
            let expected := (nonemptyToList scrutinees).length
            let armDiagnostics := fun arm : MatchArm =>
              let patterns := nonemptyToList arm.payload.patterns
              let mismatch :=
                if patterns.length = expected then []
                else [.matchPatternArityMismatch
                  arm.span expected patterns.length]
              mismatch ++ patterns.flatMap (patternDiagnosticsFuel fuel) ++
                bodyDiagnosticsFuel fuel loopDepth arm.payload.body
            have scrutineesBound := flatMap_length_le_measureList
              (expressionDiagnosticsFuel fuel) expressionMeasure
              expressionBound (nonemptyToList scrutinees)
            simp only [measureList_nonempty_expressionMeasure_eq] at scrutineesBound
            have armBound : ∀ arm, (armDiagnostics arm).length ≤
                matchArmMeasure arm := by
              intro arm
              rcases arm with ⟨armSpan, armPayload⟩
              rcases armPayload with ⟨patterns, body⟩
              have patternsBound := flatMap_length_le_measureList
                (patternDiagnosticsFuel fuel) patternMeasure patternBound
                (nonemptyToList patterns)
              simp only [measureList_nonempty_patternMeasure_eq] at patternsBound
              have nestedBodyBound := bodyBound loopDepth body
              have mismatchBound :
                  (if (nonemptyToList patterns).length = expected then []
                    else [StructuralDiagnostic.matchPatternArityMismatch
                      armSpan expected
                        (nonemptyToList patterns).length]).length ≤ 1 := by
                split <;> simp
              simp only [armDiagnostics, List.length_append,
                matchArmMeasure, matchArmPayloadMeasure]
              omega
            have armsBound := flatMap_length_le_measureList armDiagnostics
              matchArmMeasure armBound (nonemptyToList arms)
            simp only [measureList_nonempty_matchArmMeasure_eq] at armsBound
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
            rw [List.length_append]
            change
              ((nonemptyToList scrutinees).flatMap
                (expressionDiagnosticsFuel fuel)).length +
                ((nonemptyToList arms).flatMap armDiagnostics).length ≤ _
            omega
        | assembly slice =>
            simp [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
        | ifThenElse condition thenBody elseBody =>
            have conditionBound := expressionBound condition
            have thenBound := bodyBound loopDepth thenBody
            cases elseBody with
            | none =>
                simp only [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, bodyOptionMeasure,
                  List.length_append, List.length_nil]
                omega
            | some elseBody =>
                have elseBound := bodyBound loopDepth elseBody
                simp only [statementDiagnosticsFuel, statementMeasure,
                  statementPayloadMeasure, bodyOptionMeasure,
                  List.length_append]
                omega
        | forLoop initializers condition post body =>
            have initializersBound := flatMap_length_le_measureList
              (forInitDiagnosticsFuel fuel) forInitItemMeasure
              forInitBound initializers
            simp only [measureList_forInitItemMeasure_eq] at initializersBound
            have conditionBound := expressionBound condition
            have postBound := flatMap_length_le_measureList
              (forPostDiagnosticsFuel fuel) forPostItemMeasure
              forPostBound post
            simp only [measureList_forPostItemMeasure_eq] at postBound
            have nestedBodyBound := bodyBound (loopDepth + 1) body
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure, List.length_append]
            omega
        | «break» terminator =>
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
            split <;> simp
        | «continue» terminator =>
            simp only [statementDiagnosticsFuel, statementMeasure,
              statementPayloadMeasure]
            split <;> simp
      · intro item
        rcases item with ⟨span, payload⟩
        cases payload with
        | letBinding binding =>
            rcases binding with ⟨bindingSpan, bindingPayload⟩
            rcases bindingPayload with
              ⟨comptime, name, typeExpression, initializer⟩
            cases initializer with
            | none =>
                simp [forInitDiagnosticsFuel, forInitItemMeasure,
                  forInitItemPayloadMeasure, letBindingMeasure,
                  letBindingPayloadMeasure, expressionOptionMeasure]
            | some expression =>
                have nestedBound := expressionBound expression
                simp only [forInitDiagnosticsFuel, forInitItemMeasure,
                  forInitItemPayloadMeasure, letBindingMeasure,
                  letBindingPayloadMeasure, expressionOptionMeasure]
                omega
        | assignment operator left right =>
            have leftBound := expressionBound left
            have rightBound := expressionBound right
            simp only [forInitDiagnosticsFuel, forInitItemMeasure,
              forInitItemPayloadMeasure, List.length_append]
            omega
        | expression expression =>
            have nestedBound := expressionBound expression
            simp only [forInitDiagnosticsFuel, forInitItemMeasure,
              forInitItemPayloadMeasure]
            omega
      · intro item
        rcases item with ⟨span, payload⟩
        cases payload with
        | assignment operator left right =>
            have leftBound := expressionBound left
            have rightBound := expressionBound right
            simp only [forPostDiagnosticsFuel, forPostItemMeasure,
              forPostItemPayloadMeasure, List.length_append]
            omega
        | expression expression =>
            have nestedBound := expressionBound expression
            simp only [forPostDiagnosticsFuel, forPostItemMeasure,
              forPostItemPayloadMeasure]
            omega

/-- Recursive expression collectors emit no more candidates than their
concrete expression subtree contains AST carriers. -/
theorem expressionDiagnosticsFuel_length_le_measure
    (fuel : Nat) (expression : Expression) :
    (expressionDiagnosticsFuel fuel expression).length ≤
      expressionMeasure expression :=
  (diagnosticFuelBounds fuel).1 expression

/-- Recursive pattern collectors emit no more candidates than their concrete
pattern subtree contains AST carriers. -/
theorem patternDiagnosticsFuel_length_le_measure
    (fuel : Nat) (pattern : Pattern) :
    (patternDiagnosticsFuel fuel pattern).length ≤ patternMeasure pattern :=
  (diagnosticFuelBounds fuel).2.1 pattern

/-- Recursive body collectors emit no more candidates than their concrete
body subtree contains AST carriers. -/
theorem bodyDiagnosticsFuel_length_le_measure
    (fuel loopDepth : Nat) (body : Body) :
    (bodyDiagnosticsFuel fuel loopDepth body).length ≤ bodyMeasure body :=
  (diagnosticFuelBounds fuel).2.2.1 loopDepth body

/-- Recursive statement collectors emit no more candidates than their
concrete statement subtree contains AST carriers. -/
theorem statementDiagnosticsFuel_length_le_measure
    (fuel loopDepth : Nat) (statement : Statement) :
    (statementDiagnosticsFuel fuel loopDepth statement).length ≤
      statementMeasure statement :=
  (diagnosticFuelBounds fuel).2.2.2.1 loopDepth statement

/-- Recursive initializer collectors emit no more candidates than their
concrete initializer subtree contains AST carriers. -/
theorem forInitDiagnosticsFuel_length_le_measure
    (fuel : Nat) (item : ForInitItem) :
    (forInitDiagnosticsFuel fuel item).length ≤ forInitItemMeasure item :=
  (diagnosticFuelBounds fuel).2.2.2.2.1 item

/-- Recursive post-item collectors emit no more candidates than their
concrete post-item subtree contains AST carriers. -/
theorem forPostDiagnosticsFuel_length_le_measure
    (fuel : Nat) (item : ForPostItem) :
    (forPostDiagnosticsFuel fuel item).length ≤ forPostItemMeasure item :=
  (diagnosticFuelBounds fuel).2.2.2.2.2 item

private theorem duplicateDiagnosticsGo_length_le
    {alpha keyType : Type} [DecidableEq keyType]
    (key : alpha → keyType)
    (makeDiagnostic : alpha → StructuralDiagnostic)
    (seen : List keyType) (values : List alpha) :
    (duplicateDiagnostics.go key makeDiagnostic seen values).length ≤
      values.length := by
  induction values generalizing seen with
  | nil => simp [duplicateDiagnostics.go]
  | cons head tail induction =>
      simp only [duplicateDiagnostics.go]
      split
      · simp only [List.length_cons]
        have laterBound := induction (seen := key head :: seen)
        omega
      · exact Nat.le_trans (induction (seen := key head :: seen))
          (Nat.le_succ tail.length)

private theorem duplicateDiagnostics_length_le
    {alpha keyType : Type} [DecidableEq keyType]
    (key : alpha → keyType)
    (makeDiagnostic : alpha → StructuralDiagnostic)
    (values : List alpha) :
    (duplicateDiagnostics key makeDiagnostic values).length ≤ values.length := by
  exact duplicateDiagnosticsGo_length_le key makeDiagnostic [] values

private theorem mixedWildcardDiagnostic_length_le_one
    (entryCount : Nat) (spans : List SourceSpan)
    (makeDiagnostic : SourceSpan → StructuralDiagnostic) :
    (mixedWildcardDiagnostic? entryCount spans makeDiagnostic).length ≤ 1 := by
  simp only [mixedWildcardDiagnostic?]
  split
  · simp
  · cases leastSourceSpan? spans <;> simp

private theorem scaled_length_le_measureList
    {alpha : Type} (scale : Nat) (measure : alpha → Nat)
    (pointwise : ∀ value, scale ≤ measure value)
    (values : List alpha) :
    scale * values.length ≤ measureList measure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      rw [List.length_cons, Nat.mul_succ]
      simpa [measureList, Nat.add_comm] using
        Nat.add_le_add (pointwise head) induction

private theorem measureList_filterMap_le
    {alpha beta : Type} (project : alpha → Option beta)
    (sourceMeasure : alpha → Nat) (targetMeasure : beta → Nat)
    (pointwise : ∀ source target,
      project source = some target →
        targetMeasure target ≤ sourceMeasure source)
    (values : List alpha) :
    measureList targetMeasure (values.filterMap project) ≤
      measureList sourceMeasure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      cases projected : project head with
      | none =>
          simp [measureList, projected]
          exact Nat.le_trans induction
            (Nat.le_add_left _ (sourceMeasure head))
      | some target =>
          simp only [measureList, List.filterMap_cons, projected,
            List.map_cons, List.sum_cons]
          exact Nat.add_le_add (pointwise head target projected) induction

private theorem importSelectorEntryMeasure_four_le
    (entry : ImportSelectorEntry) :
    4 ≤ importSelectorEntryMeasure entry := by
  rcases entry with ⟨span, payload⟩
  cases payload with
  | wildcard marker => simp [importSelectorEntryMeasure, markerMeasure]
  | named source alias =>
      simp only [importSelectorEntryMeasure, identifierMeasure]
      omega

private theorem identifierMeasure_two_le (identifier : IdentifierOccurrence) :
    2 ≤ identifierMeasure identifier := by
  simp [identifierMeasure]

/-- Import-selection diagnostics fit within the selection's concrete AST
measure, including empty, mixed-wildcard, and both duplicate-name checks. -/
theorem importSelectionDiagnostics_length_le_measure
    (selection : ImportSelection) :
    (importSelectionDiagnostics selection).length ≤
      importSelectionMeasure selection := by
  let entries := selection.payload.entries
  let named := namedImportEntries entries
  have emptyBound :
      (if entries.isEmpty then
        [StructuralDiagnostic.emptyImportSelection selection.span]
      else []).length ≤ 1 := by
    split <;> simp
  have mixedBound := mixedWildcardDiagnostic_length_le_one
    entries.length (entries.filterMap importWildcardSpan?)
    StructuralDiagnostic.mixedImportWildcard
  have namedLengthBound : named.length ≤ entries.length := by
    exact List.length_filterMap_le _ _
  have sourcesBound := duplicateDiagnostics_length_le
    (fun entry : IdentifierOccurrence × IdentifierOccurrence => entry.1.payload)
    (fun entry => StructuralDiagnostic.duplicateImportSourceName
      entry.1.span entry.1.payload) named
  have localsBound := duplicateDiagnostics_length_le
    (fun entry : IdentifierOccurrence × IdentifierOccurrence => entry.2.payload)
    (fun entry => StructuralDiagnostic.duplicateImportLocalName
      entry.2.span entry.2.payload) named
  have entriesMeasureBound :
      4 * entries.length ≤
        measureList importSelectorEntryMeasure entries :=
    scaled_length_le_measureList 4 importSelectorEntryMeasure
      importSelectorEntryMeasure_four_le entries
  simp only [importSelectionDiagnostics, List.length_append,
    importSelectionMeasure]
  change
    (if entries.isEmpty then
      [StructuralDiagnostic.emptyImportSelection selection.span]
    else []).length +
      (mixedWildcardDiagnostic? entries.length
        (entries.filterMap importWildcardSpan?)
        StructuralDiagnostic.mixedImportWildcard).length +
      (duplicateDiagnostics
        (fun entry : IdentifierOccurrence × IdentifierOccurrence =>
          entry.1.payload)
        (fun entry => StructuralDiagnostic.duplicateImportSourceName
          entry.1.span entry.1.payload) named).length +
      (duplicateDiagnostics
        (fun entry : IdentifierOccurrence × IdentifierOccurrence =>
          entry.2.payload)
        (fun entry => StructuralDiagnostic.duplicateImportLocalName
          entry.2.span entry.2.payload) named).length ≤
      2 + measureList importSelectorEntryMeasure entries
  omega

/-- Hiding-clause diagnostics fit within the clause's concrete AST measure. -/
theorem hidingDiagnostics_length_le_measure (clause : HidingClause) :
    (hidingDiagnostics clause).length ≤ hidingClauseMeasure clause := by
  let names := clause.payload.names
  have emptyBound :
      (if names.isEmpty then
        [StructuralDiagnostic.emptyHidingClause clause.span]
      else []).length ≤ 1 := by
    split <;> simp
  have duplicatesBound := duplicateDiagnostics_length_le
    (fun name : IdentifierOccurrence => name.payload)
    (fun name => StructuralDiagnostic.duplicateHiddenName
      name.span name.payload) names
  have namesMeasureBound :
      2 * names.length ≤ measureList identifierMeasure names :=
    scaled_length_le_measureList 2 identifierMeasure
      identifierMeasure_two_le names
  simp only [hidingDiagnostics, List.length_append, hidingClauseMeasure]
  change
    (if names.isEmpty then
      [StructuralDiagnostic.emptyHidingClause clause.span]
    else []).length +
      (duplicateDiagnostics
        (fun name : IdentifierOccurrence => name.payload)
        (fun name => StructuralDiagnostic.duplicateHiddenName
          name.span name.payload) names).length ≤
      2 + measureList identifierMeasure names
  omega

/-- All diagnostics local to one import declaration fit within its concrete
AST measure. -/
theorem importDiagnostics_length_le_measure (declaration : ImportDecl) :
    (importDiagnostics declaration).length ≤ importDeclMeasure declaration := by
  rcases declaration with ⟨span, payload⟩
  rcases payload with ⟨moduleRef, mode⟩
  cases mode with
  | module alias =>
      simp [importDiagnostics, importDeclMeasure, importModeMeasure]
  | items selection hidingClause =>
      have selectionBound :=
        importSelectionDiagnostics_length_le_measure selection
      cases hidingClause with
      | none =>
          simp only [importDiagnostics, importDeclMeasure, importModeMeasure,
            List.length_append, List.length_nil]
          omega
      | some clause =>
          have hidingBound := hidingDiagnostics_length_le_measure clause
          simp only [importDiagnostics, importDeclMeasure, importModeMeasure,
            measureOption, List.length_append]
          omega

private theorem scaledLength_add_filterMapMeasure_le
    {alpha beta : Type} (scale : Nat) (project : alpha → Option beta)
    (sourceMeasure : alpha → Nat) (targetMeasure : beta → Nat)
    (noneBudget : ∀ source,
      project source = none → scale ≤ sourceMeasure source)
    (someBudget : ∀ source target,
      project source = some target →
        scale + targetMeasure target ≤ sourceMeasure source)
    (values : List alpha) :
    scale * values.length +
        measureList targetMeasure (values.filterMap project) ≤
      measureList sourceMeasure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      simp only [measureList] at induction
      cases projected : project head with
      | none =>
          simp only [List.length_cons, Nat.mul_succ, measureList,
            List.filterMap_cons, projected, List.map_cons, List.sum_cons]
          have headBound := noneBudget head projected
          omega
      | some target =>
          simp only [List.length_cons, Nat.mul_succ, measureList,
            List.filterMap_cons, projected, List.map_cons, List.sum_cons]
          have headBound := someBudget head target projected
          omega

/-- Constructor-selection duplicate diagnostics fit within the optional
selection's concrete AST measure. -/
theorem constructorSelectionDiagnostics_length_le_measureOption
    (selection : Option ConstructorSelection) :
    (constructorSelectionDiagnostics selection).length ≤
      measureOption constructorSelectionMeasure selection := by
  cases selection with
  | none => simp [constructorSelectionDiagnostics, measureOption]
  | some selection =>
      rcases selection with ⟨span, payload⟩
      cases payload with
      | all marker =>
          simp [constructorSelectionDiagnostics, measureOption,
            constructorSelectionMeasure]
      | named constructors =>
          have duplicatesBound := duplicateDiagnostics_length_le
            (fun name : IdentifierOccurrence => name.payload)
            (fun name => StructuralDiagnostic.duplicateExportConstructor
              name.span name.payload)
            (nonemptyToList constructors)
          have namesMeasureBound :
              2 * (nonemptyToList constructors).length ≤
                measureNonemptyList identifierMeasure constructors := by
            cases constructors with
            | mk head tail =>
                simp only [nonemptyToList, List.length_cons,
                  measureNonemptyList]
                have tailBound := scaled_length_le_measureList 2
                  identifierMeasure identifierMeasure_two_le tail
                simp only [identifierMeasure]
                omega
          simp only [constructorSelectionDiagnostics, measureOption,
            constructorSelectionMeasure]
          omega

/-- Diagnostics attached to one exported item fit within that item's concrete
AST measure. -/
theorem exportItemDiagnostics_length_le_measure (item : ExportItem) :
    (exportItemDiagnostics item).length ≤ exportItemMeasure item := by
  have constructorBound :=
    constructorSelectionDiagnostics_length_le_measureOption
      item.payload.constructors
  simp only [exportItemDiagnostics, exportItemMeasure]
  omega

private def localExportItemProject (entry : ExportEntry) : Option ExportItem :=
  match entry.payload with
  | .item item => some item
  | .wildcard _ | .allFrom _ _ => none

private def localExportReferenceProject
    (entry : ExportEntry) : Option ModuleReference :=
  match entry.payload with
  | .allFrom reference _ => some reference
  | .wildcard _ | .item _ => none

private theorem localExportItemBudget (entries : List ExportEntry) :
    2 * entries.length +
        measureList exportItemMeasure
          (entries.filterMap localExportItemProject) ≤
      measureList exportEntryMeasure entries := by
  apply scaledLength_add_filterMapMeasure_le 2 localExportItemProject
    exportEntryMeasure exportItemMeasure
  · intro source projectEq
    rcases source with ⟨span, payload⟩
    cases payload <;>
      simp [localExportItemProject, exportEntryMeasure] at projectEq ⊢
  · intro source target projectEq
    rcases source with ⟨span, payload⟩
    cases payload with
    | wildcard marker => simp [localExportItemProject] at projectEq
    | item item =>
        simp only [localExportItemProject, Option.some.injEq] at projectEq
        subst target
        simp [exportEntryMeasure]
    | allFrom moduleRef marker =>
        simp [localExportItemProject] at projectEq

/-- Local-export diagnostics fit within the selection's concrete AST measure. -/
theorem localExportDiagnostics_length_le_measure
    (selection : LocalExportList) :
    (localExportDiagnostics selection).length ≤
      localExportListMeasure selection := by
  let entries := selection.payload.entries
  let items := entries.filterMap localExportItemProject
  let references := entries.filterMap localExportReferenceProject
  have emptyBound :
      (if entries.isEmpty then
        [StructuralDiagnostic.emptyLocalExportList selection.span]
      else []).length ≤ 1 := by
    split <;> simp
  have mixedBound := mixedWildcardDiagnostic_length_le_one
    entries.length
    (entries.filterMap fun entry =>
      match entry.payload with
      | .wildcard marker => some marker.span
      | .item _ | .allFrom _ _ => none)
    StructuralDiagnostic.mixedExportWildcard
  have itemsLengthBound : items.length ≤ entries.length :=
    List.length_filterMap_le _ _
  have referencesLengthBound : references.length ≤ entries.length :=
    List.length_filterMap_le _ _
  have duplicateNamesBound := duplicateDiagnostics_length_le
    (fun item : ExportItem => item.payload.name.payload)
    (fun item => StructuralDiagnostic.duplicateExportName
      item.payload.name.span item.payload.name.payload) items
  have duplicateReferencesBound := duplicateDiagnostics_length_le
    ModuleReference.eraseLocations
    (fun reference => StructuralDiagnostic.duplicateExportModuleReference
      reference.span reference.eraseLocations) references
  have itemDiagnosticsBound := flatMap_length_le_measureList
    exportItemDiagnostics exportItemMeasure
    exportItemDiagnostics_length_le_measure items
  have itemBudget :
      2 * entries.length + measureList exportItemMeasure items ≤
        measureList exportEntryMeasure entries := by
    exact localExportItemBudget entries
  simp only [localExportDiagnostics, List.length_append,
    localExportListMeasure]
  change
    (if entries.isEmpty then
      [StructuralDiagnostic.emptyLocalExportList selection.span]
    else []).length +
      (mixedWildcardDiagnostic? entries.length
        (entries.filterMap fun entry =>
          match entry.payload with
          | .wildcard marker => some marker.span
          | .item _ | .allFrom _ _ => none)
        StructuralDiagnostic.mixedExportWildcard).length +
      (duplicateDiagnostics
        (fun item : ExportItem => item.payload.name.payload)
        (fun item => StructuralDiagnostic.duplicateExportName
          item.payload.name.span item.payload.name.payload) items).length +
      (duplicateDiagnostics ModuleReference.eraseLocations
        (fun reference =>
          StructuralDiagnostic.duplicateExportModuleReference
            reference.span reference.eraseLocations) references).length +
      (items.flatMap exportItemDiagnostics).length ≤
        2 + measureList exportEntryMeasure entries
  omega

private def remoteExportItemProject
    (entry : RemoteExportEntry) : Option ExportItem :=
  match entry.payload with
  | .item item => some item
  | .wildcard _ => none

private theorem remoteExportItemBudget (entries : List RemoteExportEntry) :
    entries.length +
        measureList exportItemMeasure
          (entries.filterMap remoteExportItemProject) ≤
      measureList remoteExportEntryMeasure entries := by
  simpa only [Nat.one_mul] using
    scaledLength_add_filterMapMeasure_le 1 remoteExportItemProject
      remoteExportEntryMeasure exportItemMeasure
      (by
        intro source projectEq
        rcases source with ⟨span, payload⟩
        cases payload <;>
          simp [remoteExportItemProject, remoteExportEntryMeasure]
            at projectEq ⊢ <;> omega)
      (by
        intro source target projectEq
        rcases source with ⟨span, payload⟩
        cases payload with
        | wildcard marker => simp [remoteExportItemProject] at projectEq
        | item item =>
            simp only [remoteExportItemProject, Option.some.injEq] at projectEq
            subst target
            simp [remoteExportEntryMeasure])
      entries

/-- Remote-export diagnostics fit within the selection's concrete AST measure. -/
theorem remoteExportDiagnostics_length_le_measure
    (selection : RemoteExportSelection) :
    (remoteExportDiagnostics selection).length ≤
      remoteExportSelectionMeasure selection := by
  rcases selection with ⟨span, payload⟩
  cases payload with
  | dotWildcard marker =>
      simp [remoteExportDiagnostics, remoteExportSelectionMeasure]
  | braced entries =>
      let items := entries.filterMap remoteExportItemProject
      have emptyBound :
          (if entries.isEmpty then
            [StructuralDiagnostic.emptyRemoteExportList span]
          else []).length ≤ 1 := by
        split <;> simp
      have mixedBound := mixedWildcardDiagnostic_length_le_one
        entries.length
        (entries.filterMap fun entry =>
          match entry.payload with
          | .wildcard marker => some marker.span
          | .item _ => none)
        StructuralDiagnostic.mixedExportWildcard
      have itemsLengthBound : items.length ≤ entries.length :=
        List.length_filterMap_le _ _
      have duplicateNamesBound := duplicateDiagnostics_length_le
        (fun item : ExportItem => item.payload.name.payload)
        (fun item => StructuralDiagnostic.duplicateExportName
          item.payload.name.span item.payload.name.payload) items
      have itemDiagnosticsBound := flatMap_length_le_measureList
        exportItemDiagnostics exportItemMeasure
        exportItemDiagnostics_length_le_measure items
      have itemBudget :
          entries.length + measureList exportItemMeasure items ≤
            measureList remoteExportEntryMeasure entries :=
        remoteExportItemBudget entries
      simp only [remoteExportDiagnostics, remoteExportSelectionMeasure,
        List.length_append]
      change
        (if entries.isEmpty then
          [StructuralDiagnostic.emptyRemoteExportList span]
        else []).length +
          (mixedWildcardDiagnostic? entries.length
            (entries.filterMap fun entry =>
              match entry.payload with
              | .wildcard marker => some marker.span
              | .item _ => none)
            StructuralDiagnostic.mixedExportWildcard).length +
          (duplicateDiagnostics
            (fun item : ExportItem => item.payload.name.payload)
            (fun item => StructuralDiagnostic.duplicateExportName
              item.payload.name.span item.payload.name.payload) items).length +
          (items.flatMap exportItemDiagnostics).length ≤
            2 + measureList remoteExportEntryMeasure entries
      omega

/-- All diagnostics local to one export declaration fit within its concrete
AST measure. -/
theorem exportDiagnostics_length_le_measure (declaration : ExportDecl) :
    (exportDiagnostics declaration).length ≤ exportModeMeasure declaration := by
  rcases declaration with ⟨span, mode⟩
  cases mode with
  | «local» selection =>
      have selectionBound := localExportDiagnostics_length_le_measure selection
      simp only [exportDiagnostics, exportModeMeasure]
      omega
  | module moduleRef alias =>
      simp [exportDiagnostics, exportModeMeasure]
  | «from» moduleRef selection =>
      have selectionBound := remoteExportDiagnostics_length_le_measure selection
      simp only [exportDiagnostics, exportModeMeasure]
      omega

private theorem parameterMeasure_one_le (parameter : Parameter) :
    1 ≤ parameterMeasure parameter := by
  simp only [parameterMeasure, identifierMeasure]
  omega

/-- Pragma diagnostics fit within the declaration's concrete AST measure. -/
theorem pragmaDiagnostics_length_le_measure (declaration : PragmaDecl) :
    (pragmaDiagnostics declaration).length ≤ pragmaDeclMeasure declaration := by
  let targets := declaration.payload.targets
  have emptyBound :
      (if declaration.payload.kind.payload = .noGenericInstanceFor &&
          targets.isEmpty then
        [StructuralDiagnostic.emptyGenericPragmaTargets
          declaration.payload.kind.span]
      else []).length ≤ 1 := by
    split <;> simp
  have duplicatesBound := duplicateDiagnostics_length_le
    (fun target : IdentifierOccurrence => target.payload)
    (fun target => StructuralDiagnostic.duplicatePragmaTarget
      target.span target.payload) targets
  have targetsMeasureBound :
      targets.length ≤ measureList identifierMeasure targets := by
    simpa only [Nat.one_mul] using
      scaled_length_le_measureList 1 identifierMeasure
        (fun identifier => by
          have twoLe := identifierMeasure_two_le identifier
          omega)
        targets
  simp only [pragmaDiagnostics, List.length_append, pragmaDeclMeasure]
  change
    (if declaration.payload.kind.payload = .noGenericInstanceFor &&
        targets.isEmpty then
      [StructuralDiagnostic.emptyGenericPragmaTargets
        declaration.payload.kind.span]
    else []).length +
      (duplicateDiagnostics
        (fun target : IdentifierOccurrence => target.payload)
        (fun target => StructuralDiagnostic.duplicatePragmaTarget
          target.span target.payload) targets).length ≤
      2 + pragmaKindMeasure declaration.payload.kind +
        measureList identifierMeasure targets
  omega

/-- Missing-parameter-type diagnostics fit within the concrete parameter
measure. -/
theorem missingParameterTypeDiagnostics_length_le_measureList
    (context : ParameterContext) (parameters : List Parameter) :
    (missingParameterTypeDiagnostics context parameters).length ≤
      measureList parameterMeasure parameters := by
  have lengthBound :
      (missingParameterTypeDiagnostics context parameters).length ≤
        parameters.length := by
    exact List.length_filterMap_le _ _
  have measureBound :
      parameters.length ≤ measureList parameterMeasure parameters := by
    simpa only [Nat.one_mul] using
      scaled_length_le_measureList 1 parameterMeasure
        parameterMeasure_one_le parameters
  exact Nat.le_trans lengthBound measureBound

/-- Rejected signature modifiers emit at most two diagnostics. -/
theorem disallowedSignatureModifierDiagnostics_length_le_two
    (context : ModifierContext) (signature : FunctionSignature) :
    (disallowedSignatureModifierDiagnostics context signature).length ≤ 2 := by
  simp only [disallowedSignatureModifierDiagnostics, List.length_append]
  cases signature.payload.public <;> cases signature.payload.payable <;> simp

/-- Function diagnostics fit within the declaration's concrete AST measure. -/
theorem functionDiagnostics_length_le_measure
    (fuel : Nat) (modifierContext : Option ModifierContext)
    (parameterContext : ParameterContext) (declaration : FunctionDecl) :
    (functionDiagnostics fuel modifierContext parameterContext declaration).length ≤
      functionDeclMeasure declaration := by
  let modifiers :=
    match modifierContext with
    | none => []
    | some context =>
        disallowedSignatureModifierDiagnostics context
          declaration.payload.signature
  have modifierBound : modifiers.length ≤ 2 := by
    cases modifierContext with
    | none => simp [modifiers]
    | some context =>
        exact disallowedSignatureModifierDiagnostics_length_le_two
          context declaration.payload.signature
  have parameterBound :=
    missingParameterTypeDiagnostics_length_le_measureList parameterContext
      declaration.payload.signature.payload.parameters
  have bodyBound := bodyDiagnosticsFuel_length_le_measure fuel 0
    declaration.payload.body
  simp only [functionDiagnostics, functionDeclMeasure, List.length_append]
  change
    modifiers.length +
      (missingParameterTypeDiagnostics parameterContext
        declaration.payload.signature.payload.parameters).length +
      (bodyDiagnosticsFuel fuel 0 declaration.payload.body).length ≤
      2 + functionSignatureMeasure declaration.payload.signature +
        bodyMeasure declaration.payload.body
  simp only [functionSignatureMeasure, identifierMeasure]
  omega

/-- Class-method diagnostics fit within the declaration's concrete AST
measure. -/
theorem classMethodDiagnostics_length_le_measure
    (declaration : ClassMethodDecl) :
    (classMethodDiagnostics declaration).length ≤
      classMethodDeclMeasure declaration := by
  have modifierBound :=
    disallowedSignatureModifierDiagnostics_length_le_two
      .classMethod declaration.payload.signature
  have parameterBound :=
    missingParameterTypeDiagnostics_length_le_measureList
      .classMethod declaration.payload.signature.payload.parameters
  simp only [classMethodDiagnostics, classMethodDeclMeasure,
    functionSignatureMeasure, identifierMeasure, List.length_append]
  omega

/-- Fallback diagnostics fit within the declaration's concrete AST measure. -/
theorem fallbackDiagnostics_length_le_measure
    (fuel : Nat) (declaration : FallbackDecl) :
    (fallbackDiagnostics fuel declaration).length ≤
      fallbackDeclMeasure declaration := by
  have publicBound :
      (match declaration.payload.public with
      | none => []
      | some marker =>
          [StructuralDiagnostic.modifierNotAllowed marker.span
            .fallback marker.payload]).length ≤ 1 := by
    cases declaration.payload.public <;> simp
  have parametersBound :
      (if declaration.payload.parameters.isEmpty then []
      else [StructuralDiagnostic.fallbackHasParameters
        declaration.payload.marker.span
        declaration.payload.parameters.length]).length ≤ 1 := by
    split <;> simp
  have returnBound :
      (match declaration.payload.returnType with
      | none => []
      | some expression =>
          if typeExprIsGroupedUnit expression then []
          else [StructuralDiagnostic.fallbackHasNonUnitReturn
            expression.span]).length ≤ 1 := by
    cases declaration.payload.returnType with
    | none => simp
    | some expression =>
        cases result : typeExprIsGroupedUnit expression <;> simp [result]
  have bodyBound := bodyDiagnosticsFuel_length_le_measure fuel 0
    declaration.payload.body
  simp only [fallbackDiagnostics, fallbackDeclMeasure, List.length_append]
  change
    (match declaration.payload.public with
    | none => []
    | some marker =>
        [StructuralDiagnostic.modifierNotAllowed marker.span
          .fallback marker.payload]).length +
      (if declaration.payload.parameters.isEmpty then []
      else [StructuralDiagnostic.fallbackHasParameters
        declaration.payload.marker.span
        declaration.payload.parameters.length]).length +
      (match declaration.payload.returnType with
      | none => []
      | some expression =>
          if typeExprIsGroupedUnit expression then []
          else [StructuralDiagnostic.fallbackHasNonUnitReturn
            expression.span]).length +
      (bodyDiagnosticsFuel fuel 0 declaration.payload.body).length ≤
      2 + measureOption genericPrefixMeasure declaration.payload.genericPrefix +
        measureOption markerMeasure declaration.payload.public +
        measureOption markerMeasure declaration.payload.payable +
        markerMeasure declaration.payload.marker +
        measureList parameterMeasure declaration.payload.parameters +
        measureOption typeExprMeasure declaration.payload.returnType +
        bodyMeasure declaration.payload.body
  simp only [markerMeasure]
  omega

/-- Constructor diagnostics fit within the declaration's concrete AST
measure. -/
theorem constructorDiagnostics_length_le_measure
    (fuel : Nat) (declaration : ContractConstructorDecl) :
    (constructorDiagnostics fuel declaration).length ≤
      contractConstructorDeclMeasure declaration := by
  have publicBound :
      (match declaration.payload.public with
      | none => []
      | some marker =>
          [StructuralDiagnostic.modifierNotAllowed marker.span
            .contractConstructor marker.payload]).length ≤ 1 := by
    cases declaration.payload.public <;> simp
  have parameterBound :=
    missingParameterTypeDiagnostics_length_le_measureList
      .contractConstructor declaration.payload.parameters
  have bodyBound := bodyDiagnosticsFuel_length_le_measure fuel 0
    declaration.payload.body
  simp only [constructorDiagnostics, contractConstructorDeclMeasure,
    List.length_append]
  change
    (match declaration.payload.public with
    | none => []
    | some marker =>
        [StructuralDiagnostic.modifierNotAllowed marker.span
          .contractConstructor marker.payload]).length +
      (missingParameterTypeDiagnostics .contractConstructor
        declaration.payload.parameters).length +
      (bodyDiagnosticsFuel fuel 0 declaration.payload.body).length ≤
      2 + measureOption markerMeasure declaration.payload.public +
        measureOption markerMeasure declaration.payload.payable +
        markerMeasure declaration.payload.marker +
        measureList parameterMeasure declaration.payload.parameters +
        bodyMeasure declaration.payload.body
  simp only [markerMeasure]
  omega

/-- Diagnostics rooted at one contract member fit within that member's
concrete AST measure. -/
theorem contractMemberDiagnostics_length_le_measure
    (fuel : Nat) (member : ContractMember) :
    (contractMemberDiagnostics fuel member).length ≤
      contractMemberMeasure member := by
  rcases member with ⟨span, payload⟩
  cases payload with
  | dataDecl declaration =>
      simp [contractMemberDiagnostics, contractMemberMeasure]
  | typeAlias declaration =>
      simp [contractMemberDiagnostics, contractMemberMeasure]
  | field declaration =>
      rcases declaration with ⟨declarationSpan, declarationPayload⟩
      rcases declarationPayload with ⟨name, typeExpression, initializer⟩
      cases initializer with
      | none =>
          simp [contractMemberDiagnostics, contractMemberMeasure,
            fieldDeclMeasure]
      | some expression =>
          have expressionBound :=
            expressionDiagnosticsFuel_length_le_measure fuel expression
          simp only [contractMemberDiagnostics, contractMemberMeasure,
            fieldDeclMeasure, measureOption]
          omega
  | «function» declaration =>
      have functionBound := functionDiagnostics_length_le_measure fuel none
        .contractFunction declaration
      simp only [contractMemberDiagnostics, contractMemberMeasure]
      omega
  | fallback declaration =>
      have fallbackBound := fallbackDiagnostics_length_le_measure fuel declaration
      simp only [contractMemberDiagnostics, contractMemberMeasure]
      omega
  | «constructor» declaration =>
      have constructorBound :=
        constructorDiagnostics_length_le_measure fuel declaration
      simp only [contractMemberDiagnostics, contractMemberMeasure]
      omega

/-- Contract diagnostics fit within the declaration's concrete AST measure. -/
theorem contractDiagnostics_length_le_measure
    (fuel : Nat) (declaration : ContractDecl) :
    (contractDiagnostics fuel declaration).length ≤
      contractDeclMeasure declaration := by
  have membersBound := flatMap_length_le_measureList
    (contractMemberDiagnostics fuel) contractMemberMeasure
    (contractMemberDiagnostics_length_le_measure fuel)
    declaration.payload.members
  simp only [contractDiagnostics, contractDeclMeasure]
  omega

/-- Diagnostics rooted at one top-level item fit within that item's concrete
AST measure. -/
theorem topItemDiagnostics_length_le_measure
    (fuel : Nat) (item : TopItem) :
    (topItemDiagnostics fuel item).length ≤ topItemMeasure item := by
  rcases item with ⟨span, payload⟩
  cases payload with
  | importDecl declaration =>
      have importBound := importDiagnostics_length_le_measure declaration
      simp only [topItemDiagnostics, topItemMeasure]
      omega
  | exportDecl declaration =>
      have exportBound := exportDiagnostics_length_le_measure declaration
      simp only [topItemDiagnostics, topItemMeasure]
      omega
  | pragmaDecl declaration =>
      have pragmaBound := pragmaDiagnostics_length_le_measure declaration
      simp only [topItemDiagnostics, topItemMeasure]
      omega
  | dataDecl declaration =>
      simp [topItemDiagnostics, topItemMeasure]
  | typeAliasDecl declaration =>
      simp [topItemDiagnostics, topItemMeasure]
  | classDecl declaration =>
      have methodsBound := flatMap_length_le_measureList
        classMethodDiagnostics classMethodDeclMeasure
        classMethodDiagnostics_length_le_measure declaration.payload.methods
      simp only [topItemDiagnostics, topItemMeasure, classDeclMeasure]
      omega
  | instanceDecl declaration =>
      have methodsBound := flatMap_length_le_measureList
        (functionDiagnostics fuel (some .instanceMethod) .instanceMethod)
        functionDeclMeasure
        (functionDiagnostics_length_le_measure fuel (some .instanceMethod)
          .instanceMethod)
        declaration.payload.methods
      simp only [topItemDiagnostics, topItemMeasure, instanceDeclMeasure]
      omega
  | contractDecl declaration =>
      have contractBound := contractDiagnostics_length_le_measure fuel declaration
      simp only [topItemDiagnostics, topItemMeasure]
      omega
  | functionDecl declaration =>
      have functionBound := functionDiagnostics_length_le_measure fuel
        (some .topLevelFunction) .topLevelFunction declaration
      simp only [topItemDiagnostics, topItemMeasure]
      omega

/-- The complete pre-canonical diagnostic stream fits within the module's
concrete AST measure. -/
theorem diagnosticCandidates_length_le_astNodeMeasure
    (module : ParsedModuleV1) :
    (diagnosticCandidates module).length ≤ astNodeMeasure module := by
  let fuel := astNodeMeasure module + 1
  have itemsBound := flatMap_length_le_measureList
    (topItemDiagnostics fuel) topItemMeasure
    (topItemDiagnostics_length_le_measure fuel) module.payload.items
  simp only [diagnosticCandidates, astNodeMeasure]
  change
    (module.payload.items.flatMap (topItemDiagnostics fuel)).length ≤
      2 + measureList topItemMeasure module.payload.items
  omega

end Structure

/-- The executable diagnostic-insertion counter is bounded by the module's
concrete AST-node count. -/
theorem structureDiagnosticInsertionUnits_le_astNodeMeasure
    (module : ParsedModuleV1) :
    structureDiagnosticInsertionUnits module ≤ astNodeMeasure module := by
  rw [structureDiagnosticInsertionUnits_eq_candidates_length]
  exact Structure.diagnosticCandidates_length_le_astNodeMeasure module

end Solcore.Surface.Multi
