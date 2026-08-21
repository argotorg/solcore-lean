import Solcore.Surface.Multi.ParserCore

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-- The phase-specific source of one reference-chart key. -/
inductive ChartSourceTag (tokens : List Token) where
  | rawEvidence
  | contextual (context : GuardContext tokens)
  deriving Repr, BEq, DecidableEq

/-- One coordinate in the linear reference-chart key universe. -/
structure ChartLinearKey (tokens : List Token) where
  source : ChartSourceTag tokens
  dotted : DottedRhs
  origin : Boundary tokens
  current : Boundary tokens
  deriving Repr, BEq, DecidableEq

/-- One coordinate in the prediction reference-chart key universe. -/
structure ChartPredictionKey (tokens : List Token) where
  source : ChartSourceTag tokens
  dotted : DottedRhs
  production : ProductionId
  origin : Boundary tokens
  current : Boundary tokens
  deriving Repr, BEq, DecidableEq

/-- One coordinate in the cubic reference-chart key universe. -/
structure ChartCubicKey (tokens : List Token) where
  source : ChartSourceTag tokens
  waiting : DottedRhs
  finished : DottedRhs
  origin : Boundary tokens
  shared : Boundary tokens
  current : Boundary tokens
  deriving Repr, BEq, DecidableEq

/-- The four disjoint Phase-A evidence-index families. -/
inductive EvidenceIndexKind where
  | terminalWindow
  | exactSlice
  | greatestEnd
  | delimiterOrRegion
  deriving Repr, BEq, DecidableEq

/-- The eight once-only Phase-B slots for one guard instance. -/
inductive GuardFinalizeSlot where
  | initializeUndecided
  | siteTerminalLookup
  | adjacentTerminalWindowLookup
  | exactSliceLookup
  | unguardedSpanLookup
  | greatestEndLookup
  | delimiterOrRegionLookup
  | writeFinalDecision
  deriving Repr, BEq, DecidableEq

/-- The four global phase-transition slots of the reference chart. -/
inductive ChartPhaseSlot where
  | initializePhaseA
  | sealAEnterB
  | sealBEnterC
  | selectFinalOutcome
  deriving Repr, BEq, DecidableEq

/-- The four once-only Phase-C slots for one guarded production cell. -/
inductive GuardWitnessSlot where
  | constructAnchor
  | lookupFinalDecision
  | comparePolarity
  | insertWitness
  deriving Repr, BEq, DecidableEq

/-- The fourteen tagged unit families charged to a linear chart key. -/
inductive ChartLinearUnitKind where
  | L01_itemDequeue
  | L02_scannedEdgeDequeue
  | L03_itemInsert
  | L04_scanAttempt
  | L05_scannedItemInsert
  | L06_scannedEdgeInsert
  | L07_completedItemInsert
  | L08_frontierDequeue
  | L09_frontierInsert
  | L10_expectedCandidate
  | L11_foundCandidate
  | L12_scannedAction
  | L13_epsilonAction
  | L14_frontierScannedTraversal
  deriving Repr, BEq, DecidableEq

/-- The two tagged unit families charged to a prediction chart key. -/
inductive ChartPredictionUnitKind where
  | R01_predictionAttempt
  | R02_frontierPrediction
  deriving Repr, BEq, DecidableEq

/-- The eight tagged unit families charged to a cubic chart key. -/
inductive ChartCubicUnitKind where
  | U01_evidenceIndex
  | U02_completedEdgeDequeue
  | U03_completionAttempt
  | U04_completedEdgeInsert
  | U05_completedAction
  | U06_frontierCompletion
  | U07_frontierCompletedTraversal
  | U08_G10Candidate
  deriving Repr, BEq, DecidableEq

private theorem enumeration_cardinality
    {α : Type} [BEq α] [LawfulBEq α]
    (values : List α)
    (complete : ∀ value : α, value ∈ values)
    (unique : values.Nodup) :
    ∃ encode : α → Fin values.length,
      Function.Injective encode ∧ Function.Surjective encode := by
  let encode : α → Fin values.length := fun value =>
    ⟨values.idxOf value, List.idxOf_lt_length_of_mem (complete value)⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    have leftBound : values.idxOf left < values.length :=
      List.idxOf_lt_length_of_mem (complete left)
    have rightBound : values.idxOf right < values.length :=
      List.idxOf_lt_length_of_mem (complete right)
    have leftSelected : values[values.idxOf left]'leftBound = left := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == left)) (w := leftBound))
    have rightSelected : values[values.idxOf right]'rightBound = right := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == right)) (w := rightBound))
    have sameSelected :
        values[values.idxOf left]'leftBound =
          values[values.idxOf right]'rightBound :=
      congrArg values.get equal
    exact leftSelected.symm.trans (sameSelected.trans rightSelected)
  · intro index
    let value := values[index]
    refine ⟨value, Fin.ext ?_⟩
    change values.idxOf value = index.val
    have valueBound : values.idxOf value < values.length :=
      List.idxOf_lt_length_of_mem (complete value)
    apply (List.getElem?_inj valueBound unique).mp
    rw [List.getElem?_eq_getElem valueBound,
      List.getElem?_eq_getElem index.isLt]
    have selected : values[values.idxOf value]'valueBound = value := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == value)) (w := valueBound))
    simpa [value] using congrArg some selected

private theorem productionId_cardinality :
    ∃ encode : ProductionId → Fin productionCount,
      Function.Injective encode ∧ Function.Surjective encode := by
  rw [ebnf_expansion_finite.2.2]
  exact enumeration_cardinality allProductionIds
    allProductionIds_complete allProductionIds_nodup

private theorem block_encode_injective
    {width leftBlock rightBlock leftOffset rightOffset : Nat}
    (leftBound : leftOffset < width)
    (rightBound : rightOffset < width)
    (equal : leftBlock * width + leftOffset =
      rightBlock * width + rightOffset) :
    leftBlock = rightBlock ∧ leftOffset = rightOffset := by
  have positive : 0 < width := Nat.zero_lt_of_lt leftBound
  have quotient (block offset : Nat) (bound : offset < width) :
      (block * width + offset) / width = block := by
    rw [Nat.add_comm, Nat.mul_comm block width,
      Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bound]
    exact Nat.zero_add block
  have blockEqual : leftBlock = rightBlock := by
    rw [← quotient leftBlock leftOffset leftBound, equal,
      quotient rightBlock rightOffset rightBound]
  exact ⟨blockEqual, by
    rw [blockEqual] at equal
    exact Nat.add_left_cancel equal⟩

private theorem product_cardinality
    {α β : Type} {leftSize rightSize : Nat}
    (rightPositive : 0 < rightSize)
    (leftCardinality :
      ∃ encode : α → Fin leftSize,
        Function.Injective encode ∧ Function.Surjective encode)
    (rightCardinality :
      ∃ encode : β → Fin rightSize,
        Function.Injective encode ∧ Function.Surjective encode) :
    ∃ encode : α × β → Fin (leftSize * rightSize),
      Function.Injective encode ∧ Function.Surjective encode := by
  obtain ⟨leftEncode, leftInjective, leftSurjective⟩ := leftCardinality
  obtain ⟨rightEncode, rightInjective, rightSurjective⟩ :=
    rightCardinality
  let encode (value : α × β) : Fin (leftSize * rightSize) :=
    ⟨(leftEncode value.1).val * rightSize +
        (rightEncode value.2).val, by
      have rowBound :
          (leftEncode value.1).val * rightSize +
              (rightEncode value.2).val <
            ((leftEncode value.1).val + 1) * rightSize := by
        rw [Nat.add_mul]
        simpa only [Nat.one_mul] using Nat.add_lt_add_left
          (rightEncode value.2).isLt
          ((leftEncode value.1).val * rightSize)
      exact Nat.lt_of_lt_of_le rowBound
        (Nat.mul_le_mul_right rightSize
          (Nat.succ_le_of_lt (leftEncode value.1).isLt))⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    have rawEqual := congrArg Fin.val equal
    have coordinates := block_encode_injective
      (rightEncode left.2).isLt (rightEncode right.2).isLt rawEqual
    exact Prod.ext (leftInjective (Fin.ext coordinates.1))
      (rightInjective (Fin.ext coordinates.2))
  · intro value
    let leftIndex : Fin leftSize :=
      ⟨value.val / rightSize,
        (Nat.div_lt_iff_lt_mul rightPositive).mpr value.isLt⟩
    let rightIndex : Fin rightSize :=
      ⟨value.val % rightSize, Nat.mod_lt _ rightPositive⟩
    obtain ⟨left, leftEqual⟩ := leftSurjective leftIndex
    obtain ⟨right, rightEqual⟩ := rightSurjective rightIndex
    refine ⟨(left, right), Fin.ext ?_⟩
    simp only [encode]
    rw [leftEqual, rightEqual]
    simpa [leftIndex, rightIndex, Nat.add_comm, Nat.mul_comm] using
      Nat.mod_add_div value.val rightSize

private theorem fin_cardinality (size : Nat) :
    ∃ encode : Fin size → Fin size,
      Function.Injective encode ∧ Function.Surjective encode :=
  ⟨id, Function.injective_id, Function.surjective_id⟩

private theorem transport_cardinality
    {α β : Type} {size : Nat}
    (toCoordinates : α → β) (fromCoordinates : β → α)
    (leftInverse : Function.LeftInverse fromCoordinates toCoordinates)
    (rightInverse : Function.RightInverse fromCoordinates toCoordinates)
    (cardinality : ∃ encode : β → Fin size,
      Function.Injective encode ∧ Function.Surjective encode) :
    ∃ encode : α → Fin size,
      Function.Injective encode ∧ Function.Surjective encode := by
  obtain ⟨encode, injective, surjective⟩ := cardinality
  refine ⟨encode ∘ toCoordinates, injective.comp leftInverse.injective, ?_⟩
  intro value
  obtain ⟨coordinates, equal⟩ := surjective value
  exact ⟨fromCoordinates coordinates, by
    simpa [Function.comp_apply, rightInverse coordinates] using equal⟩

private theorem chartSourceTag_cardinality (tokens : List Token) :
    ∃ encode : ChartSourceTag tokens →
        Fin (1 + (1 + 3 * (tokens.length + 2))),
      Function.Injective encode ∧ Function.Surjective encode := by
  obtain ⟨contextEncode, contextInjective, contextSurjective⟩ :=
    guard_context_cardinality tokens
  let encode : ChartSourceTag tokens →
      Fin (1 + (1 + 3 * (tokens.length + 2)))
    | .rawEvidence => ⟨0, by omega⟩
    | .contextual context => ⟨contextEncode context + 1, by
        have := (contextEncode context).isLt
        omega⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    cases left with
    | rawEvidence =>
        cases right <;> simp only [encode, Fin.mk.injEq] at equal ⊢
        omega
    | contextual leftContext =>
        cases right with
        | rawEvidence =>
            simp only [encode, Fin.mk.injEq] at equal
            omega
        | contextual rightContext =>
            simp only [encode, Fin.mk.injEq] at equal
            congr 1
            apply contextInjective
            apply Fin.ext
            omega
  · intro value
    by_cases raw : value.val = 0
    · exact ⟨.rawEvidence, Fin.ext (by simp [encode, raw])⟩
    · let contextIndex : Fin (1 + 3 * (tokens.length + 2)) :=
        ⟨value.val - 1, by have := value.isLt; omega⟩
      obtain ⟨context, equal⟩ := contextSurjective contextIndex
      refine ⟨.contextual context, Fin.ext ?_⟩
      have rawPositive : 0 < value.val := Nat.pos_of_ne_zero raw
      have := congrArg Fin.val equal
      simp only [encode]
      dsimp only [contextIndex] at this
      omega

private theorem dotted_count_positive : 0 < D := by
  let dotted : DottedRhs := {
    production := .root .module
    dot := ⟨0, Nat.zero_lt_succ _⟩
  }
  have member := allDottedRhs_complete dotted
  have positive : 0 < allDottedRhs.length :=
    List.length_pos_of_mem member
  simpa [allDottedRhs_length] using positive

private theorem production_count_positive : 0 < productionCount := by
  rw [ebnf_expansion_finite.2.2]
  exact List.length_pos_of_mem (allProductionIds_complete (.root .module))

private abbrev LinearCoordinates (tokens : List Token) :=
  ((ChartSourceTag tokens × DottedRhs) × Boundary tokens) × Boundary tokens

private abbrev PredictionCoordinates (tokens : List Token) :=
  (((ChartSourceTag tokens × DottedRhs) × ProductionId) × Boundary tokens) ×
    Boundary tokens

private abbrev CubicCoordinates (tokens : List Token) :=
  ((((ChartSourceTag tokens × DottedRhs) × DottedRhs) × Boundary tokens) ×
    Boundary tokens) × Boundary tokens

private def linearCoordinates {tokens : List Token}
    (key : ChartLinearKey tokens) : LinearCoordinates tokens :=
  (((key.source, key.dotted), key.origin), key.current)

private def linearKey {tokens : List Token}
    (coordinates : LinearCoordinates tokens) : ChartLinearKey tokens :=
  ⟨coordinates.1.1.1, coordinates.1.1.2, coordinates.1.2, coordinates.2⟩

private def predictionCoordinates {tokens : List Token}
    (key : ChartPredictionKey tokens) : PredictionCoordinates tokens :=
  ((((key.source, key.dotted), key.production), key.origin), key.current)

private def predictionKey {tokens : List Token}
    (coordinates : PredictionCoordinates tokens) : ChartPredictionKey tokens :=
  ⟨coordinates.1.1.1.1, coordinates.1.1.1.2, coordinates.1.1.2,
    coordinates.1.2, coordinates.2⟩

private def cubicCoordinates {tokens : List Token}
    (key : ChartCubicKey tokens) : CubicCoordinates tokens :=
  (((((key.source, key.waiting), key.finished), key.origin), key.shared),
    key.current)

private def cubicKey {tokens : List Token}
    (coordinates : CubicCoordinates tokens) : ChartCubicKey tokens :=
  ⟨coordinates.1.1.1.1.1, coordinates.1.1.1.1.2,
    coordinates.1.1.1.2, coordinates.1.1.2, coordinates.1.2, coordinates.2⟩

private theorem chart_key_cardinality (tokens : List Token) :
    (∃ encode : ChartSourceTag tokens →
        Fin (1 + (1 + 3 * (tokens.length + 2))),
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartLinearKey tokens →
        Fin ((1 + (1 + 3 * (tokens.length + 2))) * D *
          (tokens.length + 2) * (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartPredictionKey tokens →
        Fin ((1 + (1 + 3 * (tokens.length + 2))) * D * productionCount *
          (tokens.length + 2) * (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartCubicKey tokens →
        Fin ((1 + (1 + 3 * (tokens.length + 2))) * D * D *
          (tokens.length + 2) * (tokens.length + 2) * (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode) := by
  let sourceCardinality := chartSourceTag_cardinality tokens
  let boundaryCardinality := fin_cardinality (tokens.length + 2)
  let sourceDottedCardinality := product_cardinality dotted_count_positive
    sourceCardinality dottedRhs_cardinality
  let linearCoordinatesCardinality := product_cardinality (by omega)
    (product_cardinality (by omega) sourceDottedCardinality boundaryCardinality)
    boundaryCardinality
  let sourceDottedProductionCardinality :=
    product_cardinality production_count_positive sourceDottedCardinality
      productionId_cardinality
  let predictionCoordinatesCardinality := product_cardinality (by omega)
    (product_cardinality (by omega) sourceDottedProductionCardinality
      boundaryCardinality) boundaryCardinality
  let sourceDottedDottedCardinality := product_cardinality dotted_count_positive
    sourceDottedCardinality dottedRhs_cardinality
  let cubicCoordinatesCardinality := product_cardinality (by omega)
    (product_cardinality (by omega)
      (product_cardinality (by omega) sourceDottedDottedCardinality
        boundaryCardinality) boundaryCardinality) boundaryCardinality
  refine ⟨sourceCardinality, ?_, ?_, ?_⟩
  · exact transport_cardinality linearCoordinates linearKey
      (by intro key; cases key; rfl)
      (by intro coordinates; rcases coordinates with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl)
      linearCoordinatesCardinality
  · exact transport_cardinality predictionCoordinates predictionKey
      (by intro key; cases key; rfl)
      (by rintro ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩; rfl)
      predictionCoordinatesCardinality
  · exact transport_cardinality cubicCoordinates cubicKey
      (by intro key; cases key; rfl)
      (by rintro ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩; rfl)
      cubicCoordinatesCardinality

private theorem sum_cardinality
    {α β : Type} {leftSize rightSize : Nat}
    (leftCardinality :
      ∃ encode : α → Fin leftSize,
        Function.Injective encode ∧ Function.Surjective encode)
    (rightCardinality :
      ∃ encode : β → Fin rightSize,
        Function.Injective encode ∧ Function.Surjective encode) :
    ∃ encode : α ⊕ β → Fin (leftSize + rightSize),
      Function.Injective encode ∧ Function.Surjective encode := by
  obtain ⟨leftEncode, leftInjective, leftSurjective⟩ := leftCardinality
  obtain ⟨rightEncode, rightInjective, rightSurjective⟩ :=
    rightCardinality
  let encode : α ⊕ β → Fin (leftSize + rightSize)
    | .inl value => ⟨(leftEncode value).val,
        Nat.lt_of_lt_of_le (leftEncode value).isLt
          (Nat.le_add_right leftSize rightSize)⟩
    | .inr value => ⟨leftSize + (rightEncode value).val, by
        have := (rightEncode value).isLt
        omega⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    cases left with
    | inl leftValue =>
        cases right with
        | inl rightValue =>
            have rawEqual := congrArg Fin.val equal
            simp only [encode] at rawEqual
            exact congrArg Sum.inl
              (leftInjective (Fin.ext rawEqual))
        | inr rightValue =>
            have rawEqual := congrArg Fin.val equal
            have leftBound := (leftEncode leftValue).isLt
            simp only [encode] at rawEqual
            omega
    | inr leftValue =>
        cases right with
        | inl rightValue =>
            have rawEqual := congrArg Fin.val equal
            have rightBound := (leftEncode rightValue).isLt
            simp only [encode] at rawEqual
            omega
        | inr rightValue =>
            have rawEqual := congrArg Fin.val equal
            simp only [encode] at rawEqual
            exact congrArg Sum.inr
              (rightInjective (Fin.ext (Nat.add_left_cancel rawEqual)))
  · intro index
    by_cases inLeft : index.val < leftSize
    · let leftIndex : Fin leftSize := ⟨index.val, inLeft⟩
      obtain ⟨value, equal⟩ := leftSurjective leftIndex
      refine ⟨.inl value, Fin.ext ?_⟩
      simpa [encode, leftIndex] using congrArg Fin.val equal
    · have leftLower : leftSize ≤ index.val := Nat.le_of_not_gt inLeft
      let rightIndex : Fin rightSize := ⟨index.val - leftSize, by
        have := index.isLt
        omega⟩
      obtain ⟨value, equal⟩ := rightSurjective rightIndex
      refine ⟨.inr value, Fin.ext ?_⟩
      have rawEqual := congrArg Fin.val equal
      simp only [encode]
      dsimp only [rightIndex] at rawEqual
      omega

private instance : LawfulBEq ChartPhaseSlot where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq GuardFinalizeSlot where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq GuardWitnessSlot where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq ChartLinearUnitKind where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq ChartPredictionUnitKind where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq ChartCubicUnitKind where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private theorem chart_unit_kind_cardinality :
    (∃ encode : ChartPhaseSlot → Fin 4,
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : GuardFinalizeSlot → Fin 8,
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : GuardWitnessSlot → Fin 4,
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartLinearUnitKind → Fin 14,
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartPredictionUnitKind → Fin 2,
      Function.Injective encode ∧ Function.Surjective encode) ∧
    (∃ encode : ChartCubicUnitKind → Fin 8,
      Function.Injective encode ∧ Function.Surjective encode) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using enumeration_cardinality
      ([.initializePhaseA, .sealAEnterB, .sealBEnterC,
        .selectFinalOutcome] : List ChartPhaseSlot)
      (by intro slot; cases slot <;> simp) (by decide)
  · simpa using enumeration_cardinality
      ([.initializeUndecided, .siteTerminalLookup,
        .adjacentTerminalWindowLookup, .exactSliceLookup,
        .unguardedSpanLookup, .greatestEndLookup,
        .delimiterOrRegionLookup, .writeFinalDecision] :
        List GuardFinalizeSlot)
      (by intro slot; cases slot <;> simp) (by decide)
  · simpa using enumeration_cardinality
      ([.constructAnchor, .lookupFinalDecision, .comparePolarity,
        .insertWitness] : List GuardWitnessSlot)
      (by intro slot; cases slot <;> simp) (by decide)
  · simpa using enumeration_cardinality
      ([.L01_itemDequeue, .L02_scannedEdgeDequeue, .L03_itemInsert,
        .L04_scanAttempt, .L05_scannedItemInsert, .L06_scannedEdgeInsert,
        .L07_completedItemInsert, .L08_frontierDequeue,
        .L09_frontierInsert, .L10_expectedCandidate, .L11_foundCandidate,
        .L12_scannedAction, .L13_epsilonAction,
        .L14_frontierScannedTraversal] : List ChartLinearUnitKind)
      (by intro kind; cases kind <;> simp) (by decide)
  · simpa using enumeration_cardinality
      ([.R01_predictionAttempt, .R02_frontierPrediction] :
        List ChartPredictionUnitKind)
      (by intro kind; cases kind <;> simp) (by decide)
  · simpa using enumeration_cardinality
      ([.U01_evidenceIndex, .U02_completedEdgeDequeue,
        .U03_completionAttempt, .U04_completedEdgeInsert,
        .U05_completedAction, .U06_frontierCompletion,
        .U07_frontierCompletedTraversal, .U08_G10Candidate] :
        List ChartCubicUnitKind)
      (by intro kind; cases kind <;> simp) (by decide)

private theorem dependentEnumeration_nodup
    {α γ : Type} {β : α → Type}
    (values : List α) (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (valuesUnique : values.Nodup)
    (itemsUnique : ∀ value, (items value).Nodup)
    (makeInjective : ∀ {left right} {leftItem : β left}
      {rightItem : β right},
      make left leftItem = make right rightItem →
        Sigma.mk left leftItem = Sigma.mk right rightItem) :
    (values.flatMap fun value =>
      (items value).map (make value)).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesUnique
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      have mappedUnique : ((items head).map (make head)).Nodup := by
        rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact (itemsUnique head).imp fun different equal =>
          different (eq_of_heq
            (Sigma.ext_iff.mp (makeInjective equal)).2)
      refine ⟨mappedUnique, induction valuesUnique.2, ?_⟩
      intro left leftMember right rightMember equal
      rw [List.mem_map] at leftMember
      rcases leftMember with ⟨leftItem, _, rfl⟩
      rw [List.mem_flatMap] at rightMember
      rcases rightMember with ⟨owner, ownerMember, rightMember⟩
      rw [List.mem_map] at rightMember
      rcases rightMember with ⟨rightItem, _, rfl⟩
      have ownerEqual := congrArg Sigma.fst (makeInjective equal)
      change head = owner at ownerEqual
      exact valuesUnique.1 (ownerEqual.symm ▸ ownerMember)

private abbrev GuardCellAddress :=
  Sigma fun production : ProductionId => Fin (guardOf production).length

private def allGuardCellAddresses : List GuardCellAddress :=
  allProductionIds.flatMap fun production =>
    (List.ofFn fun cell : Fin (guardOf production).length => cell).map
      (Sigma.mk production)

private theorem allGuardCellAddresses_complete
    (address : GuardCellAddress) : address ∈ allGuardCellAddresses := by
  rcases address with ⟨production, cell⟩
  rw [allGuardCellAddresses, List.mem_flatMap]
  refine ⟨production, allProductionIds_complete production, ?_⟩
  rw [List.mem_map]
  exact ⟨cell, List.mem_ofFn.mpr ⟨cell, rfl⟩, rfl⟩

private theorem allGuardCellAddresses_nodup :
    allGuardCellAddresses.Nodup := by
  apply dependentEnumeration_nodup allProductionIds
    (fun production =>
      List.ofFn fun cell : Fin (guardOf production).length => cell)
    (fun production cell => Sigma.mk production cell)
    allProductionIds_nodup
  · intro production
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro left right _ _ before equal
    simp only [List.getElem_ofFn] at equal
    have sameValue : left = right := congrArg Fin.val equal
    omega
  · intro left right leftCell rightCell equal
    exact equal

private theorem allGuardCellAddresses_length :
    allGuardCellAddresses.length = H := by
  simp [allGuardCellAddresses, H]

private theorem guardCellAddress_cardinality :
    ∃ encode : GuardCellAddress → Fin H,
      Function.Injective encode ∧ Function.Surjective encode := by
  rw [← allGuardCellAddresses_length]
  exact enumeration_cardinality allGuardCellAddresses
    allGuardCellAddresses_complete allGuardCellAddresses_nodup

private theorem cast_cardinality
    {α : Type} {sourceSize targetSize : Nat}
    (sizesEqual : sourceSize = targetSize)
    (cardinality : ∃ encode : α → Fin sourceSize,
      Function.Injective encode ∧ Function.Surjective encode) :
    ∃ encode : α → Fin targetSize,
      Function.Injective encode ∧ Function.Surjective encode := by
  cases sizesEqual
  exact cardinality

private theorem cast_injection
    {α : Type} {sourceSize targetSize : Nat}
    (atMost : sourceSize ≤ targetSize)
    (injection : ∃ encode : α → Fin sourceSize,
      Function.Injective encode) :
    ∃ encode : α → Fin targetSize, Function.Injective encode := by
  obtain ⟨encode, injective⟩ := injection
  refine ⟨fun value => Fin.castLE atMost (encode value), ?_⟩
  intro left right equal
  apply injective
  apply Fin.ext
  have rawEqual := congrArg Fin.val equal
  simp only [Fin.castLE] at rawEqual
  exact rawEqual

end Solcore.Surface.Multi
