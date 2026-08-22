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

private def rootDottedZero (rule : GrammarRuleId) : DottedRhs := {
  production := .root rule
  dot := ⟨0, by simp [ProductionId.rhs]⟩
}

private def rootDottedOne (rule : GrammarRuleId) : DottedRhs := {
  production := .root rule
  dot := ⟨1, by simp [ProductionId.rhs]⟩
}

/-- Rules use root dot zero; guards use nine fixed root dot-one schemas. -/
private def evidenceSubjectDotted :
    PriorityGuardId ⊕ GrammarRuleId → DottedRhs
  | .inl .G01_statementIf => rootDottedOne .module
  | .inl .G02_matchArmBoundary => rootDottedOne .topItem
  | .inl .G03_parameterComptime => rootDottedOne .moduleRef
  | .inl .G04_letComptime => rootDottedOne .importDecl
  | .inl .G05_typeComptime => rootDottedOne .importEntry
  | .inl .G06_patternComptime => rootDottedOne .hidingClause
  | .inl .G07_leadingDotArguments => rootDottedOne .exportDecl
  | .inl .G08_terminalExpression => rootDottedOne .localExportEntry
  | .inl .G09_genericContext => rootDottedOne .remoteExportEntry
  | .inr rule => rootDottedZero rule

private theorem evidenceSubjectDotted_injective :
    Function.Injective evidenceSubjectDotted := by
  intro left right equal
  cases left with
  | inl leftGuard =>
      cases right with
      | inl rightGuard =>
          cases leftGuard <;> cases rightGuard <;>
            simp_all [evidenceSubjectDotted, rootDottedOne]
      | inr rightRule =>
          cases leftGuard <;>
            simp_all [evidenceSubjectDotted, rootDottedOne,
              rootDottedZero]
  | inr leftRule =>
      cases right with
      | inl rightGuard =>
          cases rightGuard <;>
            simp_all [evidenceSubjectDotted, rootDottedOne,
              rootDottedZero]
      | inr rightRule =>
          simp_all [evidenceSubjectDotted, rootDottedZero]

/-- The four index kinds use four distinct fixed root schemas. -/
private def evidenceKindDotted : EvidenceIndexKind → DottedRhs
  | .terminalWindow => rootDottedZero .module
  | .exactSlice => rootDottedZero .topItem
  | .greatestEnd => rootDottedZero .moduleRef
  | .delimiterOrRegion => rootDottedZero .importDecl

private theorem evidenceKindDotted_injective :
    Function.Injective evidenceKindDotted := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [evidenceKindDotted, rootDottedZero]

private structure EvidenceIndexAddress (tokens : List Token) where
  kind : EvidenceIndexKind
  subject : PriorityGuardId ⊕ GrammarRuleId
  contextStart : Boundary tokens
  siteCursor : Boundary tokens
  resultEnd : Boundary tokens

/-- Explicit U01 embedding, with raw Phase-A source and three boundaries. -/
private def evidenceIndexKey {tokens : List Token}
    (address : EvidenceIndexAddress tokens) : ChartCubicKey tokens := {
  source := .rawEvidence
  waiting := evidenceSubjectDotted address.subject
  finished := evidenceKindDotted address.kind
  origin := address.contextStart
  shared := address.siteCursor
  current := address.resultEnd
}

private theorem EvidenceIndexAddress.eq_of_fields
    {tokens : List Token} {left right : EvidenceIndexAddress tokens}
    (kind : left.kind = right.kind)
    (subject : left.subject = right.subject)
    (contextStart : left.contextStart = right.contextStart)
    (siteCursor : left.siteCursor = right.siteCursor)
    (resultEnd : left.resultEnd = right.resultEnd) : left = right := by
  cases left
  cases right
  simp only at kind subject contextStart siteCursor resultEnd
  cases kind
  cases subject
  cases contextStart
  cases siteCursor
  cases resultEnd
  rfl

/-- Distinct evidence-index candidates cannot consume one U01 address. -/
private theorem evidenceIndexKey_injective :
    ∀ {tokens : List Token},
      Function.Injective (@evidenceIndexKey tokens) := by
  intro tokens
  intro left right equal
  apply EvidenceIndexAddress.eq_of_fields
  · apply evidenceKindDotted_injective
    exact congrArg ChartCubicKey.finished equal
  · apply evidenceSubjectDotted_injective
    exact congrArg ChartCubicKey.waiting equal
  · exact congrArg ChartCubicKey.origin equal
  · exact congrArg ChartCubicKey.shared equal
  · exact congrArg ChartCubicKey.current equal

/-- Embed one evidence-index candidate in the exact tagged U01 unit family. -/
private def evidenceIndexUnitAddress {tokens : List Token}
    (address : EvidenceIndexAddress tokens) :
    ChartCubicUnitKind × ChartCubicKey tokens :=
  (.U01_evidenceIndex, evidenceIndexKey address)

private theorem evidenceIndexUnitAddress_injective :
    ∀ {tokens : List Token},
      Function.Injective (@evidenceIndexUnitAddress tokens) := by
  intro tokens
  intro left right equal
  apply evidenceIndexKey_injective
  exact congrArg Prod.snd equal

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

private abbrev ProductionInstanceCoordinates (tokens : List Token) :=
  (ProductionId × GuardContext tokens) × Boundary tokens

private def productionInstanceCoordinates {tokens : List Token}
    (key : ProductionInstanceKey tokens) :
    ProductionInstanceCoordinates tokens :=
  ((key.production, key.context), key.origin)

private def productionInstanceOfCoordinates {tokens : List Token}
    (coordinates : ProductionInstanceCoordinates tokens) :
    ProductionInstanceKey tokens :=
  ⟨coordinates.1.1, coordinates.2, coordinates.1.2⟩

private theorem productionInstance_cardinality (tokens : List Token) :
    ∃ encode : ProductionInstanceKey tokens →
        Fin (productionCount * (1 + 3 * (tokens.length + 2)) *
          (tokens.length + 2)),
      Function.Injective encode ∧ Function.Surjective encode := by
  let productionContextCardinality := product_cardinality (by omega)
    productionId_cardinality (guard_context_cardinality tokens)
  let coordinateCardinality := product_cardinality (by omega)
    productionContextCardinality (fin_cardinality (tokens.length + 2))
  exact transport_cardinality productionInstanceCoordinates
    productionInstanceOfCoordinates
    (by intro key; cases key; rfl)
    (by rintro ⟨⟨_, _⟩, _⟩; rfl)
    coordinateCardinality

/-- The closed tagged unit-address universe has its exact tight cardinality. -/
theorem chart_unit_family_complete (tokens : List Token) :
    let q := tokens.length + 2
    let c := 1 + 3 * q
    let source := 1 + c
    let linear := source * D * q * q
    let prediction := source * D * productionCount * q * q
    let cubic := source * D * D * q * q * q
    let guardCell :=
      Sigma fun production : ProductionId => Fin (guardOf production).length
    let guardAddress := (guardCell × GuardContext tokens) × Boundary tokens
    let unitDomain :=
      (((((ChartPhaseSlot ⊕
          (GuardFinalizeSlot × GuardInstanceKey tokens)) ⊕
        ProductionInstanceKey tokens) ⊕
        (GuardWitnessSlot × guardAddress)) ⊕
        (ChartLinearUnitKind × ChartLinearKey tokens)) ⊕
        (ChartPredictionUnitKind × ChartPredictionKey tokens)) ⊕
        (ChartCubicUnitKind × ChartCubicKey tokens)
    ∃ encode : unitDomain → Fin
        (4 +
          8 * (allPriorityGuardIds.length * q * (q + 1) / 2) +
          productionCount * c * q +
          4 * H * c * q +
          14 * linear + 2 * prediction + 8 * cubic),
      Function.Injective encode ∧ Function.Surjective encode := by
  dsimp only
  let q := tokens.length + 2
  let c := 1 + 3 * q
  let source := 1 + c
  let linear := source * D * q * q
  let prediction := source * D * productionCount * q * q
  let cubic := source * D * D * q * q * q
  have qPositive : 0 < q := by simp [q]
  have cPositive : 0 < c := by dsimp only [c]; omega
  have sourcePositive : 0 < source := by dsimp only [source]; omega
  have hPositive : 0 < H := by rw [H_eq_eighteen]; omega
  rcases chart_unit_kind_cardinality with
    ⟨phaseCardinality, finalizeSlotCardinality, witnessSlotCardinality,
      linearKindCardinality, predictionKindCardinality,
      cubicKindCardinality⟩
  let guardCardinality := guard_instance_cardinality tokens
  let guardSample : GuardInstanceKey tokens := {
    guard := .G01_statementIf
    contextStart := Boundary.start tokens
    siteCursor := Boundary.start tokens
    ordered := Nat.le_refl _
  }
  have guardPositive :
      0 < allPriorityGuardIds.length * q * (q + 1) / 2 := by
    obtain ⟨guardEncode, _guardInjective, _guardSurjective⟩ :=
      guardCardinality
    exact Nat.zero_lt_of_lt (guardEncode guardSample).isLt
  let guardFamilyCardinality := product_cardinality guardPositive
    finalizeSlotCardinality guardCardinality
  let witnessAddressCardinality := product_cardinality qPositive
    (product_cardinality cPositive guardCellAddress_cardinality
      (guard_context_cardinality tokens)) (fin_cardinality q)
  have witnessAddressPositive : 0 < H * c * q :=
    Nat.mul_pos (Nat.mul_pos hPositive cPositive) qPositive
  let witnessFamilyCardinality := product_cardinality witnessAddressPositive
    witnessSlotCardinality witnessAddressCardinality
  rcases chart_key_cardinality tokens with
    ⟨_sourceCardinality, linearKeyCardinality, predictionKeyCardinality,
      cubicKeyCardinality⟩
  have linearPositive : 0 < linear := by
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos sourcePositive dotted_count_positive)
        qPositive) qPositive
  have predictionPositive : 0 < prediction := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos sourcePositive dotted_count_positive)
          production_count_positive) qPositive) qPositive
  have cubicPositive : 0 < cubic := by
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos sourcePositive dotted_count_positive)
            dotted_count_positive) qPositive) qPositive) qPositive
  let linearFamilyCardinality := product_cardinality linearPositive
    linearKindCardinality linearKeyCardinality
  let predictionFamilyCardinality := product_cardinality predictionPositive
    predictionKindCardinality predictionKeyCardinality
  let cubicFamilyCardinality := product_cardinality cubicPositive
    cubicKindCardinality cubicKeyCardinality
  let phaseGuardCardinality := sum_cardinality phaseCardinality
    guardFamilyCardinality
  let withProductionCardinality := sum_cardinality phaseGuardCardinality
    (productionInstance_cardinality tokens)
  let withWitnessCardinality := sum_cardinality withProductionCardinality
    witnessFamilyCardinality
  let withLinearCardinality := sum_cardinality withWitnessCardinality
    linearFamilyCardinality
  let withPredictionCardinality := sum_cardinality withLinearCardinality
    predictionFamilyCardinality
  let allFamilyCardinality := sum_cardinality withPredictionCardinality
    cubicFamilyCardinality
  exact cast_cardinality (by
    simp only [q, c, source, linear, prediction, cubic, Nat.mul_assoc])
    allFamilyCardinality

/-- Every tagged chart unit occupies a distinct slot below `chartGBound`. -/
theorem chart_unit_family_injective (tokens : List Token) :
    let q := tokens.length + 2
    let c := 1 + 3 * q
    let source := 1 + c
    let linear := source * D * q * q
    let prediction := source * D * productionCount * q * q
    let cubic := source * D * D * q * q * q
    let guardCell :=
      Sigma fun production : ProductionId => Fin (guardOf production).length
    let guardAddress := (guardCell × GuardContext tokens) × Boundary tokens
    let unitDomain :=
      (((((ChartPhaseSlot ⊕
          (GuardFinalizeSlot × GuardInstanceKey tokens)) ⊕
        ProductionInstanceKey tokens) ⊕
        (GuardWitnessSlot × guardAddress)) ⊕
        (ChartLinearUnitKind × ChartLinearKey tokens)) ⊕
        (ChartPredictionUnitKind × ChartPredictionKey tokens)) ⊕
        (ChartCubicUnitKind × ChartCubicKey tokens)
    ∃ encode : unitDomain → Fin
        (4 +
          8 * allPriorityGuardIds.length * q * q +
          productionCount * c * q +
          4 * H * c * q +
          14 * linear + 2 * prediction + 8 * cubic),
      Function.Injective encode := by
  dsimp only
  obtain ⟨tightEncode, tightInjective, _tightSurjective⟩ :=
    chart_unit_family_complete tokens
  let q := tokens.length + 2
  have qSuccLe : q + 1 ≤ 2 * q := by simp [q]; omega
  have numeratorLe :
      allPriorityGuardIds.length * q * (q + 1) ≤
        2 * (allPriorityGuardIds.length * q * q) := by
    calc
      allPriorityGuardIds.length * q * (q + 1) ≤
          allPriorityGuardIds.length * q * (2 * q) :=
        Nat.mul_le_mul_left _ qSuccLe
      _ = 2 * (allPriorityGuardIds.length * q * q) := by ac_rfl
  have rectangleLe :
      allPriorityGuardIds.length * q * (q + 1) / 2 ≤
        allPriorityGuardIds.length * q * q :=
    Nat.div_le_of_le_mul numeratorLe
  have guardFamilyLe :
      8 * (allPriorityGuardIds.length * q * (q + 1) / 2) ≤
        8 * allPriorityGuardIds.length * q * q := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8 rectangleLe
  exact cast_injection (by
    have expandedGuardLe :
        8 * (allPriorityGuardIds.length * (tokens.length + 2) *
          (tokens.length + 2 + 1) / 2) ≤
        8 * allPriorityGuardIds.length * (tokens.length + 2) *
          (tokens.length + 2) := by
      simpa only [q] using guardFamilyLe
    omega) ⟨tightEncode, tightInjective⟩

private abbrev GuardAddress (tokens : List Token) :=
  (GuardCellAddress × GuardContext tokens) × Boundary tokens

private abbrev AddressSum (tokens : List Token) :=
  (((((ChartPhaseSlot ⊕
      (GuardFinalizeSlot × GuardInstanceKey tokens)) ⊕
    ProductionInstanceKey tokens) ⊕
    (GuardWitnessSlot × GuardAddress tokens)) ⊕
    (ChartLinearUnitKind × ChartLinearKey tokens)) ⊕
    (ChartPredictionUnitKind × ChartPredictionKey tokens)) ⊕
    (ChartCubicUnitKind × ChartCubicKey tokens)

/-- One and only one charge identity for every primitive chart unit. -/
private inductive UnitAddress (tokens : List Token) where
  | phase (slot : ChartPhaseSlot)
  | guardFinalize
      (slot : GuardFinalizeSlot) (key : GuardInstanceKey tokens)
  | production (key : ProductionInstanceKey tokens)
  | guardWitness
      (slot : GuardWitnessSlot) (key : GuardAddress tokens)
  | linear (kind : ChartLinearUnitKind) (key : ChartLinearKey tokens)
  | prediction
      (kind : ChartPredictionUnitKind) (key : ChartPredictionKey tokens)
  | cubic (kind : ChartCubicUnitKind) (key : ChartCubicKey tokens)
  deriving DecidableEq

private def UnitAddress.toSum {tokens : List Token} :
    UnitAddress tokens → AddressSum tokens
  | .phase slot => .inl (.inl (.inl (.inl (.inl (.inl slot)))))
  | .guardFinalize slot key =>
      .inl (.inl (.inl (.inl (.inl (.inr (slot, key))))))
  | .production key => .inl (.inl (.inl (.inl (.inr key))))
  | .guardWitness slot key => .inl (.inl (.inl (.inr (slot, key))))
  | .linear kind key => .inl (.inl (.inr (kind, key)))
  | .prediction kind key => .inl (.inr (kind, key))
  | .cubic kind key => .inr (kind, key)

private def UnitAddress.ofSum {tokens : List Token} :
    AddressSum tokens → UnitAddress tokens
  | .inl (.inl (.inl (.inl (.inl (.inl slot))))) => .phase slot
  | .inl (.inl (.inl (.inl (.inl (.inr (slot, key)))))) =>
      .guardFinalize slot key
  | .inl (.inl (.inl (.inl (.inr key)))) => .production key
  | .inl (.inl (.inl (.inr (slot, key)))) => .guardWitness slot key
  | .inl (.inl (.inr (kind, key))) => .linear kind key
  | .inl (.inr (kind, key)) => .prediction kind key
  | .inr (kind, key) => .cubic kind key

private theorem UnitAddress.toSum_injective {tokens : List Token} :
    Function.Injective (@UnitAddress.toSum tokens) := by
  intro left right equal
  cases left <;> cases right <;>
    simp only [UnitAddress.toSum, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq] at equal
  all_goals first
    | contradiction
    | (rcases equal with ⟨leftEqual, rightEqual⟩
       cases leftEqual
       cases rightEqual
       rfl)
    | (cases equal; rfl)

private theorem UnitAddress.toSum_surjective {tokens : List Token} :
    Function.Surjective (@UnitAddress.toSum tokens) := by
  intro address
  refine ⟨UnitAddress.ofSum address, ?_⟩
  rcases address with left | cubic
  · rcases left with left | prediction
    · rcases left with left | linear
      · rcases left with left | witness
        · rcases left with left | production
          · rcases left with phase | guard <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- The landed U01 bridge occupies exactly the cubic U01 counter family. -/
private def UnitAddress.evidenceIndex {tokens : List Token}
    (address : EvidenceIndexAddress tokens) : UnitAddress tokens :=
  let unit := evidenceIndexUnitAddress address
  .cubic unit.1 unit.2

private theorem UnitAddress.evidenceIndex_injective {tokens : List Token} :
    Function.Injective (@UnitAddress.evidenceIndex tokens) := by
  intro left right equal
  apply evidenceIndexUnitAddress_injective
  simp only [UnitAddress.evidenceIndex] at equal
  have fields := UnitAddress.cubic.inj equal
  exact Prod.ext fields.1 fields.2

private def tightAddressCount (tokens : List Token) : Nat :=
  let q := tokens.length + 2
  let c := 1 + 3 * q
  let source := 1 + c
  let linear := source * D * q * q
  let prediction := source * D * productionCount * q * q
  let cubic := source * D * D * q * q * q
  4 + 8 * (allPriorityGuardIds.length * q * (q + 1) / 2) +
    productionCount * c * q + 4 * H * c * q +
    14 * linear + 2 * prediction + 8 * cubic

private theorem unitAddress_complete (tokens : List Token) :
    ∃ encode : UnitAddress tokens → Fin (tightAddressCount tokens),
      Function.Injective encode ∧ Function.Surjective encode := by
  have cardinality := chart_unit_family_complete tokens
  change ∃ encode : AddressSum tokens → Fin (tightAddressCount tokens),
    Function.Injective encode ∧ Function.Surjective encode at cardinality
  obtain ⟨encode, injective, surjective⟩ := cardinality
  refine ⟨encode ∘ UnitAddress.toSum,
    injective.comp UnitAddress.toSum_injective, ?_⟩
  intro index
  obtain ⟨address, equal⟩ := surjective index
  obtain ⟨unit, sameAddress⟩ := UnitAddress.toSum_surjective address
  exact ⟨unit, by simp [Function.comp_apply, sameAddress, equal]⟩

/-- The ADR bound takes `T`, including the one logical EOF terminal. -/
def chartGBound (terminalCount : Nat) : Nat :=
  let q := terminalCount + 1
  let c := 1 + 3 * q
  let source := 1 + c
  let linear := source * D * q * q
  let prediction := source * D * productionCount * q * q
  let cubic := source * D * D * q * q * q
  4 + 8 * allPriorityGuardIds.length * q * q +
    productionCount * c * q + 4 * H * c * q +
    14 * linear + 2 * prediction + 8 * cubic

private theorem unitAddress_injective (tokens : List Token) :
    ∃ encode : UnitAddress tokens →
        Fin (chartGBound (tokens.length + 1)),
      Function.Injective encode := by
  obtain ⟨encode, injective⟩ := chart_unit_family_injective tokens
  exact ⟨encode ∘ UnitAddress.toSum,
    injective.comp UnitAddress.toSum_injective⟩

/-- The executable ledger of already charged primitive addresses. -/
private structure Counter (tokens : List Token) where
  usedRev : List (UnitAddress tokens)
  unique : usedRev.Nodup

private def Counter.empty (tokens : List Token) : Counter tokens :=
  ⟨[], by simp⟩

private def Counter.units {tokens : List Token}
    (counter : Counter tokens) : Nat :=
  counter.usedRev.length

/-- Charge exactly one fresh primitive address. -/
private def Counter.charge {tokens : List Token}
    (counter : Counter tokens) (address : UnitAddress tokens)
    (fresh : address ∉ counter.usedRev) : Counter tokens :=
  ⟨address :: counter.usedRev, List.nodup_cons.mpr ⟨fresh, counter.unique⟩⟩

/-- One logical primitive: its state transition has exactly one charge. -/
private structure PrimitiveStep (tokens : List Token) (state : Type) where
  address : UnitAddress tokens
  transition : state → state

/-- Executor payload paired with the only counter that may advance it. -/
private structure CountedState (tokens : List Token) (state : Type) where
  payload : state
  counter : Counter tokens

private def CountedState.runPrimitive {tokens : List Token} {state : Type}
    (current : CountedState tokens state) (step : PrimitiveStep tokens state)
    (fresh : step.address ∉ current.counter.usedRev) :
    CountedState tokens state := {
  payload := step.transition current.payload
  counter := current.counter.charge step.address fresh
}

@[simp] private theorem Counter.units_empty (tokens : List Token) :
    (Counter.empty tokens).units = 0 :=
  rfl

@[simp] private theorem Counter.units_charge {tokens : List Token}
    (counter : Counter tokens) (address : UnitAddress tokens)
    (fresh : address ∉ counter.usedRev) :
    (counter.charge address fresh).units = counter.units + 1 := by
  simp [Counter.charge, Counter.units]

@[simp] private theorem CountedState.runPrimitive_units
    {tokens : List Token} {state : Type}
    (current : CountedState tokens state) (step : PrimitiveStep tokens state)
    (fresh : step.address ∉ current.counter.usedRev) :
    (current.runPrimitive step fresh).counter.units =
      current.counter.units + 1 := by
  simp [CountedState.runPrimitive]

private theorem map_nodup_of_injective
    {alpha beta : Type} (encode : alpha → beta)
    (injective : Function.Injective encode) {values : List alpha}
    (unique : values.Nodup) : (values.map encode).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at unique
      simp only [List.map_cons]
      rw [List.nodup_cons]
      refine ⟨?_, induction unique.2⟩
      intro member
      rw [List.mem_map] at member
      rcases member with ⟨value, valueMember, equal⟩
      exact unique.1 ((injective equal.symm) ▸ valueMember)

private theorem nodup_length_le_of_subset
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {left right : List alpha} (unique : left.Nodup)
    (subset : left ⊆ right) : left.length ≤ right.length := by
  induction left generalizing right with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at unique
      have headMember : head ∈ right := subset (by simp)
      have tailSubset : tail ⊆ right.erase head := by
        intro value valueMember
        rw [List.mem_erase_of_ne]
        · exact subset (by simp [valueMember])
        · intro equal
          exact unique.1 (equal.symm ▸ valueMember)
      have tailBound := induction unique.2 tailSubset
      rw [List.length_erase_of_mem headMember] at tailBound
      simp only [List.length_cons]
      have rightPositive := List.length_pos_of_mem headMember
      omega

/-- A collision-free ledger over chart slots stays within the ADR bound. -/
private theorem oneUseLedger_units_le_chartGBound
    {tokens : List Token} {actualUnits : Nat}
    (oneUse :
      ∃ usedSlots : List (Fin (chartGBound (tokens.length + 1))),
        usedSlots.Nodup ∧ actualUnits = usedSlots.length) :
    actualUnits ≤ chartGBound (tokens.length + 1) := by
  rcases oneUse with ⟨usedSlots, unique, count⟩
  rw [count]
  have subset : usedSlots ⊆
      List.finRange (chartGBound (tokens.length + 1)) := by
    intro slot _
    exact List.mem_finRange slot
  have bound := nodup_length_le_of_subset unique subset
  simpa using bound

/-- Any state constructible only through fresh charges is within the ADR bound. -/
private theorem Counter.units_le_chartGBound {tokens : List Token}
    (counter : Counter tokens) :
    counter.units ≤ chartGBound (tokens.length + 1) := by
  obtain ⟨encode, injective⟩ := unitAddress_injective tokens
  apply oneUseLedger_units_le_chartGBound
  refine ⟨counter.usedRev.map encode,
    map_nodup_of_injective encode injective counter.unique, ?_⟩
  simp [Counter.units]

/-- At the bound, no primitive address can remain fresh. -/
private theorem Counter.no_fresh_at_bound {tokens : List Token}
    (counter : Counter tokens)
    (full : counter.units = chartGBound (tokens.length + 1))
    (address : UnitAddress tokens) : address ∈ counter.usedRev := by
  by_cases member : address ∈ counter.usedRev
  · exact member
  · have nextBound :=
      (counter.charge address member).units_le_chartGBound
    rw [Counter.units_charge, full] at nextBound
    omega

/-- Final executor output; its unit count is derived from the unique ledger. -/
private structure Execution (tokens : List Token) (result : Type) where
  value : result
  counter : Counter tokens

private def Execution.actualUnits {tokens : List Token} {result : Type}
    (execution : Execution tokens result) : Nat :=
  execution.counter.units

/-- A counted executor result inherits the one-use-ledger bound. -/
private theorem Execution.actualUnits_le_chartGBound
    {tokens : List Token} {result : Type}
    (execution : Execution tokens result) :
    execution.actualUnits ≤ chartGBound (tokens.length + 1) :=
  execution.counter.units_le_chartGBound

namespace Chart

open Grammar

private def terminalValueAt?
    (tokens : List Token) (cursor : TerminalCursor tokens) :
    Option TerminalStreamValue :=
  if inRange : cursor.val < tokens.length then
    some (.retained tokens[cursor.val])
  else
    some .endOfFile

private def rawSeedBool {tokens : List Token}
    (item : DottedItem tokens) : Bool :=
  item.dot.val == 0 && item.origin == item.current

private def rawPredictBool {tokens : List Token}
    (known : List (DottedItem tokens)) (predicted : DottedItem tokens) : Bool :=
  known.any fun waiting =>
    predicted.dot.val == 0 &&
      predicted.origin == waiting.current &&
      predicted.current == waiting.current &&
      match waiting.production.rhs[waiting.dot.val]? with
      | some (.nonterminal symbol) => predicted.production.lhs == symbol
      | _ => false

private def rawScanBool {tokens : List Token}
    (known : List (DottedItem tokens)) (after : DottedItem tokens) : Bool :=
  known.any fun before =>
    if currentInRange : before.current.val < tokens.length + 1 then
      let cursor : TerminalCursor tokens :=
        ⟨before.current.val, currentInRange⟩
      match before.production.rhs[before.dot.val]?,
          terminalValueAt? tokens cursor with
      | some (.terminal terminal), some value =>
          terminalMatchesBool terminal value &&
            after.production == before.production &&
            after.dot.val == before.dot.val + 1 &&
            after.origin == before.origin &&
            after.current == cursor.afterBoundary
      | _, _ => false
    else
      false

private def rawCompleteBool {tokens : List Token}
    (known : List (DottedItem tokens)) (after : DottedItem tokens) : Bool :=
  known.any fun waiting => known.any fun finished =>
    match waiting.production.rhs[waiting.dot.val]? with
    | some (.nonterminal symbol) =>
        symbol == finished.production.lhs &&
          finished.dot.val == finished.production.rhs.length &&
          waiting.current == finished.origin &&
          after.production == waiting.production &&
          after.dot.val == waiting.dot.val + 1 &&
          after.origin == waiting.origin &&
          after.current == finished.current
    | _ => false

private def rawMemberBool {tokens : List Token}
    (known : List (DottedItem tokens)) (item : DottedItem tokens) : Bool :=
  known.any fun candidate => decide (candidate = item)

private def rawClosureBool (tokens : List Token)
    (known : List (DottedItem tokens)) (item : DottedItem tokens) : Bool :=
  rawMemberBool known item || rawSeedBool item ||
    rawPredictBool known item || rawScanBool known item ||
      rawCompleteBool known item

private def rawClosureStep (tokens : List Token)
    (known : List (DottedItem tokens)) : List (DottedItem tokens) :=
  (allDottedItems tokens).filter (rawClosureBool tokens known)

private def closureIterate {α : Type}
    (step : List α → List α) : Nat → List α
  | 0 => []
  | fuel + 1 => step (closureIterate step fuel)

private theorem closureIterate_stable_of_stable
    {α : Type} (step : List α → List α) {start finish : Nat}
    (stable : closureIterate step start =
      closureIterate step (start + 1))
    (later : start ≤ finish) :
    closureIterate step finish =
      closureIterate step (finish + 1) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  clear later
  induction offset with
  | zero => simpa using stable
  | succ offset induction =>
      change step (closureIterate step (start + offset)) =
        step (closureIterate step (start + offset + 1))
      exact congrArg step induction

private theorem finiteClosure_stable
    {α : Type} [DecidableEq α]
    (carrier : List α) (step : List α → List α)
    (ascending : ∀ stage,
      (closureIterate step stage).Sublist
        (closureIterate step (stage + 1)))
    (bounded : ∀ stage,
      (closureIterate step stage).Sublist carrier) :
    step (closureIterate step carrier.length) =
      closureIterate step carrier.length := by
  let final := closureIterate step carrier.length
  match stable : decide
      (final = closureIterate step (carrier.length + 1)) with
  | true =>
      have equality : final =
          closureIterate step (carrier.length + 1) :=
        of_decide_eq_true stable
      exact equality.symm
  | false =>
      have notStable : final ≠
          closureIterate step (carrier.length + 1) :=
        of_decide_eq_false stable
      have noEarlier (stage : Nat) (beforeFinal : stage ≤ carrier.length) :
          closureIterate step stage ≠
            closureIterate step (stage + 1) := by
        intro equality
        exact notStable (closureIterate_stable_of_stable
          step equality beforeFinal)
      have lower (stage : Nat) (within : stage ≤ carrier.length + 1) :
          stage ≤ (closureIterate step stage).length := by
        induction stage with
        | zero => simp
        | succ previous induction =>
            have previousWithin : previous ≤ carrier.length + 1 := by omega
            have previousBeforeFinal : previous ≤ carrier.length := by omega
            have previousLower := induction previousWithin
            have growth := ascending previous
            have lengthLe := growth.length_le
            have lengthNe :
                (closureIterate step previous).length ≠
                  (closureIterate step (previous + 1)).length := by
              intro sameLength
              exact noEarlier previous previousBeforeFinal
                (growth.eq_of_length sameLength)
            omega
      have finalLower := lower (carrier.length + 1) (by omega)
      have finalUpper := (bounded (carrier.length + 1)).length_le
      exfalso
      omega

private theorem filter_sublist_filter_of_imp
    {α : Type} (values : List α) (left right : α → Bool)
    (implies : ∀ value, value ∈ values →
      left value = true → right value = true) :
    (values.filter left).Sublist (values.filter right) := by
  induction values with
  | nil => exact .slnil
  | cons head tail induction =>
      have tailImplication : ∀ value, value ∈ tail →
          left value = true → right value = true := by
        intro value member selected
        exact implies value (List.mem_cons_of_mem head member) selected
      have tailSublist := induction tailImplication
      simp only [List.filter_cons]
      match leftTrue : left head with
      | false =>
          match rightTrue : right head with
          | false => exact tailSublist
          | true => exact tailSublist.cons head
      | true =>
          have selected : right head = true :=
            implies head (List.mem_cons_self) leftTrue
          rw [selected]
          exact tailSublist.cons_cons head

private theorem filteredClosure_ascending
    {α : Type} (carrier : List α) (select : List α → α → Bool)
    (inflationary : ∀ known item, item ∈ known →
      select known item = true) :
    ∀ stage,
      (closureIterate (fun known => carrier.filter (select known)) stage).Sublist
        (closureIterate (fun known => carrier.filter (select known))
          (stage + 1)) := by
  intro stage
  cases stage with
  | zero => exact List.nil_sublist _
  | succ previous =>
      simp only [closureIterate]
      apply filter_sublist_filter_of_imp
      intro item member selected
      apply inflationary
      rw [List.mem_filter]
      exact ⟨member, selected⟩

private theorem filteredClosure_bounded
    {α : Type} (carrier : List α) (select : List α → α → Bool) :
    ∀ stage,
      (closureIterate (fun known => carrier.filter (select known)) stage).Sublist
        carrier := by
  intro stage
  cases stage with
  | zero => exact List.nil_sublist _
  | succ _ => exact List.filter_sublist

private theorem finiteFilteredClosure_stable
    {α : Type} [DecidableEq α]
    (carrier : List α) (select : List α → α → Bool)
    (inflationary : ∀ known item, item ∈ known →
      select known item = true) :
    carrier.filter (select
        (closureIterate (fun known => carrier.filter (select known))
          carrier.length)) =
      closureIterate (fun known => carrier.filter (select known))
        carrier.length := by
  exact finiteClosure_stable carrier _
    (filteredClosure_ascending carrier select inflationary)
    (filteredClosure_bounded carrier select)

private theorem rawClosureBool_inflationary
    {tokens : List Token} (known : List (DottedItem tokens))
    (item : DottedItem tokens) (member : item ∈ known) :
    rawClosureBool tokens known item = true := by
  have contained : rawMemberBool known item = true := by
    rw [rawMemberBool, List.any_eq_true]
    exact ⟨item, member, by simp⟩
  simp only [rawClosureBool, Bool.or_eq_true]
  exact Or.inl (Or.inl (Or.inl (Or.inl contained)))

private def rawSaturation (tokens : List Token) : List (DottedItem tokens) :=
  closureIterate (rawClosureStep tokens) (allDottedItems tokens).length

private theorem rawSaturation_stable (tokens : List Token) :
    rawClosureStep tokens (rawSaturation tokens) = rawSaturation tokens := by
  exact finiteFilteredClosure_stable (allDottedItems tokens)
    (rawClosureBool tokens) rawClosureBool_inflationary

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def runMappedPrimitive?
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after) :
    Option (CountedState tokens after) :=
  if fresh : address ∉ current.counter.usedRev then
    some {
      payload := transition current.payload
      counter := current.counter.charge address fresh
    }
  else
    none

private theorem runMappedPrimitive?_units
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    {result : CountedState tokens after}
    (selected : runMappedPrimitive? current address transition = some result) :
    result.counter.units = current.counter.units + 1 := by
  unfold runMappedPrimitive? at selected
  split at selected
  · cases selected
    simp
  · contradiction

private def chargeAddresses?
    {tokens : List Token} {state : Type}
    (current : CountedState tokens state) :
    List (UnitAddress tokens) → Option (CountedState tokens state)
  | [] => some current
  | address :: rest => do
      let next ← runMappedPrimitive? current address id
      chargeAddresses? next rest

private def allGuardInstanceKeys (tokens : List Token) :
    List (GuardInstanceKey tokens) :=
  allPriorityGuardIds.flatMap fun guard =>
    (List.finRange (tokens.length + 2)).flatMap fun contextStart =>
      (List.finRange (tokens.length + 2)).filterMap fun siteCursor =>
        if ordered : contextStart.val ≤ siteCursor.val then
          some {
            guard := guard
            contextStart := contextStart
            siteCursor := siteCursor
            ordered := ordered
          }
        else
          none

private theorem allGuardInstanceKeys_complete
    {tokens : List Token} (key : GuardInstanceKey tokens) :
    key ∈ allGuardInstanceKeys tokens := by
  rw [allGuardInstanceKeys, List.mem_flatMap]
  refine ⟨key.guard, ?_, ?_⟩
  · cases key.guard <;> simp [allPriorityGuardIds]
  · rw [List.mem_flatMap]
    refine ⟨key.contextStart, List.mem_finRange _, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨key.siteCursor, List.mem_finRange _, ?_⟩
    simp [key.ordered]

private structure PhaseAOpen (file : WorkspaceFile) (tokens : List Token) where
  rawItems : List (DottedItem tokens)
  itemQueue : List (DottedItem tokens)
  rawEdges : List (PackedEdge file tokens)
  edgeQueue : List (PackedEdge file tokens)

private def beginPhaseA (file : WorkspaceFile) (tokens : List Token) :
    CountedState tokens (PhaseAOpen file tokens) := {
  payload := ⟨[], [], [], []⟩
  counter := (Counter.empty tokens).charge
    (.phase .initializePhaseA) (by simp [Counter.empty])
}

@[simp] private theorem beginPhaseA_units
    (file : WorkspaceFile) (tokens : List Token) :
    (beginPhaseA file tokens).counter.units = 1 := by
  simp [beginPhaseA]

private structure PhaseASealed (file : WorkspaceFile) (tokens : List Token) where
  rawItems : List (DottedItem tokens)
  rawEdges : List (PackedEdge file tokens)

private structure PhaseBOpen (file : WorkspaceFile) (tokens : List Token) where
  phaseA : PhaseASealed file tokens
  cells : GuardInstanceKey tokens → Option GuardMemoState
  remaining : List (GuardInstanceKey tokens)
  finalizedRev : List (GuardInstanceKey tokens)

private def enterPhaseB? {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (CountedState tokens (PhaseBOpen file tokens)) :=
  if _itemsDone : current.payload.itemQueue = [] then
    if _edgesDone : current.payload.edgeQueue = [] then
      if _saturated : current.payload.rawItems = rawSaturation tokens then
        runMappedPrimitive? current (.phase .sealAEnterB) fun state => {
          phaseA := ⟨state.rawItems, state.rawEdges⟩
          cells := fun _ => none
          remaining := allGuardInstanceKeys tokens
          finalizedRev := []
        }
      else
        none
    else
      none
  else
    none

private def preFinalGuardSlots : List GuardFinalizeSlot := [
  .siteTerminalLookup,
  .adjacentTerminalWindowLookup,
  .exactSliceLookup,
  .unguardedSpanLookup,
  .greatestEndLookup,
  .delimiterOrRegionLookup
]

private def finalizeNextGuardWithDecision?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBOpen file tokens))
    (decision : GuardDecision) :
    Option (CountedState tokens (PhaseBOpen file tokens)) :=
  match current.payload.remaining with
  | [] => none
  | key :: rest => do
      let initialized ← runMappedPrimitive? current
        (.guardFinalize .initializeUndecided key) fun state => {
          state with
          cells := fun candidate =>
            if candidate = key then some .undecided else state.cells candidate
        }
      let lookups ← chargeAddresses? initialized
        (preFinalGuardSlots.map fun slot => .guardFinalize slot key)
      runMappedPrimitive? lookups
        (.guardFinalize .writeFinalDecision key) fun state => {
          phaseA := state.phaseA
          cells := fun candidate =>
            if candidate = key then some (.final decision)
            else state.cells candidate
          remaining := rest
          finalizedRev := key :: state.finalizedRev
        }

private structure PhaseBSealed (file : WorkspaceFile) (tokens : List Token) where
  phaseA : PhaseASealed file tokens
  memo : GuardMemo tokens
  finalizedRev : List (GuardInstanceKey tokens)

private def sealPhaseB?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBOpen file tokens)) :
    Option (CountedState tokens (PhaseBSealed file tokens)) :=
  match current.payload.remaining with
  | _ :: _ => none
  | [] =>
      runMappedPrimitive? current (.phase .sealBEnterC) fun state => {
        phaseA := state.phaseA
        memo := fun key =>
          match state.cells key with
          | some value => value
          | none => .undecided
        finalizedRev := state.finalizedRev
      }

private def contextualLinearKey {tokens : List Token}
    (item : ContextualItemKey tokens) : ChartLinearKey tokens := {
  source := .contextual item.context
  dotted := ⟨item.raw.production, item.raw.dot⟩
  origin := item.raw.origin
  current := item.raw.current
}

private def contextualRoot (tokens : List Token) :
    ContextualItemKey tokens := {
  raw := {
    production := .root .module
    dot := ⟨0, Nat.zero_lt_succ _⟩
    origin := Boundary.start tokens
    current := Boundary.start tokens
  }
  context := .plain
}

private structure PhaseCOpen (file : WorkspaceFile) (tokens : List Token) where
  phaseA : PhaseASealed file tokens
  memo : GuardMemo tokens
  guardWitnesses : List (GuardWitnessKey tokens)
  contextualItems : List (ContextualItemKey tokens)
  itemQueue : List (ContextualItemKey tokens)
  contextualEdges : List (StructurallyValidContextualPackedEdge file tokens)
  edgeQueue : List (StructurallyValidContextualPackedEdge file tokens)

private def enterPhaseC?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens)) :
    Option (CountedState tokens (PhaseCOpen file tokens)) := do
  let root := contextualRoot tokens
  runMappedPrimitive? current
    (.linear .L03_itemInsert (contextualLinearKey root)) fun state => {
      phaseA := state.phaseA
      memo := state.memo
      guardWitnesses := []
      contextualItems := [root]
      itemQueue := [root]
      contextualEdges := []
      edgeQueue := []
    }

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def guardWitnessFor?
    {tokens : List Token}
    (memo : GuardMemo tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity) :
    Option (GuardWitnessKey tokens) :=
  match selected : GuardAnchor.decide productionInstance cell with
  | none => none
  | some guardInstance =>
      match memo guardInstance with
      | .undecided => none
      | .final decision =>
          if _accepted : cell.2.accepts decision = true then
            some ⟨{
              productionInstance := productionInstance
              guardInstance := guardInstance
              polarity := cell.2
            }, by
              have anchor : GuardAnchor productionInstance cell guardInstance :=
                GuardAnchor.decide_eq_some_iff.mp selected
              have sameGuard : guardInstance.guard = cell.1 :=
                anchor.2.1
              constructor
              · simpa only [sameGuard] using anchor.1
              · simpa only [sameGuard] using anchor⟩
          else
            none

private def guardCellAddress
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length) :
    GuardAddress tokens :=
  ((⟨productionInstance.production, index⟩, productionInstance.context),
    productionInstance.origin)

private def preInsertWitnessSlots : List GuardWitnessSlot := [
  .constructAnchor,
  .lookupFinalDecision,
  .comparePolarity
]

private def processGuardCell?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length) :
    Option (CountedState tokens (PhaseCOpen file tokens) × Bool) := do
  let address := guardCellAddress productionInstance index
  let inspected ← chargeAddresses? current
    (preInsertWitnessSlots.map fun slot => .guardWitness slot address)
  let witness := guardWitnessFor? current.payload.memo productionInstance
    ((guardOf productionInstance.production).get index)
  let inserted ← runMappedPrimitive? inspected
    (.guardWitness .insertWitness address) fun state =>
      match witness with
      | none => state
      | some key => {
          state with guardWitnesses := key :: state.guardWitnesses
        }
  pure (inserted, witness.isSome)

private def processGuardCells?
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    List (Fin (guardOf productionInstance.production).length) →
      CountedState tokens (PhaseCOpen file tokens) →
      Option (CountedState tokens (PhaseCOpen file tokens) × Bool)
  | [], current => some (current, true)
  | index :: rest, current => do
      let (next, accepted) ←
        processGuardCell? current productionInstance index
      let (finished, restAccepted) ←
        processGuardCells? productionInstance rest next
      pure (finished, accepted && restAccepted)

private def activateProduction?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens) :
    Option (CountedState tokens (PhaseCOpen file tokens) × Bool) := do
  let attempted ← runMappedPrimitive? current
    (.production productionInstance) id
  processGuardCells? productionInstance
    (List.ofFn fun index :
      Fin (guardOf productionInstance.production).length => index)
    attempted

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def rawLinearKey {tokens : List Token}
    (item : DottedItem tokens) : ChartLinearKey tokens := {
  source := .rawEvidence
  dotted := ⟨item.production, item.dot⟩
  origin := item.origin
  current := item.current
}

private def rawPredictionKey {tokens : List Token}
    (waiting : DottedItem tokens) (predicted : ProductionId) :
    ChartPredictionKey tokens := {
  source := .rawEvidence
  dotted := ⟨waiting.production, waiting.dot⟩
  production := predicted
  origin := waiting.origin
  current := waiting.current
}

private def rawCompletionKey {tokens : List Token}
    (waiting finished : DottedItem tokens) : ChartCubicKey tokens := {
  source := .rawEvidence
  waiting := ⟨waiting.production, waiting.dot⟩
  finished := ⟨finished.production, finished.dot⟩
  origin := waiting.origin
  shared := waiting.current
  current := finished.current
}

private def predictedItem? {tokens : List Token}
    (waiting : DottedItem tokens) (predicted : ProductionId) :
    Option (DottedItem tokens) :=
  match waiting.production.rhs[waiting.dot.val]? with
  | some (.nonterminal symbol) =>
      if _sameLhs : predicted.lhs = symbol then
        some {
          production := predicted
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := waiting.current
          current := waiting.current
        }
      else
        none
  | _ => none

private def scannedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (before : DottedItem tokens) :
    Option (DottedItem tokens × PackedEdge file tokens) :=
  if nextInRange : before.dot.val < before.production.rhs.length then
    match nextEq : before.production.rhs[before.dot.val] with
    | .terminal terminal =>
        if currentInRange : before.current.val < tokens.length + 1 then
          let cursor : TerminalCursor tokens :=
            ⟨before.current.val, currentInRange⟩
          match selected : MatchedTerminal.atCursor?
              file tokens owned terminal cursor with
          | none => none
          | some matched =>
              let after : DottedItem tokens := {
                production := before.production
                dot := ⟨before.dot.val + 1, by omega⟩
                origin := before.origin
                current := cursor.afterBoundary
              }
              let witness : ScannedEdgeWitness
                  file tokens before after cursor := {
                terminal := terminal
                matched := matched.val
                sameCursor := matched.property
                next := by
                  constructor
                  · exact nextInRange
                  · rw [List.getElem?_eq_getElem nextInRange, nextEq]
                atCurrent := Fin.ext rfl
                advance := by
                  rw [matched.property]
                  simp [AdvanceItem, after]
              }
              some (after, ⟨.scanned before after cursor,
                packedEdge_scanned_valid_iff.mpr ⟨witness⟩⟩)
        else
          none
    | _ => none
  else
    none

private def completedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished : DottedItem tokens) :
    Option (DottedItem tokens × PackedEdge file tokens) :=
  if nextInRange : waiting.dot.val < waiting.production.rhs.length then
    match nextEq : waiting.production.rhs[waiting.dot.val] with
    | .nonterminal symbol =>
        if sameLhs : symbol = finished.production.lhs then
          if complete : finished.dot.val = finished.production.rhs.length then
            if sameCursor : waiting.current = finished.origin then
              let after : DottedItem tokens := {
                production := waiting.production
                dot := ⟨waiting.dot.val + 1, by omega⟩
                origin := waiting.origin
                current := finished.current
              }
              let witness : CompletedEdgeWitness
                  tokens waiting finished after waiting.current := {
                next := by
                  constructor
                  · exact nextInRange
                  · rw [List.getElem?_eq_getElem nextInRange, nextEq, sameLhs]
                complete := complete
                waitingAtShared := rfl
                finishedAtShared := sameCursor.symm
                advance := by simp [AdvanceItem, after]
              }
              some (after, ⟨.completed waiting finished after waiting.current,
                packedEdge_completed_valid_iff.mpr ⟨witness⟩⟩)
            else
              none
          else
            none
        else
          none
    | _ => none
  else
    none

private inductive RawItemInsertSource where
  | seedOrPrediction
  | scan
  | completion

private def RawItemInsertSource.unitKind :
    RawItemInsertSource → ChartLinearUnitKind
  | .seedOrPrediction => .L03_itemInsert
  | .scan => .L05_scannedItemInsert
  | .completion => .L07_completedItemInsert

private def insertRawItem?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens) :
    Option (CountedState tokens (PhaseAOpen file tokens)) :=
  if rawMemberBool current.payload.rawItems item then
    some current
  else
    runMappedPrimitive? current
      (.linear source.unitKind (rawLinearKey item)) fun state => {
        state with
        rawItems := state.rawItems ++ [item]
        itemQueue := state.itemQueue ++ [item]
      }

private def insertRawEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) :
    Option (CountedState tokens (PhaseAOpen file tokens)) :=
  if current.payload.rawEdges.any fun candidate =>
      decide (candidate.val = edge.val) then
    some current
  else
    let address : UnitAddress tokens :=
      match edge.val with
      | .scanned before _ _ =>
          .linear .L06_scannedEdgeInsert (rawLinearKey before)
      | .completed waiting finished _ _ =>
          .cubic .U04_completedEdgeInsert
            (rawCompletionKey waiting finished)
    runMappedPrimitive? current address fun state => {
      state with
      rawEdges := state.rawEdges ++ [edge]
      edgeQueue := state.edgeQueue ++ [edge]
    }

private def dequeueRawItem?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens)) :=
  match current.payload.itemQueue with
  | [] => none
  | item :: rest => do
      let next ← runMappedPrimitive? current
        (.linear .L01_itemDequeue (rawLinearKey item)) fun state => {
          state with itemQueue := rest
        }
      pure (item, next)

private def dequeueRawEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens)) :=
  match current.payload.edgeQueue with
  | [] => none
  | edge :: rest => do
      let address : UnitAddress tokens :=
        match edge.val with
        | .scanned before _ _ =>
            .linear .L02_scannedEdgeDequeue (rawLinearKey before)
        | .completed waiting finished _ _ =>
            .cubic .U02_completedEdgeDequeue
              (rawCompletionKey waiting finished)
      let next ← runMappedPrimitive? current address fun state => {
        state with edgeQueue := rest
      }
      pure (edge, next)

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def rawSeedItems (tokens : List Token) :
    List (DottedItem tokens) :=
  (allDottedItems tokens).filter rawSeedBool

private def insertRawSeeds?
    {file : WorkspaceFile} {tokens : List Token} :
    List (DottedItem tokens) →
      CountedState tokens (PhaseAOpen file tokens) →
      Option (CountedState tokens (PhaseAOpen file tokens))
  | [], current => some current
  | item :: rest, current => do
      let next ← insertRawItem? current .seedOrPrediction item
      insertRawSeeds? rest next

private def attemptPrediction?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId) :
    Option (CountedState tokens (PhaseAOpen file tokens)) :=
  match predictedItem? waiting predicted with
  | none => some current
  | some item => do
      let attempted ← runMappedPrimitive? current
        (.prediction .R01_predictionAttempt
          (rawPredictionKey waiting predicted)) id
      insertRawItem? attempted .seedOrPrediction item

private def attemptPredictions?
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    List ProductionId → CountedState tokens (PhaseAOpen file tokens) →
      Option (CountedState tokens (PhaseAOpen file tokens))
  | [], current => some current
  | predicted :: rest, current => do
      let next ← attemptPrediction? current waiting predicted
      attemptPredictions? waiting rest next

private def rawScanApplicable {tokens : List Token}
    (item : DottedItem tokens) : Bool :=
  match item.production.rhs[item.dot.val]? with
  | some (.terminal _) => decide (item.current.val < tokens.length + 1)
  | _ => false

private def attemptScan?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens) :
    Option (CountedState tokens (PhaseAOpen file tokens)) :=
  if rawScanApplicable before then do
    let attempted ← runMappedPrimitive? current
      (.linear .L04_scanAttempt (rawLinearKey before)) id
    match scannedEdge? owned before with
    | none => some attempted
    | some (after, edge) => do
        let withItem ← insertRawItem? attempted .scan after
        insertRawEdge? withItem edge
  else
    some current

private def attemptCompletion?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens) :
    Option (CountedState tokens (PhaseAOpen file tokens)) :=
  match completedEdge? (file := file) waiting finished with
  | none => some current
  | some (after, edge) =>
      let address : UnitAddress tokens :=
        .cubic .U03_completionAttempt
          (rawCompletionKey waiting finished)
      if address ∈ current.counter.usedRev then
        some current
      else do
        let attempted ← runMappedPrimitive? current address id
        let withItem ← insertRawItem? attempted .completion after
        insertRawEdge? withItem edge

private def attemptCompletionsWith?
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    List (DottedItem tokens) →
      CountedState tokens (PhaseAOpen file tokens) →
      Option (CountedState tokens (PhaseAOpen file tokens))
  | [], current => some current
  | other :: rest, current => do
      let forward ← attemptCompletion? current pivot other
      let reverse ←
        if other = pivot then
          some forward
        else
          attemptCompletion? forward other pivot
      attemptCompletionsWith? pivot rest reverse

private def processRawItem?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : DottedItem tokens)
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (CountedState tokens (PhaseAOpen file tokens)) := do
  let predicted ← attemptPredictions? item allProductionIds current
  let scanned ← attemptScan? owned predicted item
  attemptCompletionsWith? item scanned.payload.rawItems scanned

private def runPhaseAQueues?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Nat → CountedState tokens (PhaseAOpen file tokens) →
      Option (CountedState tokens (PhaseAOpen file tokens))
  | 0, current =>
      if current.payload.itemQueue.isEmpty &&
          current.payload.edgeQueue.isEmpty then
        some current
      else
        none
  | fuel + 1, current =>
      match current.payload.itemQueue with
      | _ :: _ =>
          match dequeueRawItem? current with
          | none => none
          | some (item, afterDequeue) => do
              let processed ← processRawItem? owned item afterDequeue
              runPhaseAQueues? owned fuel processed
      | [] =>
          match current.payload.edgeQueue with
          | _ :: _ =>
              match dequeueRawEdge? current with
              | none => none
              | some (_, afterDequeue) =>
                  runPhaseAQueues? owned fuel afterDequeue
          | [] => some current

private def executePhaseA?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    Option (CountedState tokens (PhaseAOpen file tokens)) := do
  let seeded ← insertRawSeeds? (rawSeedItems tokens)
    (beginPhaseA file tokens)
  runPhaseAQueues? owned (chartGBound (tokens.length + 1)) seeded

private theorem runPhaseAQueues?_queues_empty
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result : CountedState tokens (PhaseAOpen file tokens)),
      runPhaseAQueues? owned fuel current = some result →
        result.payload.itemQueue = [] ∧
          result.payload.edgeQueue = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result selected
      rw [runPhaseAQueues?] at selected
      split at selected
      · cases selected
        rename_i condition
        have queues := Bool.and_eq_true_iff.mp condition
        exact ⟨List.isEmpty_iff.mp queues.1,
          List.isEmpty_iff.mp queues.2⟩
      · contradiction
  | succ previous induction =>
      intro current result selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact ⟨items, edges⟩
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨dequeuedItem, afterDequeue⟩
              simp only at selected
              cases processing :
                  processRawItem? owned dequeuedItem afterDequeue with
              | none => simp [processing] at selected
              | some processed =>
                  rw [processing] at selected
                  exact induction processed result selected

private theorem rawSaturation_rule_closed
    {tokens : List Token} {item : DottedItem tokens}
    (selected : rawClosureBool tokens (rawSaturation tokens) item = true) :
    item ∈ rawSaturation tokens := by
  rw [← rawSaturation_stable]
  exact List.mem_filter.mpr ⟨allDottedItems_complete item, selected⟩

private theorem rawSaturation_seed_closed
    {tokens : List Token} {item : DottedItem tokens}
    (zero : item.dot.val = 0) (same : item.origin = item.current) :
    item ∈ rawSaturation tokens := by
  apply rawSaturation_rule_closed
  simp [rawClosureBool, rawSeedBool, zero, same]

private theorem rawSaturation_predict_closed
    {tokens : List Token} {waiting predicted : DottedItem tokens}
    (waitingMember : waiting ∈ rawSaturation tokens)
    (next : NextSymbol waiting (.nonterminal predicted.production.lhs))
    (zero : predicted.dot.val = 0)
    (origin : predicted.origin = waiting.current)
    (current : predicted.current = waiting.current) :
    predicted ∈ rawSaturation tokens := by
  apply rawSaturation_rule_closed
  simp only [rawClosureBool, Bool.or_eq_true]
  apply Or.inl
  apply Or.inl
  apply Or.inr
  rw [rawPredictBool, List.any_eq_true]
  refine ⟨waiting, waitingMember, ?_⟩
  rw [next.2]
  simp [zero, origin, current]

private theorem terminalValueAt?_of_terminalAt
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : TerminalCursor tokens} {value : TerminalStreamValue}
    {span : SourceSpan} (terminalAt : TerminalAt file tokens cursor value span) :
    terminalValueAt? tokens cursor = some value := by
  cases terminalAt with
  | retained token inRange lookup valid =>
      have tokenEq : tokens[cursor.val] = token :=
        Option.some.inj
          ((List.getElem?_eq_getElem inRange).symm.trans lookup)
      simp [terminalValueAt?, inRange, tokenEq]
  | endOfFile atEnd =>
      have outside : ¬ cursor.val < tokens.length := by omega
      simp [terminalValueAt?, outside]

private theorem rawSaturation_scan_closed
    {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens} {cursor : TerminalCursor tokens}
    (beforeMember : before ∈ rawSaturation tokens)
    (valid : PackedEdgeKey.Valid file tokens (.scanned before after cursor)) :
    after ∈ rawSaturation tokens := by
  rcases valid with ⟨terminal, value, span, next, atCurrent,
    terminalAt, matched, advance⟩
  apply rawSaturation_rule_closed
  simp only [rawClosureBool, Bool.or_eq_true]
  apply Or.inl
  apply Or.inr
  rw [rawScanBool, List.any_eq_true]
  refine ⟨before, beforeMember, ?_⟩
  have inRange : before.current.val < tokens.length + 1 := by
    rw [← atCurrent]
    exact cursor.isLt
  rw [dif_pos inRange]
  let computed : TerminalCursor tokens := ⟨before.current.val, inRange⟩
  have computedEq : computed = cursor := by
    apply Fin.ext
    exact congrArg Fin.val atCurrent |>.symm
  rw [next.2]
  have observed : terminalValueAt? tokens
      (⟨before.current.val, inRange⟩ : TerminalCursor tokens) = some value := by
    change terminalValueAt? tokens computed = some value
    rw [computedEq]
    exact terminalValueAt?_of_terminalAt terminalAt
  simp only
  rw [observed]
  have accepted : terminalMatchesBool terminal value = true :=
    (terminalMatchesBool_eq_true_iff terminal value).mpr matched
  have afterEq : cursor.afterBoundary =
      TerminalCursor.afterBoundary
        (⟨before.current.val, inRange⟩ : TerminalCursor tokens) :=
    congrArg TerminalCursor.afterBoundary computedEq.symm
  rcases advance with ⟨production, dot, origin, current⟩
  simp [accepted, production, dot, origin, current, afterEq]

private theorem rawSaturation_complete_closed
    {tokens : List Token} {waiting finished after : DottedItem tokens}
    (waitingMember : waiting ∈ rawSaturation tokens)
    (finishedMember : finished ∈ rawSaturation tokens)
    (next : NextSymbol waiting
      (.nonterminal finished.production.lhs))
    (complete : CompleteItem finished)
    (same : waiting.current = finished.origin)
    (advance : AdvanceItem waiting finished.current after) :
    after ∈ rawSaturation tokens := by
  apply rawSaturation_rule_closed
  simp only [rawClosureBool, Bool.or_eq_true]
  apply Or.inr
  rw [rawCompleteBool, List.any_eq_true]
  refine ⟨waiting, waitingMember, ?_⟩
  rw [List.any_eq_true]
  refine ⟨finished, finishedMember, ?_⟩
  unfold CompleteItem at complete
  rcases advance with ⟨production, dot, origin, current⟩
  simp [next.2, complete, same, production, dot, origin, current]

private theorem rawMemberBool_true_iff
    {tokens : List Token} (items : List (DottedItem tokens))
    (item : DottedItem tokens) :
    rawMemberBool items item = true ↔ item ∈ items := by
  rw [rawMemberBool, List.any_eq_true]
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨candidate, member, rfl⟩
    exact member
  · intro member
    exact ⟨item, member, rfl⟩

private theorem rawClosureBool_mono
    {tokens : List Token} {left right : List (DottedItem tokens)}
    (subset : left ⊆ right) (item : DottedItem tokens)
    (selected : rawClosureBool tokens left item = true) :
    rawClosureBool tokens right item = true := by
  simp only [rawClosureBool, Bool.or_eq_true] at selected ⊢
  rcases selected with beforeComplete | completed
  rcases beforeComplete with beforeScan | scanned
  rcases beforeScan with beforePredict | predicted
  rcases beforePredict with carried | seeded
  · exact Or.inl (Or.inl (Or.inl (Or.inl
      ((rawMemberBool_true_iff right item).mpr
        (subset ((rawMemberBool_true_iff left item).mp carried))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr seeded)))
  · apply Or.inl
    apply Or.inl
    apply Or.inr
    rw [rawPredictBool, List.any_eq_true] at predicted ⊢
    rcases predicted with ⟨waiting, member, accepted⟩
    exact ⟨waiting, subset member, accepted⟩
  · apply Or.inl
    apply Or.inr
    rw [rawScanBool, List.any_eq_true] at scanned ⊢
    rcases scanned with ⟨before, member, accepted⟩
    exact ⟨before, subset member, accepted⟩
  · apply Or.inr
    rw [rawCompleteBool, List.any_eq_true] at completed ⊢
    rcases completed with ⟨waiting, waitingMember, accepted⟩
    refine ⟨waiting, subset waitingMember, ?_⟩
    rw [List.any_eq_true] at accepted ⊢
    rcases accepted with ⟨finished, finishedMember, accepted⟩
    exact ⟨finished, subset finishedMember, accepted⟩

private theorem rawSaturation_subset_of_closed
    {tokens : List Token} {items : List (DottedItem tokens)}
    (closed : ∀ item,
      rawClosureBool tokens items item = true → item ∈ items) :
    ∀ item, item ∈ rawSaturation tokens → item ∈ items := by
  have stages : ∀ stage item,
      item ∈ closureIterate (rawClosureStep tokens) stage →
        item ∈ items := by
    intro stage
    induction stage with
    | zero =>
        intro item member
        simp [closureIterate] at member
    | succ previous induction =>
        intro item member
        rw [closureIterate, rawClosureStep, List.mem_filter] at member
        apply closed item
        exact rawClosureBool_mono (fun candidate candidateMember =>
          induction candidate candidateMember) item member.2
  intro item member
  exact stages (allDottedItems tokens).length item member

private theorem rawItems_membership_eq_rawSaturation
    {tokens : List Token} {items : List (DottedItem tokens)}
    (sound : ∀ item, item ∈ items → item ∈ rawSaturation tokens)
    (closed : ∀ item,
      rawClosureBool tokens items item = true → item ∈ items) :
    ∀ item, item ∈ items ↔ item ∈ rawSaturation tokens := by
  intro item
  exact ⟨sound item, rawSaturation_subset_of_closed closed item⟩

private def RawEdgeSaturated
    {file : WorkspaceFile} {tokens : List Token}
    (edge : PackedEdge file tokens) : Prop :=
  match edge.val with
  | .scanned before after _ =>
      before ∈ rawSaturation tokens ∧ after ∈ rawSaturation tokens
  | .completed waiting finished after _ =>
      waiting ∈ rawSaturation tokens ∧
        finished ∈ rawSaturation tokens ∧
        after ∈ rawSaturation tokens

private def PhaseARawSound
    {file : WorkspaceFile} {tokens : List Token}
    (state : PhaseAOpen file tokens) : Prop :=
  (∀ item, item ∈ state.rawItems → item ∈ rawSaturation tokens) ∧
    (∀ item, item ∈ state.itemQueue → item ∈ rawSaturation tokens) ∧
    ∀ edge, edge ∈ state.rawEdges → RawEdgeSaturated edge

private theorem phaseA_runMappedPrimitive?_payload
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition = some result) :
    result.payload = transition current.payload := by
  unfold runMappedPrimitive? at selected
  split at selected
  · cases selected
    rfl
  · contradiction

private theorem beginPhaseA_rawSound
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseARawSound (beginPhaseA file tokens).payload := by
  simp [PhaseARawSound, beginPhaseA]

private theorem insertRawItem?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (invariant : PhaseARawSound current.payload)
    (sound : item ∈ rawSaturation tokens)
    (selected : insertRawItem? current source item = some result) :
    PhaseARawSound result.payload := by
  unfold insertRawItem? at selected
  split at selected
  · cases selected
    exact invariant
  · have payload := phaseA_runMappedPrimitive?_payload current
      (.linear source.unitKind (rawLinearKey item)) _ result selected
    rw [payload]
    rcases invariant with ⟨itemsSound, queueSound, edgesSound⟩
    constructor
    · intro candidate member
      rw [List.mem_append] at member
      exact member.elim (itemsSound candidate) (fun singleton => by
        have same := List.eq_of_mem_singleton singleton
        simpa [same] using sound)
    constructor
    · intro candidate member
      rw [List.mem_append] at member
      exact member.elim (queueSound candidate) (fun singleton => by
        have same := List.eq_of_mem_singleton singleton
        simpa [same] using sound)
    · exact edgesSound
private theorem insertRawEdge?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (invariant : PhaseARawSound current.payload)
    (sound : RawEdgeSaturated edge)
    (selected : insertRawEdge? current edge = some result) :
    PhaseARawSound result.payload := by
  unfold insertRawEdge? at selected
  split at selected
  · cases selected
    exact invariant
  · split at selected <;>
      have payload := phaseA_runMappedPrimitive?_payload current _ _ result selected
    all_goals
      rw [payload]
      rcases invariant with ⟨itemsSound, queueSound, edgesSound⟩
      refine ⟨itemsSound, queueSound, ?_⟩
      intro candidate member
      rw [List.mem_append] at member
      exact member.elim (edgesSound candidate) (fun singleton => by
        have same := List.eq_of_mem_singleton singleton
        simpa [same] using sound)

private theorem dequeueRawItem?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseARawSound current.payload)
    (selected : dequeueRawItem? current = some result) :
    result.1 ∈ rawSaturation tokens ∧
      PhaseARawSound result.2.payload := by
  unfold dequeueRawItem? at selected
  cases queueEq : current.payload.itemQueue with
  | nil => simp [queueEq] at selected
  | cons item rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := phaseA_runMappedPrimitive?_payload current
        (.linear .L01_itemDequeue (rawLinearKey item)) _ next nextEq
      constructor
      · exact invariant.2.1 item (by simp [queueEq])
      · rw [payload]
        refine ⟨invariant.1, ?_, invariant.2.2⟩
        intro candidate member
        exact invariant.2.1 candidate (by simp [queueEq, member])

private theorem dequeueRawEdge?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseARawSound current.payload)
    (selected : dequeueRawEdge? current = some result) :
    PhaseARawSound result.2.payload := by
  unfold dequeueRawEdge? at selected
  cases queueEq : current.payload.edgeQueue with
  | nil => simp [queueEq] at selected
  | cons edge rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := phaseA_runMappedPrimitive?_payload current _ _ next nextEq
      rw [payload]
      exact invariant

private theorem rawSeedItems_saturated
    {tokens : List Token} {item : DottedItem tokens}
    (member : item ∈ rawSeedItems tokens) :
    item ∈ rawSaturation tokens := by
  rw [rawSeedItems, List.mem_filter] at member
  have selected := member.2
  simp only [rawSeedBool, Bool.and_eq_true, beq_iff_eq] at selected
  exact rawSaturation_seed_closed selected.1 selected.2

private theorem insertRawSeeds?_rawSound
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      (∀ item, item ∈ seeds → item ∈ rawSaturation tokens) →
      PhaseARawSound current.payload →
      insertRawSeeds? seeds current = some result →
      PhaseARawSound result.payload := by
  intro seeds
  induction seeds with
  | nil =>
      intro current result _ invariant selected
      cases selected
      exact invariant
  | cons head tail induction =>
      intro current result seedsSound invariant selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (fun item member => seedsSound item (by simp [member]))
        (insertRawItem?_rawSound current next .seedOrPrediction head
          invariant (seedsSound head (by simp)) nextEq) restEq

private theorem predictedItem?_saturated
    {tokens : List Token} {waiting result : DottedItem tokens}
    {predicted : ProductionId}
    (waitingSound : waiting ∈ rawSaturation tokens)
    (selected : predictedItem? waiting predicted = some result) :
    result ∈ rawSaturation tokens := by
  unfold predictedItem? at selected
  split at selected
  next symbol nextEq =>
    split at selected
    next sameLhs =>
      cases selected
      apply rawSaturation_predict_closed waitingSound
      · rcases List.getElem?_eq_some_iff.mp nextEq with ⟨bound, lookup⟩
        exact ⟨bound, by simpa [sameLhs] using nextEq⟩
      · rfl
      · rfl
      · rfl
    next different => contradiction
  next => contradiction

private theorem attemptPrediction?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId)
    (invariant : PhaseARawSound current.payload)
    (waitingSound : waiting ∈ rawSaturation tokens)
    (selected : attemptPrediction? current waiting predicted = some result) :
    PhaseARawSound result.payload := by
  unfold attemptPrediction? at selected
  cases predictedEq : predictedItem? waiting predicted with
  | none =>
      simp only [predictedEq, Option.some.injEq] at selected
      cases selected
      exact invariant
  | some item =>
      simp only [predictedEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      have attemptedPayload := phaseA_runMappedPrimitive?_payload current
        (.prediction .R01_predictionAttempt
          (rawPredictionKey waiting predicted)) id attempted attemptedEq
      apply insertRawItem?_rawSound attempted result .seedOrPrediction item
      · simpa [attemptedPayload] using invariant
      · exact predictedItem?_saturated waitingSound predictedEq
      · exact insertedEq

private theorem attemptPredictions?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions
      (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseARawSound current.payload →
      waiting ∈ rawSaturation tokens →
      attemptPredictions? waiting productions current = some result →
      PhaseARawSound result.payload := by
  intro productions
  induction productions with
  | nil =>
      intro current result invariant _ selected
      cases selected
      exact invariant
  | cons predicted rest induction =>
      intro current result invariant waitingSound selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (attemptPrediction?_rawSound current next waiting predicted
          invariant waitingSound nextEq) waitingSound restEq
private theorem scannedEdge?_shape
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (before after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (selected : scannedEdge? owned before = some (after, edge)) :
    ∃ cursor, edge.val = .scanned before after cursor := by
  unfold scannedEdge? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  simp only at selected
  split at selected <;> try contradiction
  next matched matchEq =>
    cases selected
    exact ⟨_, rfl⟩
private theorem completedEdge?_shape
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (selected : completedEdge? waiting finished = some (after, edge)) :
    ∃ shared, edge.val = .completed waiting finished after shared := by
  unfold completedEdge? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  next sameCursor =>
    cases selected
    exact ⟨waiting.current, rfl⟩
private theorem scannedEdge?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (before after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (beforeSound : before ∈ rawSaturation tokens)
    (selected : scannedEdge? owned before = some (after, edge)) :
    after ∈ rawSaturation tokens ∧ RawEdgeSaturated edge := by
  obtain ⟨cursor, shape⟩ := scannedEdge?_shape owned before after edge selected
  have valid : PackedEdgeKey.Valid file tokens
      (.scanned before after cursor) := by
    rw [← shape]
    exact edge.property
  have afterSound := rawSaturation_scan_closed beforeSound valid
  refine ⟨afterSound, ?_⟩
  rw [RawEdgeSaturated, shape]
  exact ⟨beforeSound, afterSound⟩
private theorem completedEdge?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (waitingSound : waiting ∈ rawSaturation tokens)
    (finishedSound : finished ∈ rawSaturation tokens)
    (selected : completedEdge? waiting finished = some (after, edge)) :
    after ∈ rawSaturation tokens ∧ RawEdgeSaturated edge := by
  obtain ⟨shared, shape⟩ := completedEdge?_shape
    waiting finished after edge selected
  have valid : PackedEdgeKey.Valid file tokens
      (.completed waiting finished after shared) := by
    rw [← shape]
    exact edge.property
  rcases valid with ⟨symbol, next, complete, lhs,
    waitingAtShared, finishedAtShared, advance⟩
  have exactNext : NextSymbol waiting
      (.nonterminal finished.production.lhs) := by
    simpa [lhs] using next
  have same : waiting.current = finished.origin :=
    waitingAtShared.trans finishedAtShared.symm
  have afterSound := rawSaturation_complete_closed waitingSound finishedSound
    exactNext complete same advance
  refine ⟨afterSound, ?_⟩
  rw [RawEdgeSaturated, shape]
  exact ⟨waitingSound, finishedSound, afterSound⟩
private theorem attemptScan?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (invariant : PhaseARawSound current.payload)
    (beforeSound : before ∈ rawSaturation tokens)
    (selected : attemptScan? owned current before = some result) :
    PhaseARawSound result.payload := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedPayload := phaseA_runMappedPrimitive?_payload current
      (.linear .L04_scanAttempt (rawLinearKey before)) id
      attempted attemptedEq
    have attemptedSound : PhaseARawSound attempted.payload := by
      simpa [attemptedPayload] using invariant
    cases scanEq : scannedEdge? owned before with
    | none =>
        simp only [scanEq, Option.some.injEq] at remainder
        cases remainder
        exact attemptedSound
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scanEq, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have edgeSound := scannedEdge?_rawSound owned before after edge
          beforeSound scanEq
        exact insertRawEdge?_rawSound withItem result edge
          (insertRawItem?_rawSound attempted withItem .scan after
            attemptedSound edgeSound.1 itemEq) edgeSound.2 edgeEq
  next notApplicable =>
    cases selected
    exact invariant
private theorem attemptCompletion?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (invariant : PhaseARawSound current.payload)
    (waitingSound : waiting ∈ rawSaturation tokens)
    (finishedSound : finished ∈ rawSaturation tokens)
    (selected : attemptCompletion? current waiting finished = some result) :
    PhaseARawSound result.payload := by
  unfold attemptCompletion? at selected
  cases completionEq : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completionEq, Option.some.injEq] at selected
      cases selected
      exact invariant
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completionEq] at selected
      split at selected
      next attemptedBefore =>
        cases selected
        exact invariant
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq,
          withItem, itemEq, edgeEq⟩
        have attemptedPayload := phaseA_runMappedPrimitive?_payload current
          _ id attempted attemptedEq
        have attemptedSound : PhaseARawSound attempted.payload := by
          simpa [attemptedPayload] using invariant
        have edgeSound := completedEdge?_rawSound waiting finished after edge
          waitingSound finishedSound completionEq
        exact insertRawEdge?_rawSound withItem result edge
          (insertRawItem?_rawSound attempted withItem .completion after
            attemptedSound edgeSound.1 itemEq) edgeSound.2 edgeEq
private theorem attemptCompletionsWith?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseARawSound current.payload →
      pivot ∈ rawSaturation tokens →
      (∀ other, other ∈ others → other ∈ rawSaturation tokens) →
      attemptCompletionsWith? pivot others current = some result →
      PhaseARawSound result.payload := by
  intro others
  induction others with
  | nil =>
      intro current result invariant _ _ selected
      cases selected
      exact invariant
  | cons other rest induction =>
      intro current result invariant pivotSound othersSound selected
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have otherSound := othersSound other (by simp)
          have forwardSound := attemptCompletion?_rawSound
            current forward pivot other invariant pivotSound otherSound
              forwardEq
          split at selected
          next same =>
            exact induction forward result forwardSound pivotSound
              (fun item member => othersSound item (by simp [member]))
              selected
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact induction reverse result
                  (attemptCompletion?_rawSound forward reverse other pivot
                    forwardSound otherSound pivotSound reverseEq)
                  pivotSound
                  (fun item member => othersSound item (by simp [member]))
                  selected
private theorem processRawItem?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseARawSound current.payload)
    (itemSound : item ∈ rawSaturation tokens)
    (selected : processRawItem? owned item current = some result) :
    PhaseARawSound result.payload := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completionEq⟩
  have predictedSound := attemptPredictions?_rawSound item
    allProductionIds current predicted invariant itemSound predictedEq
  have scannedSound := attemptScan?_rawSound owned predicted scanned item
    predictedSound itemSound scannedEq
  exact attemptCompletionsWith?_rawSound item scanned.payload.rawItems
    scanned result scannedSound itemSound scannedSound.1 completionEq
private theorem runPhaseAQueues?_rawSound
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseARawSound current.payload →
      runPhaseAQueues? owned fuel current = some result →
      PhaseARawSound result.payload := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runPhaseAQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact invariant
  | succ fuel induction =>
      intro current result invariant selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact invariant
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueRawEdge?_rawSound current pair invariant dequeued)
                    selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processed : processRawItem? owned pivot afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  have dequeuedSound := dequeueRawItem?_rawSound current
                    (pivot, afterDequeue) invariant dequeued
                  exact induction next result
                    (processRawItem?_rawSound owned pivot afterDequeue next
                      dequeuedSound.2 dequeuedSound.1 processed) selected
private theorem executePhaseA?_rawSound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    PhaseARawSound result.payload := by
  unfold executePhaseA? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨seeded, seededEq, runEq⟩
  have seededSound := insertRawSeeds?_rawSound
    (rawSeedItems tokens) (beginPhaseA file tokens) seeded
    (fun item member => rawSeedItems_saturated member)
    (beginPhaseA_rawSound file tokens) seededEq
  exact runPhaseAQueues?_rawSound owned _ seeded result seededSound runEq

private theorem dottedItem_eq_of_fields
    {tokens : List Token} {left right : DottedItem tokens}
    (production : left.production = right.production)
    (dot : left.dot.val = right.dot.val)
    (origin : left.origin = right.origin)
    (current : left.current = right.current) : left = right := by
  cases left
  cases right
  simp only at production dot origin current
  subst_vars
  congr
  exact Fin.ext dot

private theorem terminalValueAt?_terminalAt
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (cursor : TerminalCursor tokens)
    {value : TerminalStreamValue}
    (selected : terminalValueAt? tokens cursor = some value) :
    ∃ span, TerminalAt file tokens cursor value span := by
  unfold terminalValueAt? at selected
  split at selected
  next inRange =>
    cases selected
    exact ⟨tokens[cursor.val].span, .retained cursor tokens[cursor.val]
      inRange (List.getElem?_eq_getElem inRange)
      (owned tokens[cursor.val] (List.getElem_mem inRange))⟩
  next outside =>
    cases selected
    have atEnd : cursor.val = tokens.length := by omega
    exact ⟨{
      source := file.id
      startByte := file.content.utf8ByteSize
      endByte := file.content.utf8ByteSize
    }, .endOfFile cursor atEnd⟩

private theorem rawPredictBool_witness
    {tokens : List Token} (known : List (DottedItem tokens))
    (predicted : DottedItem tokens)
    (selected : rawPredictBool known predicted = true) :
    ∃ waiting, waiting ∈ known ∧
      predictedItem? waiting predicted.production = some predicted := by
  rw [rawPredictBool, List.any_eq_true] at selected
  rcases selected with ⟨waiting, member, accepted⟩
  cases nextEq : waiting.production.rhs[waiting.dot.val]? with
  | none => simp [nextEq] at accepted
  | some symbol =>
      cases symbol with
      | terminal terminal => simp [nextEq] at accepted
      | nonterminal symbol =>
          simp only [nextEq, Bool.and_eq_true, beq_iff_eq] at accepted
          rcases accepted with
            ⟨⟨⟨zero, origin⟩, current⟩, sameLhs⟩
          let expected : DottedItem tokens := {
            production := predicted.production
            dot := ⟨0, Nat.zero_lt_succ _⟩
            origin := waiting.current
            current := waiting.current
          }
          have expectedEq : expected = predicted :=
            dottedItem_eq_of_fields rfl zero.symm origin.symm current.symm
          refine ⟨waiting, member, ?_⟩
          unfold predictedItem?
          rw [nextEq]
          simp only
          rw [dif_pos sameLhs]
          exact congrArg some expectedEq

private theorem rawCompleteBool_witness
    {file : WorkspaceFile} {tokens : List Token}
    (known : List (DottedItem tokens)) (after : DottedItem tokens)
    (selected : rawCompleteBool known after = true) :
    ∃ waiting, waiting ∈ known ∧ ∃ finished, finished ∈ known ∧
      ∃ edge : PackedEdge file tokens,
        completedEdge? waiting finished = some (after, edge) := by
  rw [rawCompleteBool, List.any_eq_true] at selected
  rcases selected with ⟨waiting, waitingMember, selected⟩
  rw [List.any_eq_true] at selected
  rcases selected with ⟨finished, finishedMember, accepted⟩
  cases nextEq : waiting.production.rhs[waiting.dot.val]? with
  | none => simp [nextEq] at accepted
  | some symbol =>
      cases symbol with
      | terminal terminal => simp [nextEq] at accepted
      | nonterminal symbol =>
          simp only [nextEq, Bool.and_eq_true, beq_iff_eq] at accepted
          rcases accepted with
            ⟨⟨⟨⟨⟨⟨sameLhs, complete⟩, sameCursor⟩,
              production⟩, dot⟩, origin⟩, current⟩
          rcases List.getElem?_eq_some_iff.mp nextEq with
            ⟨nextInRange, nextGet⟩
          let expected : DottedItem tokens := {
            production := waiting.production
            dot := ⟨waiting.dot.val + 1, by omega⟩
            origin := waiting.origin
            current := finished.current
          }
          have expectedEq : expected = after :=
            dottedItem_eq_of_fields production.symm dot.symm
              origin.symm current.symm
          refine ⟨waiting, waitingMember, finished, finishedMember, ?_⟩
          rw [← expectedEq]
          unfold completedEdge?
          rw [dif_pos nextInRange]
          split <;> simp_all [expected]

private theorem rawScanBool_witness
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (known : List (DottedItem tokens)) (after : DottedItem tokens)
    (selected : rawScanBool known after = true) :
    ∃ before, before ∈ known ∧ ∃ edge : PackedEdge file tokens,
      scannedEdge? owned before = some (after, edge) := by
  rw [rawScanBool, List.any_eq_true] at selected
  rcases selected with ⟨before, beforeMember, accepted⟩
  split at accepted
  next currentInRange =>
    let cursor : TerminalCursor tokens :=
      ⟨before.current.val, currentInRange⟩
    cases nextEq : before.production.rhs[before.dot.val]? with
    | none => simp [nextEq] at accepted
    | some symbol =>
        cases symbol with
        | nonterminal symbol => simp [nextEq] at accepted
        | terminal terminal =>
            cases valueEq : terminalValueAt? tokens cursor with
            | none => simp [nextEq, cursor, valueEq] at accepted
            | some value =>
                simp only [nextEq, cursor, valueEq, Bool.and_eq_true,
                  beq_iff_eq] at accepted
                rcases accepted with
                  ⟨⟨⟨⟨matched, production⟩, dot⟩, origin⟩, current⟩
                rcases List.getElem?_eq_some_iff.mp nextEq with
                  ⟨nextInRange, nextGet⟩
                obtain ⟨span, terminalAt⟩ :=
                  terminalValueAt?_terminalAt owned cursor valueEq
                have terminalMatches : TerminalMatches terminal value :=
                  (terminalMatchesBool_eq_true_iff terminal value).mp matched
                obtain ⟨matchedResult, matchedEq⟩ :=
                  MatchedTerminal.atCursor?_complete owned terminal cursor
                    terminalAt terminalMatches
                let expected : DottedItem tokens := {
                  production := before.production
                  dot := ⟨before.dot.val + 1, by omega⟩
                  origin := before.origin
                  current := cursor.afterBoundary
                }
                have expectedEq : expected = after :=
                  dottedItem_eq_of_fields production.symm dot.symm
                    origin.symm current.symm
                have valid : PackedEdgeKey.Valid file tokens
                    (.scanned before after cursor) :=
                  packedEdge_scanned_valid_iff.mpr ⟨{
                    terminal := terminal
                    matched := matchedResult.val
                    sameCursor := matchedResult.property
                    next := ⟨nextInRange, nextEq⟩
                    atCurrent := Fin.ext rfl
                    advance := ⟨production, dot, origin, by
                      rw [matchedResult.property]
                      exact current⟩
                  }⟩
                refine ⟨before, beforeMember, ?_⟩
                rw [← expectedEq]
                unfold scannedEdge?
                rw [dif_pos nextInRange]
                split <;> simp_all [expected, cursor]
                all_goals
                  subst_vars
                  rw [matchedEq]
                  simp
                  simpa [cursor] using valid
  next outside => contradiction
private def ExecutableRawClosed
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (items : List (DottedItem tokens)) : Prop :=
  (∀ item, item ∈ rawSeedItems tokens → item ∈ items) ∧
  (∀ waiting, waiting ∈ items → ∀ production result,
    predictedItem? waiting production = some result → result ∈ items) ∧
  (∀ before, before ∈ items → ∀ after (edge : PackedEdge file tokens),
    scannedEdge? owned before = some (after, edge) → after ∈ items) ∧
  ∀ waiting, waiting ∈ items → ∀ finished, finished ∈ items →
    ∀ after (edge : PackedEdge file tokens),
      completedEdge? waiting finished = some (after, edge) →
      after ∈ items

private theorem ExecutableRawClosed.rawClosureBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (items : List (DottedItem tokens))
    (closed : ExecutableRawClosed owned items) :
    ∀ item, rawClosureBool tokens items item = true → item ∈ items := by
  intro item selected
  unfold Chart.rawClosureBool at selected
  simp only [Bool.or_eq_true] at selected
  rcases selected with beforeComplete | completed
  rcases beforeComplete with beforeScan | scanned
  rcases beforeScan with beforePredict | predicted
  rcases beforePredict with carried | seeded
  · exact (rawMemberBool_true_iff items item).mp carried
  · apply closed.1 item
    rw [rawSeedItems, List.mem_filter]
    exact ⟨allDottedItems_complete item, seeded⟩
  · obtain ⟨waiting, waitingMember, computed⟩ :=
      rawPredictBool_witness items item predicted
    exact closed.2.1 waiting waitingMember item.production item computed
  · obtain ⟨before, beforeMember, edge, computed⟩ :=
      rawScanBool_witness owned items item scanned
    exact closed.2.2.1 before beforeMember item edge computed
  · obtain ⟨waiting, waitingMember, finished, finishedMember,
      edge, computed⟩ := rawCompleteBool_witness
        (file := file) items item completed
    exact closed.2.2.2 waiting waitingMember finished finishedMember
      item edge computed

private theorem executePhaseA?_membership_eq_of_closed
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result)
    (closed : ExecutableRawClosed owned result.payload.rawItems) :
    ∀ item, item ∈ result.payload.rawItems ↔
      item ∈ rawSaturation tokens := by
  exact rawItems_membership_eq_rawSaturation
    (executePhaseA?_rawSound file tokens owned result selected).1
    (closed.rawClosureBool owned result.payload.rawItems)

private theorem insertRawItem?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (selected : insertRawItem? current source item = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold insertRawItem? at selected
  split at selected
  · cases selected
    exact Nat.le_refl _
  · rw [runMappedPrimitive?_units current _ _ selected]
    omega

private theorem insertRawEdge?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : insertRawEdge? current edge = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold insertRawEdge? at selected
  split at selected
  · cases selected
    exact Nat.le_refl _
  · split at selected <;>
      rw [runMappedPrimitive?_units current _ _ selected] <;> omega

private theorem insertRawSeeds?_units_mono
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      insertRawSeeds? seeds current = some result →
      current.counter.units ≤ result.counter.units := by
  intro seeds
  induction seeds with
  | nil =>
      intro current result selected
      cases selected
      exact Nat.le_refl _
  | cons item rest induction =>
      intro current result selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, inserted, continued⟩
      exact Nat.le_trans
        (insertRawItem?_units_mono current next .seedOrPrediction item inserted)
        (induction next result continued)

private theorem attemptPrediction?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId)
    (selected : attemptPrediction? current waiting predicted = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting predicted with
  | none =>
      simp only [prediction, Option.some.injEq] at selected
      cases selected
      exact Nat.le_refl _
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      have inserted := insertRawItem?_units_mono attempted result
        .seedOrPrediction item insertedEq
      rw [runMappedPrimitive?_units current _ _ attemptedEq] at inserted
      omega

private theorem attemptPredictions?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result : CountedState tokens (PhaseAOpen file tokens)),
      attemptPredictions? waiting productions current = some result →
      current.counter.units ≤ result.counter.units := by
  intro productions
  induction productions with
  | nil =>
      intro current result selected
      cases selected
      exact Nat.le_refl _
  | cons production rest induction =>
      intro current result selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact Nat.le_trans
        (attemptPrediction?_units_mono current next waiting production nextEq)
        (induction next result restEq)

private theorem attemptScan?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (selected : attemptScan? owned current before = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have first : current.counter.units ≤ attempted.counter.units := by
      rw [runMappedPrimitive?_units current _ _ attemptedEq]
      omega
    cases scanEq : scannedEdge? owned before with
    | none =>
        simp only [scanEq, Option.some.injEq] at remainder
        cases remainder
        exact first
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scanEq, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        exact Nat.le_trans first (Nat.le_trans
          (insertRawItem?_units_mono attempted withItem .scan after itemEq)
          (insertRawEdge?_units_mono withItem result edge edgeEq))
  next notApplicable =>
    cases selected
    exact Nat.le_refl _

private theorem attemptCompletion?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (selected : attemptCompletion? current waiting finished = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold attemptCompletion? at selected
  cases completionEq : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completionEq, Option.some.injEq] at selected
      cases selected
      exact Nat.le_refl _
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completionEq] at selected
      split at selected
      next attemptedBefore =>
        cases selected
        exact Nat.le_refl _
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq,
          withItem, itemEq, edgeEq⟩
        have first : current.counter.units ≤ attempted.counter.units := by
          rw [runMappedPrimitive?_units current _ _ attemptedEq]
          omega
        exact Nat.le_trans first (Nat.le_trans
          (insertRawItem?_units_mono attempted withItem .completion after itemEq)
          (insertRawEdge?_units_mono withItem result edge edgeEq))

private theorem attemptCompletionsWith?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current result : CountedState tokens (PhaseAOpen file tokens)),
      attemptCompletionsWith? pivot others current = some result →
      current.counter.units ≤ result.counter.units := by
  intro others
  induction others with
  | nil =>
      intro current result selected
      cases selected
      exact Nat.le_refl _
  | cons other rest induction =>
      intro current result selected
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have first := attemptCompletion?_units_mono current forward
            pivot other forwardEq
          split at selected
          next same => exact Nat.le_trans first (induction forward result selected)
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact Nat.le_trans first (Nat.le_trans
                  (attemptCompletion?_units_mono forward reverse
                    other pivot reverseEq)
                  (induction reverse result selected))

private theorem processRawItem?_units_mono
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (selected : processRawItem? owned item current = some result) :
    current.counter.units ≤ result.counter.units := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completionEq⟩
  exact Nat.le_trans
    (attemptPredictions?_units_mono item allProductionIds
      current predicted predictedEq)
    (Nat.le_trans (attemptScan?_units_mono owned predicted scanned item scannedEq)
      (attemptCompletionsWith?_units_mono item scanned.payload.rawItems
        scanned result completionEq))

private theorem dequeueRawItem?_units_exact
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (selected : dequeueRawItem? current = some result) :
    result.2.counter.units = current.counter.units + 1 := by
  unfold dequeueRawItem? at selected
  cases queueEq : current.payload.itemQueue with
  | nil => simp [queueEq] at selected
  | cons item rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      exact runMappedPrimitive?_units current _ _ nextEq

private theorem dequeueRawEdge?_units_exact
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (selected : dequeueRawEdge? current = some result) :
    result.2.counter.units = current.counter.units + 1 := by
  unfold dequeueRawEdge? at selected
  cases queueEq : current.payload.edgeQueue with
  | nil => simp [queueEq] at selected
  | cons edge rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      exact runMappedPrimitive?_units current _ _ nextEq

private inductive PhaseAQueueReachable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (start : CountedState tokens (PhaseAOpen file tokens)) :
    CountedState tokens (PhaseAOpen file tokens) → Prop where
  | refl : PhaseAQueueReachable owned start start
  | item
      {current after result : CountedState tokens (PhaseAOpen file tokens)}
      {pivot : DottedItem tokens}
      (prior : PhaseAQueueReachable owned start current)
      (dequeued : dequeueRawItem? current = some (pivot, after))
      (processed : processRawItem? owned pivot after = some result) :
      PhaseAQueueReachable owned start result
  | edge
      {current result : CountedState tokens (PhaseAOpen file tokens)}
      {edge : PackedEdge file tokens}
      (prior : PhaseAQueueReachable owned start current)
      (dequeued : dequeueRawEdge? current = some (edge, result)) :
      PhaseAQueueReachable owned start result

private def PhaseAQueueBlocked
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  match current.payload.itemQueue with
  | _ :: _ =>
      dequeueRawItem? current = none ∨
        ∃ pivot after,
          dequeueRawItem? current = some (pivot, after) ∧
            processRawItem? owned pivot after = none
  | [] =>
      match current.payload.edgeQueue with
      | _ :: _ => dequeueRawEdge? current = none
      | [] => False

private theorem runPhaseAQueues?_failure_is_operation_blocked
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (start : CountedState tokens (PhaseAOpen file tokens)) :
    ∀ fuel (current : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAQueueReachable owned start current →
      chartGBound (tokens.length + 1) < current.counter.units + fuel →
      runPhaseAQueues? owned fuel current = none →
      ∃ blocked, PhaseAQueueReachable owned start blocked ∧
        PhaseAQueueBlocked owned blocked := by
  intro fuel
  induction fuel with
  | zero =>
      intro current reachable budget selected
      have bound := current.counter.units_le_chartGBound
      omega
  | succ fuel induction =>
      intro current reachable budget selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil => simp [items, edges] at selected
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none =>
                  exact ⟨current, reachable, by
                    simp [PhaseAQueueBlocked, items, edges, dequeued]⟩
              | some pair =>
                  rw [dequeued] at selected
                  have units := dequeueRawEdge?_units_exact current pair dequeued
                  exact induction pair.2
                    (.edge reachable dequeued) (by omega) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none =>
              exact ⟨current, reachable, by
                simp [PhaseAQueueBlocked, items, dequeued]⟩
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, after⟩
              simp only at selected
              cases processed : processRawItem? owned pivot after with
              | none =>
                  refine ⟨current, reachable, ?_⟩
                  rw [PhaseAQueueBlocked, items]
                  exact Or.inr ⟨pivot, after, dequeued, processed⟩
              | some next =>
                  rw [processed] at selected
                  have dequeuedUnits := dequeueRawItem?_units_exact current
                    (pivot, after) dequeued
                  have processedUnits := processRawItem?_units_mono owned
                    pivot after next processed
                  have nextBudget : chartGBound (tokens.length + 1) <
                      next.counter.units + fuel := by
                    simp only at dequeuedUnits
                    omega
                  exact induction next (.item reachable dequeued processed)
                    nextBudget selected

set_option maxRecDepth 2048 in
private theorem executePhaseA?_failure_boundary
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (failed : executePhaseA? file tokens owned = none) :
    insertRawSeeds? (rawSeedItems tokens) (beginPhaseA file tokens) = none ∨
      ∃ seeded blocked,
        insertRawSeeds? (rawSeedItems tokens) (beginPhaseA file tokens) =
          some seeded ∧
        PhaseAQueueReachable owned seeded blocked ∧
        PhaseAQueueBlocked owned blocked := by
  unfold executePhaseA? at failed
  cases seededEq : insertRawSeeds? (rawSeedItems tokens)
      (beginPhaseA file tokens) with
  | none => exact Or.inl rfl
  | some seeded =>
      rw [seededEq] at failed
      have units := insertRawSeeds?_units_mono (rawSeedItems tokens)
        (beginPhaseA file tokens) seeded seededEq
      have positive : 0 < seeded.counter.units := by
        rw [beginPhaseA_units] at units
        omega
      have budget : chartGBound (tokens.length + 1) <
          seeded.counter.units + chartGBound (tokens.length + 1) := by
        simpa only [Nat.add_comm] using
          (Nat.lt_add_of_pos_right (n := chartGBound (tokens.length + 1))
            positive)
      obtain ⟨blocked, reachable, operationBlocked⟩ :=
        runPhaseAQueues?_failure_is_operation_blocked owned seeded
          (chartGBound (tokens.length + 1)) seeded .refl
          budget failed
      exact Or.inr ⟨seeded, blocked, rfl, reachable, operationBlocked⟩

private theorem insertRawItem?_coverage
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (selected : insertRawItem? current source item = some result) :
    current.payload.rawItems ⊆ result.payload.rawItems ∧
      current.payload.itemQueue ⊆ result.payload.itemQueue ∧
      item ∈ result.payload.rawItems := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact ⟨fun _ => id, fun _ => id,
      (rawMemberBool_true_iff current.payload.rawItems item).mp present⟩
  next absent =>
    have payload := phaseA_runMappedPrimitive?_payload current
      (.linear source.unitKind (rawLinearKey item)) _ result selected
    rw [payload]
    exact ⟨fun candidate member => by simp [member],
      fun candidate member => by simp [member], by simp⟩

private theorem insertRawEdge?_itemPayload
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : insertRawEdge? current edge = some result) :
    result.payload.rawItems = current.payload.rawItems ∧
      result.payload.itemQueue = current.payload.itemQueue := by
  unfold insertRawEdge? at selected
  split at selected
  · cases selected
    exact ⟨rfl, rfl⟩
  · split at selected <;>
      have payload := phaseA_runMappedPrimitive?_payload current _ _ result selected
    all_goals simp [payload]
private theorem insertRawEdge?_coverage
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : insertRawEdge? current edge = some result) :
    current.payload.rawEdges ⊆ result.payload.rawEdges ∧
      ∃ candidate, candidate ∈ result.payload.rawEdges ∧
        candidate.val = edge.val := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    rw [List.any_eq_true] at present
    rcases present with ⟨candidate, member, same⟩
    exact ⟨fun _ => id, candidate, member, by simpa using same⟩
  next absent =>
    split at selected <;>
      have payload := phaseA_runMappedPrimitive?_payload current _ _ result selected
    all_goals
      rw [payload]
      exact ⟨fun candidate member => by simp [member], edge, by simp⟩

private def CompletionAttemptLedgerMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  ∀ waiting finished after (edge : PackedEdge file tokens),
    completedEdge? waiting finished = some (after, edge) →
    (.cubic .U03_completionAttempt
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev →
    after ∈ current.payload.rawItems ∧
      ∃ candidate, candidate ∈ current.payload.rawEdges ∧
        candidate.val = edge.val

private theorem attemptCompletion?_materialization_boundary
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (computed : completedEdge? waiting finished = some (after, edge))
    (selected : attemptCompletion? current waiting finished = some result) :
    ((.cubic .U03_completionAttempt
        (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev ∧ result = current) ∨
      (after ∈ result.payload.rawItems ∧
        ∃ candidate, candidate ∈ result.payload.rawEdges ∧
          candidate.val = edge.val) := by
  unfold attemptCompletion? at selected
  rw [computed] at selected
  simp only at selected
  split at selected
  next used =>
    cases selected
    exact Or.inl ⟨used, rfl⟩
  next fresh =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq,
      withItem, itemEq, edgeEq⟩
    have itemCoverage := insertRawItem?_coverage attempted withItem
      .completion after itemEq
    have edgePayload := insertRawEdge?_itemPayload withItem result edge edgeEq
    have edgeCoverage := insertRawEdge?_coverage withItem result edge edgeEq
    exact Or.inr ⟨by
      rw [edgePayload.1]
      exact itemCoverage.2.2, edgeCoverage.2⟩

private theorem attemptCompletion?_materialized_of_ledger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (computed : completedEdge? waiting finished = some (after, edge))
    (selected : attemptCompletion? current waiting finished = some result) :
    after ∈ result.payload.rawItems ∧
      ∃ candidate, candidate ∈ result.payload.rawEdges ∧
        candidate.val = edge.val := by
  rcases attemptCompletion?_materialization_boundary current result
    waiting finished after edge computed selected with skipped | materialized
  · rw [skipped.2]
    exact ledger waiting finished after edge computed skipped.1
  · exact materialized

private theorem completedEdge?_finished_origin_eq
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (edge : PackedEdge file tokens)
    (selected : completedEdge? waiting finished = some (after, edge)) :
    finished.origin = waiting.current := by
  obtain ⟨shared, shape⟩ := completedEdge?_shape
    waiting finished after edge selected
  have valid : PackedEdgeKey.Valid file tokens
      (.completed waiting finished after shared) := by
    rw [← shape]
    exact edge.property
  rcases valid with ⟨_, _, _, _, waitingAtShared, finishedAtShared, _⟩
  exact finishedAtShared.trans waitingAtShared.symm

private theorem completedEdge?_eq_of_rawCompletionKey_eq
    {file : WorkspaceFile} {tokens : List Token}
    (leftWaiting leftFinished leftAfter : DottedItem tokens)
    (leftEdge : PackedEdge file tokens)
    (rightWaiting rightFinished rightAfter : DottedItem tokens)
    (rightEdge : PackedEdge file tokens)
    (leftSelected : completedEdge? leftWaiting leftFinished =
      some (leftAfter, leftEdge))
    (rightSelected : completedEdge? rightWaiting rightFinished =
      some (rightAfter, rightEdge))
    (keys : rawCompletionKey leftWaiting leftFinished =
      rawCompletionKey rightWaiting rightFinished) :
    leftAfter = rightAfter ∧ leftEdge = rightEdge := by
  have waitingEq : leftWaiting = rightWaiting :=
    dottedItem_eq_of_fields
      (congrArg (fun key => key.waiting.production) keys)
      (congrArg (fun key => key.waiting.dot.val) keys)
      (congrArg (fun key => key.origin) keys)
      (congrArg (fun key => key.shared) keys)
  have finishedOrigin : leftFinished.origin = rightFinished.origin := by
    rw [completedEdge?_finished_origin_eq leftWaiting leftFinished
      leftAfter leftEdge leftSelected,
      completedEdge?_finished_origin_eq rightWaiting rightFinished
        rightAfter rightEdge rightSelected, waitingEq]
  have finishedEq : leftFinished = rightFinished :=
    dottedItem_eq_of_fields
      (congrArg (fun key => key.finished.production) keys)
      (congrArg (fun key => key.finished.dot.val) keys)
      finishedOrigin
      (congrArg (fun key => key.current) keys)
  subst rightWaiting
  subst rightFinished
  rw [leftSelected] at rightSelected
  exact Prod.mk.inj (Option.some.inj rightSelected)

private def PhaseAContentSubset
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  before.payload.rawItems ⊆ after.payload.rawItems ∧
    before.payload.rawEdges ⊆ after.payload.rawEdges

private def CompletionAttemptAddressesSubset
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  ∀ waiting finished,
    (.cubic .U03_completionAttempt
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        after.counter.usedRev →
    (.cubic .U03_completionAttempt
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        before.counter.usedRev

private theorem PhaseAContentSubset.refl
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    PhaseAContentSubset current current :=
  ⟨fun _ => id, fun _ => id⟩

private theorem PhaseAContentSubset.trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : CountedState tokens (PhaseAOpen file tokens)}
    (left : PhaseAContentSubset first second)
    (right : PhaseAContentSubset second third) :
    PhaseAContentSubset first third :=
  ⟨fun _ member => right.1 (left.1 member),
    fun _ member => right.2 (left.2 member)⟩

private theorem CompletionAttemptAddressesSubset.refl
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    CompletionAttemptAddressesSubset current current :=
  fun _ _ => id

private theorem CompletionAttemptAddressesSubset.trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : CountedState tokens (PhaseAOpen file tokens)}
    (left : CompletionAttemptAddressesSubset first second)
    (right : CompletionAttemptAddressesSubset second third) :
    CompletionAttemptAddressesSubset first third :=
  fun waiting finished member => left waiting finished
    (right waiting finished member)

private theorem CompletionAttemptLedgerMaterialized.mono
    {file : WorkspaceFile} {tokens : List Token}
    {before after : CountedState tokens (PhaseAOpen file tokens)}
    (ledger : CompletionAttemptLedgerMaterialized before)
    (content : PhaseAContentSubset before after)
    (addresses : CompletionAttemptAddressesSubset before after) :
    CompletionAttemptLedgerMaterialized after := by
  intro waiting finished result edge computed used
  obtain ⟨itemMember, candidate, edgeMember, same⟩ :=
    ledger waiting finished result edge computed
      (addresses waiting finished used)
  exact ⟨content.1 itemMember, candidate, content.2 edgeMember, same⟩

private theorem phaseA_runMappedPrimitive?_usedRev
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition = some result) :
    result.counter.usedRev = address :: current.counter.usedRev := by
  unfold runMappedPrimitive? at selected
  split at selected
  next fresh =>
    cases selected
    rfl
  next collision => contradiction

private theorem runMappedPrimitive?_phaseA_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (address : UnitAddress tokens)
    (transition : PhaseAOpen file tokens → PhaseAOpen file tokens)
    (content : ∀ state,
      state.rawItems ⊆ (transition state).rawItems ∧
      state.rawEdges ⊆ (transition state).rawEdges)
    (notAttempt : ∀ waiting finished,
      address ≠ (.cubic .U03_completionAttempt
        (rawCompletionKey waiting finished) : UnitAddress tokens))
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesSubset current result := by
  have payload := phaseA_runMappedPrimitive?_payload current
    address transition result selected
  have used := phaseA_runMappedPrimitive?_usedRev current address transition
    result selected
  constructor
  · unfold PhaseAContentSubset
    rw [payload]
    exact content current.payload
  · intro waiting finished member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · exact (notAttempt waiting finished equal.symm).elim
    · exact old

private theorem insertRawItem?_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (selected : insertRawItem? current source item = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesSubset current result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current, .refl current⟩
  next absent =>
    apply runMappedPrimitive?_phaseA_subsets current result _ _ _ _ selected
    · intro state
      exact ⟨fun candidate member => by simp [member], fun _ => id⟩
    · intro waiting finished
      simp

private theorem insertRawItem?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : insertRawItem? current source item = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have subsets := insertRawItem?_subsets current result source item selected
  exact ledger.mono subsets.1 subsets.2

private theorem insertRawEdge?_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesSubset current result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current, .refl current⟩
  next absent =>
    split at selected <;>
      apply runMappedPrimitive?_phaseA_subsets current result _ _ _ _ selected <;>
      simp

private theorem insertRawEdge?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : insertRawEdge? current edge = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have subsets := insertRawEdge?_subsets current result edge selected
  exact ledger.mono subsets.1 subsets.2

private theorem dequeueRawItem?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : dequeueRawItem? current = some result) :
    CompletionAttemptLedgerMaterialized result.2 := by
  unfold dequeueRawItem? at selected
  cases queue : current.payload.itemQueue with
  | nil => simp [queue] at selected
  | cons item rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, stepped, output⟩
      cases output
      apply ledger.mono
      · exact (runMappedPrimitive?_phaseA_subsets current next _ _
          (by simp) (by simp) stepped).1
      · exact (runMappedPrimitive?_phaseA_subsets current next _ _
          (by simp) (by simp) stepped).2

private theorem dequeueRawEdge?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : dequeueRawEdge? current = some result) :
    CompletionAttemptLedgerMaterialized result.2 := by
  unfold dequeueRawEdge? at selected
  cases queue : current.payload.edgeQueue with
  | nil => simp [queue] at selected
  | cons edge rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, stepped, output⟩
      cases output
      have noAttempt : ∀ waiting finished,
          (match edge.val with
          | .scanned before _ _ =>
              .linear .L02_scannedEdgeDequeue (rawLinearKey before)
          | .completed waiting finished _ _ =>
              .cubic .U02_completedEdgeDequeue
                (rawCompletionKey waiting finished)) ≠
            (.cubic .U03_completionAttempt
              (rawCompletionKey waiting finished) : UnitAddress tokens) := by
        intro waiting finished
        cases edge.val <;> simp
      have subsets := runMappedPrimitive?_phaseA_subsets current next _ _
        (by simp) noAttempt stepped
      exact ledger.mono subsets.1 subsets.2

private theorem attemptPrediction?_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId)
    (selected : attemptPrediction? current waiting predicted = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesSubset current result := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting predicted with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact ⟨.refl current, .refl current⟩
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      have attemptedSubset := runMappedPrimitive?_phaseA_subsets current attempted
        _ id (by simp) (by simp) attemptedEq
      have inserted := insertRawItem?_subsets attempted result
        .seedOrPrediction item insertedEq
      exact ⟨attemptedSubset.1.trans inserted.1,
        attemptedSubset.2.trans inserted.2⟩

private theorem attemptPrediction?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : attemptPrediction? current waiting predicted = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have subsets := attemptPrediction?_subsets current result
    waiting predicted selected
  exact ledger.mono subsets.1 subsets.2

private theorem attemptPredictions?_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result :
      CountedState tokens (PhaseAOpen file tokens)),
      attemptPredictions? waiting productions current = some result →
      PhaseAContentSubset current result ∧
        CompletionAttemptAddressesSubset current result := by
  intro productions
  induction productions with
  | nil =>
      intro current result selected
      cases selected
      exact ⟨.refl current, .refl current⟩
  | cons production rest induction =>
      intro current result selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      have first := attemptPrediction?_subsets current next
        waiting production nextEq
      have remaining := induction next result restEq
      exact ⟨first.1.trans remaining.1, first.2.trans remaining.2⟩

private theorem attemptPredictions?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) (productions : List ProductionId)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : attemptPredictions? waiting productions current = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have subsets := attemptPredictions?_subsets waiting productions
    current result selected
  exact ledger.mono subsets.1 subsets.2

private theorem attemptScan?_subsets
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (selected : attemptScan? owned current before = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesSubset current result := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have first := runMappedPrimitive?_phaseA_subsets current attempted
      _ id (by simp) (by simp) attemptedEq
    cases scan : scannedEdge? owned before with
    | none =>
        simp only [scan] at remainder
        cases remainder
        exact first
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scan, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have itemSubset := insertRawItem?_subsets attempted withItem
          .scan after itemEq
        have edgeSubset := insertRawEdge?_subsets withItem result edge edgeEq
        exact ⟨first.1.trans (itemSubset.1.trans edgeSubset.1),
          first.2.trans (itemSubset.2.trans edgeSubset.2)⟩
  next notApplicable =>
    cases selected
    exact ⟨.refl current, .refl current⟩

private theorem attemptScan?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : attemptScan? owned current before = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have subsets := attemptScan?_subsets owned current result before selected
  exact ledger.mono subsets.1 subsets.2

private def CompletionAttemptAddressesExtendedBy
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens) : Prop :=
  ∀ candidateWaiting candidateFinished,
    (.cubic .U03_completionAttempt
      (rawCompletionKey candidateWaiting candidateFinished) :
        UnitAddress tokens) ∈ after.counter.usedRev →
    (.cubic .U03_completionAttempt
      (rawCompletionKey candidateWaiting candidateFinished) :
        UnitAddress tokens) ∈ before.counter.usedRev ∨
    (rawCompletionKey candidateWaiting candidateFinished =
        rawCompletionKey waiting finished ∧
      ∃ after edge, completedEdge? (file := file) waiting finished =
        some (after, edge))

private theorem attemptCompletion?_content_extension
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (selected : attemptCompletion? current waiting finished = some result) :
    PhaseAContentSubset current result ∧
      CompletionAttemptAddressesExtendedBy current result waiting finished := by
  unfold attemptCompletion? at selected
  cases completion : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completion] at selected
      cases selected
      exact ⟨.refl current, fun _ _ member => Or.inl member⟩
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completion] at selected
      split at selected
      next usedBefore =>
        cases selected
        exact ⟨.refl current, fun _ _ member => Or.inl member⟩
      next fresh =>
        simp only [Option.bind_eq_bind,
          Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq,
          withItem, itemEq, edgeEq⟩
        have attemptedContent : PhaseAContentSubset current attempted := by
          unfold PhaseAContentSubset
          rw [phaseA_runMappedPrimitive?_payload current _ id attempted
            attemptedEq]
          exact ⟨fun _ => id, fun _ => id⟩
        have itemSubset := insertRawItem?_subsets attempted withItem
          .completion after itemEq
        have edgeSubset := insertRawEdge?_subsets withItem result edge edgeEq
        constructor
        · exact attemptedContent.trans (itemSubset.1.trans edgeSubset.1)
        · intro candidateWaiting candidateFinished member
          have inAttempted := itemSubset.2 candidateWaiting candidateFinished
            (edgeSubset.2 candidateWaiting candidateFinished member)
          rw [phaseA_runMappedPrimitive?_usedRev current _ id attempted
            attemptedEq] at inAttempted
          simp only [List.mem_cons] at inAttempted
          rcases inAttempted with equal | old
          · right
            have keyEq : rawCompletionKey candidateWaiting candidateFinished =
                rawCompletionKey waiting finished := by
              simpa only [UnitAddress.cubic.injEq, true_and] using equal
            exact ⟨keyEq, after, edge, completion⟩
          · exact Or.inl old

private theorem attemptCompletion?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : attemptCompletion? current waiting finished = some result) :
    CompletionAttemptLedgerMaterialized result := by
  have extension := attemptCompletion?_content_extension current result
    waiting finished selected
  intro candidateWaiting candidateFinished after edge computed used
  rcases extension.2 candidateWaiting candidateFinished used with
    old | extended
  · obtain ⟨itemMember, candidate, edgeMember, same⟩ :=
      ledger candidateWaiting candidateFinished after edge computed old
    exact ⟨extension.1.1 itemMember,
      candidate, extension.1.2 edgeMember, same⟩
  · rcases extended with ⟨sameKey, actualAfter, actualEdge, completion⟩
    have sameResult := completedEdge?_eq_of_rawCompletionKey_eq
      candidateWaiting candidateFinished after edge
      waiting finished actualAfter actualEdge computed completion sameKey
    obtain ⟨actualItem, candidate, candidateMember, candidateSame⟩ :=
      attemptCompletion?_materialized_of_ledger current result
        waiting finished actualAfter actualEdge ledger completion selected
    rw [sameResult.1, sameResult.2]
    exact ⟨actualItem, candidate, candidateMember, candidateSame⟩

private theorem attemptCompletionsWith?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current result : CountedState tokens (PhaseAOpen file tokens)),
      CompletionAttemptLedgerMaterialized current →
      attemptCompletionsWith? pivot others current = some result →
      CompletionAttemptLedgerMaterialized result := by
  intro others
  induction others with
  | nil =>
      intro current result ledger selected
      cases selected
      exact ledger
  | cons other rest induction =>
      intro current result ledger selected
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardLedger := attemptCompletion?_completionLedger
            current forward pivot other ledger forwardEq
          split at selected
          next same => exact induction forward result forwardLedger selected
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact induction reverse result
                  (attemptCompletion?_completionLedger forward reverse
                    other pivot forwardLedger reverseEq) selected

private theorem processRawItem?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : processRawItem? owned item current = some result) :
    CompletionAttemptLedgerMaterialized result := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completedEq⟩
  exact attemptCompletionsWith?_completionLedger item
    scanned.payload.rawItems scanned result
    (attemptScan?_completionLedger owned predicted scanned item
      (attemptPredictions?_completionLedger item allProductionIds
        current predicted ledger predictedEq) scannedEq) completedEq

private theorem insertRawSeeds?_completionLedger
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      CompletionAttemptLedgerMaterialized current →
      insertRawSeeds? seeds current = some result →
      CompletionAttemptLedgerMaterialized result := by
  intro seeds
  induction seeds with
  | nil =>
      intro current result ledger selected
      cases selected
      exact ledger
  | cons item rest induction =>
      intro current result ledger selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (insertRawItem?_completionLedger current next .seedOrPrediction item
          ledger nextEq) restEq

private theorem beginPhaseA_completionLedger
    (file : WorkspaceFile) (tokens : List Token) :
    CompletionAttemptLedgerMaterialized (beginPhaseA file tokens) := by
  intro waiting finished after edge _ used
  simp [beginPhaseA, Counter.charge, Counter.empty] at used

private theorem runPhaseAQueues?_completionLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result : CountedState tokens (PhaseAOpen file tokens)),
      CompletionAttemptLedgerMaterialized current →
      runPhaseAQueues? owned fuel current = some result →
      CompletionAttemptLedgerMaterialized result := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result ledger selected
      rw [runPhaseAQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact ledger
  | succ fuel induction =>
      intro current result ledger selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact ledger
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueRawEdge?_completionLedger current pair ledger
                      dequeued) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processed : processRawItem? owned pivot afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  exact induction next result
                    (processRawItem?_completionLedger owned pivot
                      afterDequeue next
                      (dequeueRawItem?_completionLedger current
                        (pivot, afterDequeue) ledger dequeued) processed)
                    selected

private theorem executePhaseA?_completionLedger
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    CompletionAttemptLedgerMaterialized result := by
  unfold executePhaseA? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨seeded, seededEq, runEq⟩
  exact runPhaseAQueues?_completionLedger owned _ seeded result
    (insertRawSeeds?_completionLedger (rawSeedItems tokens)
      (beginPhaseA file tokens) seeded
      (beginPhaseA_completionLedger file tokens) seededEq) runEq

private def PhaseAItemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  before.payload.rawItems ⊆ after.payload.rawItems ∧
  before.payload.itemQueue ⊆ after.payload.itemQueue ∧
  ∀ item, item ∈ after.payload.rawItems →
    item ∈ before.payload.rawItems ∨ item ∈ after.payload.itemQueue

private theorem PhaseAItemGrowth.refl
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    PhaseAItemGrowth current current :=
  ⟨fun _ => id, fun _ => id, fun _item member => Or.inl member⟩

private theorem PhaseAItemGrowth.trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : CountedState tokens (PhaseAOpen file tokens)}
    (left : PhaseAItemGrowth first second)
    (right : PhaseAItemGrowth second third) :
    PhaseAItemGrowth first third := by
  refine ⟨fun item member => right.1 (left.1 member),
    fun item member => right.2.1 (left.2.1 member), ?_⟩
  intro item member
  rcases right.2.2 item member with middle | queued
  · rcases left.2.2 item middle with old | queued
    · exact Or.inl old
    · exact Or.inr (right.2.1 queued)
  · exact Or.inr queued

private theorem runMappedPrimitive?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (address : UnitAddress tokens)
    (transition : PhaseAOpen file tokens → PhaseAOpen file tokens)
    (growth : ∀ state,
      state.rawItems ⊆ (transition state).rawItems ∧
      state.itemQueue ⊆ (transition state).itemQueue ∧
      ∀ item, item ∈ (transition state).rawItems →
        item ∈ state.rawItems ∨ item ∈ (transition state).itemQueue)
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseAItemGrowth current result := by
  unfold PhaseAItemGrowth
  rw [phaseA_runMappedPrimitive?_payload current address transition
    result selected]
  exact growth current.payload

private theorem insertRawItem?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (selected : insertRawItem? current source item = some result) :
    PhaseAItemGrowth current result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact .refl current
  next absent =>
    apply runMappedPrimitive?_itemGrowth current result _ _ _ selected
    intro state
    refine ⟨fun candidate member => by simp [member],
      fun candidate member => by simp [member], ?_⟩
    intro candidate member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    exact member.elim Or.inl (fun equal => Or.inr (Or.inr equal))

private theorem insertRawEdge?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAItemGrowth current result := by
  have payload := insertRawEdge?_itemPayload current result edge selected
  unfold PhaseAItemGrowth
  rw [payload.1, payload.2]
  exact ⟨fun _ => id, fun _ => id, fun item member => Or.inl member⟩

private theorem attemptPrediction?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (selected : attemptPrediction? current waiting production = some result) :
    PhaseAItemGrowth current result := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting production with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact .refl current
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      exact (runMappedPrimitive?_itemGrowth current attempted _ id
        (by
          intro state
          exact ⟨fun _ => id, fun _ => id,
            fun _item member => Or.inl member⟩) attemptedEq).trans
          (insertRawItem?_itemGrowth attempted result
            .seedOrPrediction item insertedEq)

private theorem attemptPrediction?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting item : DottedItem tokens) (production : ProductionId)
    (computed : predictedItem? waiting production = some item)
    (selected : attemptPrediction? current waiting production = some result) :
    item ∈ result.payload.rawItems := by
  unfold attemptPrediction? at selected
  rw [computed] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
  exact (insertRawItem?_coverage attempted result
    .seedOrPrediction item insertedEq).2.2

private theorem attemptPredictions?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result :
      CountedState tokens (PhaseAOpen file tokens)),
      attemptPredictions? waiting productions current = some result →
      PhaseAItemGrowth current result := by
  intro productions
  induction productions with
  | nil =>
      intro current result selected
      cases selected
      exact .refl current
  | cons production rest induction =>
      intro current result selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact (attemptPrediction?_itemGrowth current next waiting production
        nextEq).trans (induction next result restEq)

private theorem attemptPredictions?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result :
      CountedState tokens (PhaseAOpen file tokens)),
      attemptPredictions? waiting productions current = some result →
      ∀ production, production ∈ productions →
      ∀ item, predictedItem? waiting production = some item →
        item ∈ result.payload.rawItems := by
  intro productions
  induction productions with
  | nil => simp
  | cons head rest induction =>
      intro current result selected production member item computed
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact (attemptPredictions?_itemGrowth waiting rest next result
          restEq).1 (attemptPrediction?_materializes current next waiting
            item production computed nextEq)
      · exact induction next result restEq production member item computed

private theorem attemptScan?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (selected : attemptScan? owned current before = some result) :
    PhaseAItemGrowth current result := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have first := runMappedPrimitive?_itemGrowth current attempted _ id
      (by
        intro state
        exact ⟨fun _ => id, fun _ => id,
          fun _item member => Or.inl member⟩) attemptedEq
    cases scan : scannedEdge? owned before with
    | none =>
        simp only [scan] at remainder
        cases remainder
        exact first
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scan, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        exact first.trans ((insertRawItem?_itemGrowth attempted withItem
          .scan after itemEq).trans
            (insertRawEdge?_itemGrowth withItem result edge edgeEq))
  next notApplicable =>
    cases selected
    exact .refl current

private theorem attemptScan?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before after : DottedItem tokens) (edge : PackedEdge file tokens)
    (computed : scannedEdge? owned before = some (after, edge))
    (selected : attemptScan? owned current before = some result) :
    after ∈ result.payload.rawItems := by
  unfold attemptScan? at selected
  have applicable : rawScanApplicable before = true := by
    unfold scannedEdge? at computed
    split at computed
    next nextInRange =>
      split at computed <;> try contradiction
      next terminal =>
        split at computed
        next currentInRange =>
          unfold rawScanApplicable
          rw [List.getElem?_eq_getElem nextInRange]
          simp_all
        next currentOutside => contradiction
    next nextOutside => contradiction
  rw [if_pos applicable] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, remainder⟩
  rw [computed] at remainder
  simp only [Option.bind_eq_some_iff] at remainder
  rcases remainder with ⟨withItem, itemEq, edgeEq⟩
  have itemMember := (insertRawItem?_coverage attempted withItem
    .scan after itemEq).2.2
  rw [(insertRawEdge?_itemPayload withItem result edge edgeEq).1]
  exact itemMember

private theorem attemptCompletion?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (selected : attemptCompletion? current waiting finished = some result) :
    PhaseAItemGrowth current result := by
  unfold attemptCompletion? at selected
  cases completion : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completion] at selected
      cases selected
      exact .refl current
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completion] at selected
      split at selected
      next used =>
        cases selected
        exact .refl current
      next fresh =>
        simp only [Option.bind_eq_bind,
          Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq,
          withItem, itemEq, edgeEq⟩
        exact (runMappedPrimitive?_itemGrowth current attempted _ id
          (by
            intro state
            exact ⟨fun _ => id, fun _ => id,
              fun _item member => Or.inl member⟩) attemptedEq).trans
          ((insertRawItem?_itemGrowth attempted withItem .completion
            after itemEq).trans
              (insertRawEdge?_itemGrowth withItem result edge edgeEq))

private theorem attemptCompletionsWith?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current result : CountedState tokens (PhaseAOpen file tokens)),
      attemptCompletionsWith? pivot others current = some result →
      PhaseAItemGrowth current result := by
  intro others
  induction others with
  | nil =>
      intro current result selected
      cases selected
      exact .refl current
  | cons other rest induction =>
      intro current result selected
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardGrowth := attemptCompletion?_itemGrowth
            current forward pivot other forwardEq
          split at selected
          next same =>
            exact forwardGrowth.trans (induction forward result selected)
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact forwardGrowth.trans
                  ((attemptCompletion?_itemGrowth forward reverse other pivot
                    reverseEq).trans (induction reverse result selected))

private theorem attemptCompletionsWith?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current result : CountedState tokens (PhaseAOpen file tokens)),
      CompletionAttemptLedgerMaterialized current →
      attemptCompletionsWith? pivot others current = some result →
      ∀ other, other ∈ others →
        (∀ after (edge : PackedEdge file tokens),
          completedEdge? pivot other = some (after, edge) →
          after ∈ result.payload.rawItems) ∧
        (∀ after (edge : PackedEdge file tokens),
          completedEdge? other pivot = some (after, edge) →
          after ∈ result.payload.rawItems) := by
  intro others
  induction others with
  | nil => simp
  | cons head rest induction =>
      intro current result ledger selected other member
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot head with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardLedger := attemptCompletion?_completionLedger
            current forward pivot head ledger forwardEq
          have forwardGrowth := attemptCompletion?_itemGrowth
            current forward pivot head forwardEq
          split at selected
          next same =>
            have restGrowth := attemptCompletionsWith?_itemGrowth pivot rest
              forward result selected
            rw [List.mem_cons] at member
            rcases member with equal | member
            · subst other
              constructor
              · intro after edge computed
                exact restGrowth.1
                  (attemptCompletion?_materialized_of_ledger current forward
                    pivot head after edge ledger computed forwardEq).1
              · intro after edge computed
                subst head
                exact restGrowth.1
                  (attemptCompletion?_materialized_of_ledger current forward
                    pivot pivot after edge ledger computed forwardEq).1
            · exact induction forward result forwardLedger selected
                other member
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward head pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                have reverseLedger := attemptCompletion?_completionLedger
                  forward reverse head pivot forwardLedger reverseEq
                have reverseGrowth := attemptCompletion?_itemGrowth
                  forward reverse head pivot reverseEq
                have restGrowth := attemptCompletionsWith?_itemGrowth
                  pivot rest reverse result selected
                rw [List.mem_cons] at member
                rcases member with equal | member
                · subst other
                  constructor
                  · intro after edge computed
                    exact restGrowth.1 (reverseGrowth.1
                      (attemptCompletion?_materialized_of_ledger current
                        forward pivot head after edge ledger computed
                          forwardEq).1)
                  · intro after edge computed
                    exact restGrowth.1
                      (attemptCompletion?_materialized_of_ledger forward
                        reverse head pivot after edge forwardLedger computed
                          reverseEq).1
                · exact induction reverse result reverseLedger selected
                    other member

private theorem processRawItem?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (selected : processRawItem? owned item current = some result) :
    PhaseAItemGrowth current result := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completedEq⟩
  exact (attemptPredictions?_itemGrowth item allProductionIds
    current predicted predictedEq).trans
    ((attemptScan?_itemGrowth owned predicted scanned item scannedEq).trans
      (attemptCompletionsWith?_itemGrowth item scanned.payload.rawItems
        scanned result completedEq))

private theorem processRawItem?_prediction_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (pivot after : DottedItem tokens) (production : ProductionId)
    (computed : predictedItem? pivot production = some after)
    (selected : processRawItem? owned pivot current = some result) :
    after ∈ result.payload.rawItems := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completedEq⟩
  have predictedMember := attemptPredictions?_materializes pivot
    allProductionIds current predicted predictedEq production
      (Grammar.allProductionIds_complete production) after computed
  exact (attemptCompletionsWith?_itemGrowth pivot scanned.payload.rawItems
    scanned result completedEq).1
      ((attemptScan?_itemGrowth owned predicted scanned pivot scannedEq).1
        predictedMember)

private theorem processRawItem?_scan_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (pivot after : DottedItem tokens) (edge : PackedEdge file tokens)
    (computed : scannedEdge? owned pivot = some (after, edge))
    (selected : processRawItem? owned pivot current = some result) :
    after ∈ result.payload.rawItems := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completedEq⟩
  exact (attemptCompletionsWith?_itemGrowth pivot scanned.payload.rawItems
    scanned result completedEq).1
      (attemptScan?_materializes owned predicted scanned pivot after edge
        computed scannedEq)

private theorem processRawItem?_completion_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (pivot other : DottedItem tokens)
    (otherMember : other ∈ current.payload.rawItems)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : processRawItem? owned pivot current = some result) :
    (∀ after (edge : PackedEdge file tokens),
      completedEdge? pivot other = some (after, edge) →
        after ∈ result.payload.rawItems) ∧
    (∀ after (edge : PackedEdge file tokens),
      completedEdge? other pivot = some (after, edge) →
        after ∈ result.payload.rawItems) := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completedEq⟩
  have predictedGrowth := attemptPredictions?_itemGrowth pivot
    allProductionIds current predicted predictedEq
  have predictedLedger := attemptPredictions?_completionLedger pivot
    allProductionIds current predicted ledger predictedEq
  have scannedGrowth := attemptScan?_itemGrowth owned predicted scanned
    pivot scannedEq
  have scannedLedger := attemptScan?_completionLedger owned predicted scanned
    pivot predictedLedger scannedEq
  exact attemptCompletionsWith?_materializes pivot scanned.payload.rawItems
    scanned result scannedLedger completedEq other
      (scannedGrowth.1 (predictedGrowth.1 otherMember))

private def PhaseAFairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  (∀ item, item ∈ rawSeedItems tokens →
      item ∈ current.payload.rawItems) ∧
  (∀ waiting, waiting ∈ current.payload.rawItems →
    ∀ production after,
      predictedItem? waiting production = some after →
      waiting ∈ current.payload.itemQueue ∨
        after ∈ current.payload.rawItems) ∧
  (∀ before, before ∈ current.payload.rawItems →
    ∀ after (edge : PackedEdge file tokens),
      scannedEdge? owned before = some (after, edge) →
      before ∈ current.payload.itemQueue ∨
        after ∈ current.payload.rawItems) ∧
  ∀ waiting, waiting ∈ current.payload.rawItems →
    ∀ finished, finished ∈ current.payload.rawItems →
    ∀ after (edge : PackedEdge file tokens),
      completedEdge? waiting finished = some (after, edge) →
      waiting ∈ current.payload.itemQueue ∨
      finished ∈ current.payload.itemQueue ∨
      after ∈ current.payload.rawItems

private def RawItemsQueued
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  current.payload.rawItems ⊆ current.payload.itemQueue

private theorem insertRawItem?_rawItemsQueued
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (invariant : RawItemsQueued current)
    (selected : insertRawItem? current source item = some result) :
    RawItemsQueued result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact invariant
  next absent =>
    have payload := phaseA_runMappedPrimitive?_payload current _ _ result
      selected
    unfold RawItemsQueued
    rw [payload]
    intro candidate member
    simp only [List.mem_append, List.mem_singleton] at member ⊢
    exact member.elim (fun old => Or.inl (invariant old)) Or.inr

private theorem insertRawSeeds?_rawItemsQueued
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      RawItemsQueued current →
      insertRawSeeds? seeds current = some result →
      RawItemsQueued result := by
  intro seeds
  induction seeds with
  | nil =>
      intro current result invariant selected
      cases selected
      exact invariant
  | cons item rest induction =>
      intro current result invariant selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (insertRawItem?_rawItemsQueued current next .seedOrPrediction
          item invariant nextEq) restEq

private theorem insertRawSeeds?_itemGrowth
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      insertRawSeeds? seeds current = some result →
      PhaseAItemGrowth current result := by
  intro seeds
  induction seeds with
  | nil =>
      intro current result selected
      cases selected
      exact .refl current
  | cons item rest induction =>
      intro current result selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact (insertRawItem?_itemGrowth current next .seedOrPrediction item
        nextEq).trans (induction next result restEq)

private theorem insertRawSeeds?_materializes
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current result : CountedState tokens (PhaseAOpen file tokens)),
      insertRawSeeds? seeds current = some result →
      ∀ item, item ∈ seeds → item ∈ result.payload.rawItems := by
  intro seeds
  induction seeds with
  | nil => simp
  | cons head rest induction =>
      intro current result selected item member
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact (insertRawSeeds?_itemGrowth rest next result restEq).1
          (insertRawItem?_coverage current next .seedOrPrediction item
            nextEq).2.2
      · exact induction next result restEq item member

private theorem insertRawSeeds?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : insertRawSeeds? (rawSeedItems tokens)
      (beginPhaseA file tokens) = some result) :
    PhaseAFairPending owned result := by
  have queued : RawItemsQueued result :=
    insertRawSeeds?_rawItemsQueued (rawSeedItems tokens)
      (beginPhaseA file tokens) result (by simp [RawItemsQueued, beginPhaseA])
      selected
  refine ⟨insertRawSeeds?_materializes (rawSeedItems tokens)
    (beginPhaseA file tokens) result selected, ?_, ?_, ?_⟩
  · intro waiting member production after computed
    exact Or.inl (queued member)
  · intro before member after edge computed
    exact Or.inl (queued member)
  · intro waiting waitingMember finished finishedMember after edge computed
    exact Or.inl (queued waitingMember)

private theorem dequeueRawItem?_raw_queue
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (head pivot : DottedItem tokens) (rest : List (DottedItem tokens))
    (queue : current.payload.itemQueue = head :: rest)
    (selected : dequeueRawItem? current = some (pivot, after)) :
    pivot = head ∧ after.payload.rawItems = current.payload.rawItems ∧
      after.payload.itemQueue = rest := by
  unfold dequeueRawItem? at selected
  simp only [queue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at output
  rcases output with ⟨headEq, nextEqual⟩
  subst pivot
  subst next
  rw [phaseA_runMappedPrimitive?_payload current _ _ after nextEq]
  exact ⟨rfl, rfl, rfl⟩

private theorem processRawItem?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before current result : CountedState tokens (PhaseAOpen file tokens))
    (pivot : DottedItem tokens) (rest : List (DottedItem tokens))
    (fair : PhaseAFairPending owned before)
    (beforeQueue : before.payload.itemQueue = pivot :: rest)
    (currentRaw : current.payload.rawItems = before.payload.rawItems)
    (currentQueue : current.payload.itemQueue = rest)
    (ledger : CompletionAttemptLedgerMaterialized current)
    (selected : processRawItem? owned pivot current = some result) :
    PhaseAFairPending owned result := by
  have growth := processRawItem?_itemGrowth owned pivot current result selected
  have carryRaw : ∀ {item}, item ∈ before.payload.rawItems →
      item ∈ result.payload.rawItems := by
    intro item member
    exact growth.1 (currentRaw.symm ▸ member)
  have carryQueue : ∀ {item}, item ≠ pivot →
      item ∈ before.payload.itemQueue →
      item ∈ result.payload.itemQueue := by
    intro item different member
    rw [beforeQueue, List.mem_cons] at member
    rcases member with equal | member
    · exact (different equal).elim
    · exact growth.2.1 (currentQueue.symm ▸ member)
  refine ⟨fun item member => carryRaw (fair.1 item member), ?_, ?_, ?_⟩
  · intro waiting waitingMember production after computed
    rcases growth.2.2 waiting waitingMember with old | queued
    · by_cases same : waiting = pivot
      · subst waiting
        exact Or.inr (processRawItem?_prediction_materializes owned
          current result pivot after production computed selected)
      · rcases fair.2.1 waiting (currentRaw ▸ old)
          production after computed with waitingQueued | materialized
        · exact Or.inl (carryQueue same waitingQueued)
        · exact Or.inr (carryRaw materialized)
    · exact Or.inl queued
  · intro waiting waitingMember after edge computed
    rcases growth.2.2 waiting waitingMember with old | queued
    · by_cases same : waiting = pivot
      · subst waiting
        exact Or.inr (processRawItem?_scan_materializes owned
          current result pivot after edge computed selected)
      · rcases fair.2.2.1 waiting (currentRaw ▸ old)
          after edge computed with waitingQueued | materialized
        · exact Or.inl (carryQueue same waitingQueued)
        · exact Or.inr (carryRaw materialized)
    · exact Or.inl queued
  · intro waiting waitingMember finished finishedMember after edge computed
    rcases growth.2.2 waiting waitingMember with waitingOld | waitingQueued
    · rcases growth.2.2 finished finishedMember with
        finishedOld | finishedQueued
      · by_cases waitingSame : waiting = pivot
        · subst waiting
          exact Or.inr (Or.inr
            ((processRawItem?_completion_materializes owned current result
              pivot finished finishedOld ledger selected).1
                after edge computed))
        · by_cases finishedSame : finished = pivot
          · subst finished
            exact Or.inr (Or.inr
              ((processRawItem?_completion_materializes owned current result
                pivot waiting waitingOld ledger selected).2
                  after edge computed))
          · rcases fair.2.2.2 waiting (currentRaw ▸ waitingOld)
                finished (currentRaw ▸ finishedOld) after edge computed with
              waitingQueued | finishedQueued | materialized
            · exact Or.inl (carryQueue waitingSame waitingQueued)
            · exact Or.inr (Or.inl
                (carryQueue finishedSame finishedQueued))
            · exact Or.inr (Or.inr (carryRaw materialized))
      · exact Or.inr (Or.inl finishedQueued)
    · exact Or.inl waitingQueued

private theorem dequeueRawEdge?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (fair : PhaseAFairPending owned current)
    (selected : dequeueRawEdge? current = some result) :
    PhaseAFairPending owned result.2 := by
  unfold dequeueRawEdge? at selected
  cases queue : current.payload.edgeQueue with
  | nil => simp [queue] at selected
  | cons edge rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, output⟩
      cases output
      change PhaseAFairPending owned next
      have payload := phaseA_runMappedPrimitive?_payload current _ _ next nextEq
      unfold PhaseAFairPending at fair ⊢
      rw [payload]
      exact fair

private theorem runPhaseAQueues?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result : CountedState tokens (PhaseAOpen file tokens)),
      CompletionAttemptLedgerMaterialized current →
      PhaseAFairPending owned current →
      runPhaseAQueues? owned fuel current = some result →
      PhaseAFairPending owned result := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result ledger fair selected
      rw [runPhaseAQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact fair
  | succ fuel induction =>
      intro current result ledger fair selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact fair
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueRawEdge?_completionLedger current pair ledger
                      dequeued)
                    (dequeueRawEdge?_fairPending owned current pair fair
                      dequeued) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processed : processRawItem? owned pivot afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  have afterLedger := dequeueRawItem?_completionLedger current
                    (pivot, afterDequeue) ledger dequeued
                  have contents := dequeueRawItem?_raw_queue current
                    afterDequeue item pivot rest items dequeued
                  have pivotEq := contents.1
                  subst item
                  exact induction next result
                    (processRawItem?_completionLedger owned pivot
                      afterDequeue next afterLedger processed)
                    (processRawItem?_fairPending owned current afterDequeue
                      next pivot rest fair items contents.2.1 contents.2.2
                      afterLedger processed) selected

private theorem executePhaseA?_fairPending
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    PhaseAFairPending owned result := by
  unfold executePhaseA? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨seeded, seededEq, runEq⟩
  have seededLedger := insertRawSeeds?_completionLedger
    (rawSeedItems tokens) (beginPhaseA file tokens) seeded
    (beginPhaseA_completionLedger file tokens) seededEq
  exact runPhaseAQueues?_fairPending owned _ seeded result seededLedger
    (insertRawSeeds?_fairPending owned seeded seededEq) runEq

private theorem executePhaseA?_executableRawClosed
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    ExecutableRawClosed owned result.payload.rawItems := by
  have fair := executePhaseA?_fairPending file tokens owned result selected
  unfold executePhaseA? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨seeded, seededEq, runEq⟩
  have empty := runPhaseAQueues?_queues_empty owned _ seeded result runEq
  refine ⟨fair.1, ?_, ?_, ?_⟩
  · intro waiting waitingMember production after computed
    rcases fair.2.1 waiting waitingMember production after computed with
      queued | materialized
    · simp [empty.1] at queued
    · exact materialized
  · intro before beforeMember after edge computed
    rcases fair.2.2.1 before beforeMember after edge computed with
      queued | materialized
    · simp [empty.1] at queued
    · exact materialized
  · intro waiting waitingMember finished finishedMember after edge computed
    rcases fair.2.2.2 waiting waitingMember finished finishedMember
        after edge computed with queued | queued | materialized
    · simp [empty.1] at queued
    · simp [empty.1] at queued
    · exact materialized

private theorem executePhaseA?_membership_eq
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    ∀ item, item ∈ result.payload.rawItems ↔
      item ∈ rawSaturation tokens := by
  exact executePhaseA?_membership_eq_of_closed file tokens owned result selected
    (executePhaseA?_executableRawClosed file tokens owned result selected)








end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem rawLinearKey_injective {tokens : List Token} :
    Function.Injective (rawLinearKey (tokens := tokens)) := by
  intro left right equal
  exact dottedItem_eq_of_fields
    (congrArg (fun key => key.dotted.production) equal)
    (congrArg (fun key => key.dotted.dot.val) equal)
    (congrArg (fun key => key.origin) equal)
    (congrArg (fun key => key.current) equal)

private structure PhaseAItemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop where
  inserted : ∀ (source : RawItemInsertSource) (item : DottedItem tokens),
    (.linear source.unitKind (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev → item ∈ current.payload.rawItems
  dequeued : ∀ item,
    (.linear .L01_itemDequeue (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev → item ∈ current.payload.rawItems
  predicted : ∀ item production,
    (.prediction .R01_predictionAttempt
      (rawPredictionKey item production) : UnitAddress tokens) ∈
        current.counter.usedRev →
    (.linear .L01_itemDequeue (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev
  scanned : ∀ item,
    (.linear .L04_scanAttempt (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev →
    (.linear .L01_itemDequeue (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev
  scannedEdge : ∀ item,
    (.linear .L06_scannedEdgeInsert (rawLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev →
    (.linear .L01_itemDequeue (rawLinearKey item) : UnitAddress tokens) ∈
      current.counter.usedRev
  queueFresh : ∀ item, item ∈ current.payload.itemQueue →
    (.linear .L01_itemDequeue (rawLinearKey item) : UnitAddress tokens) ∉
      current.counter.usedRev
  rawNodup : current.payload.rawItems.Nodup
  queueNodup : current.payload.itemQueue.Nodup
  queueSubset : current.payload.itemQueue ⊆ current.payload.rawItems

private theorem beginPhaseA_itemSafe
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAItemSafe (beginPhaseA file tokens) := by
  constructor <;> simp [beginPhaseA, Counter.charge, Counter.empty]

private theorem insertRawItem?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (safe : PhaseAItemSafe current)
    (selected : insertRawItem? current source item = some result) :
    PhaseAItemSafe result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    have payload := phaseA_runMappedPrimitive?_payload current _ _ result
      selected
    have used := phaseA_runMappedPrimitive?_usedRev current _ _ result selected
    have itemAbsent : item ∉ current.payload.rawItems := by
      intro member
      exact absent
        ((rawMemberBool_true_iff current.payload.rawItems item).mpr member)
    constructor
    · intro candidateSource candidate member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp only [UnitAddress.linear.injEq] at equal
        have keys : rawLinearKey candidate = rawLinearKey item := equal.2
        rw [rawLinearKey_injective keys, payload]
        simp
      · rw [payload]
        exact List.mem_append_left _ (safe.inserted candidateSource candidate old)
    · intro candidate member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [RawItemInsertSource.unitKind] at equal
      · rw [payload]
        exact List.mem_append_left _ (safe.dequeued candidate old)
    · intro candidate production member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [RawItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.predicted candidate production old)
    · intro candidate member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [RawItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scanned candidate old)
    · intro candidate member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [RawItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scannedEdge candidate old)
    · intro candidate member usedCandidate
      rw [payload] at member
      simp only [List.mem_append, List.mem_singleton] at member
      rw [used] at usedCandidate
      simp only [List.mem_cons] at usedCandidate
      rcases member with oldMember | equal
      · rcases usedCandidate with collision | oldUsed
        · cases source <;>
            simp [RawItemInsertSource.unitKind] at collision
        · exact safe.queueFresh candidate oldMember oldUsed
      · subst candidate
        rcases usedCandidate with collision | oldUsed
        · cases source <;>
            simp [RawItemInsertSource.unitKind] at collision
        · exact itemAbsent (safe.dequeued item oldUsed)
    · rw [payload]
      rw [List.nodup_append]
      refine ⟨safe.rawNodup, by simp, ?_⟩
      intro candidate member singleton singletonMember equal
      have singletonEq : singleton = item :=
        List.eq_of_mem_singleton singletonMember
      apply itemAbsent
      rw [← singletonEq, ← equal]
      exact member
    · rw [payload]
      have notQueued : item ∉ current.payload.itemQueue :=
        fun member => itemAbsent (safe.queueSubset member)
      rw [List.nodup_append]
      refine ⟨safe.queueNodup, by simp, ?_⟩
      intro candidate member singleton singletonMember equal
      have singletonEq : singleton = item :=
        List.eq_of_mem_singleton singletonMember
      apply notQueued
      rw [← singletonEq, ← equal]
      exact member
    · intro candidate member
      rw [payload] at member ⊢
      simp only [List.mem_append, List.mem_singleton] at member ⊢
      exact member.elim (fun old => Or.inl (safe.queueSubset old)) Or.inr

private theorem insertRawItem?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (safe : PhaseAItemSafe current) :
    ∃ result, insertRawItem? current source item = some result := by
  unfold insertRawItem?
  split
  next present => exact ⟨current, rfl⟩
  next absent =>
    have fresh : (.linear source.unitKind (rawLinearKey item) :
        UnitAddress tokens) ∉ current.counter.usedRev := by
      intro used
      exact absent ((rawMemberBool_true_iff current.payload.rawItems item).mpr
        (safe.inserted source item used))
    simp [runMappedPrimitive?, fresh]


private theorem dequeueRawItem?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (safe : PhaseAItemSafe current)
    (selected : dequeueRawItem? current = some result) :
    PhaseAItemSafe result.2 := by
  unfold dequeueRawItem? at selected
  cases queue : current.payload.itemQueue with
  | nil => simp [queue] at selected
  | cons head rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, output⟩
      cases output
      have payload := phaseA_runMappedPrimitive?_payload current _ _ next nextEq
      have used := phaseA_runMappedPrimitive?_usedRev current _ _ next nextEq
      have unique : head ∉ rest ∧ rest.Nodup := by
        have queueNodup := safe.queueNodup
        rw [queue, List.nodup_cons] at queueNodup
        exact queueNodup
      constructor
      · intro source item member
        rw [used] at member
        simp only [List.mem_cons] at member
        rcases member with equal | old
        · cases source <;> simp [RawItemInsertSource.unitKind] at equal
        · rw [payload]
          exact safe.inserted source item old
      · intro item member
        rw [used] at member
        simp only [List.mem_cons] at member
        rcases member with equal | old
        · simp only [UnitAddress.linear.injEq] at equal
          rw [rawLinearKey_injective equal.2, payload]
          exact safe.queueSubset (by simp [queue])
        · rw [payload]
          exact safe.dequeued item old
      · intro item production member
        rw [used] at member
        simp only [List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.predicted item production old)
      · intro item member
        rw [used] at member
        simp only [List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.scanned item old)
      · intro item member
        rw [used] at member
        simp only [List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
      · intro item member usedItem
        rw [payload] at member
        rw [used] at usedItem
        simp only [List.mem_cons] at usedItem
        rcases usedItem with collision | old
        · simp only [UnitAddress.linear.injEq] at collision
          have same := rawLinearKey_injective collision.2
          exact unique.1 (same ▸ member)
        · exact safe.queueFresh item (by simp [queue, member]) old
      · simpa [payload] using safe.rawNodup
      · simpa [payload] using unique.2
      · intro item member
        rw [payload] at member ⊢
        exact safe.queueSubset (by simp [queue, member])

private structure PhaseAItemWorkFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) : Prop where
  dequeued : (.linear .L01_itemDequeue (rawLinearKey item) :
    UnitAddress tokens) ∈ current.counter.usedRev
  predictions : ∀ production,
    (.prediction .R01_predictionAttempt
      (rawPredictionKey item production) : UnitAddress tokens) ∉
        current.counter.usedRev
  scan : (.linear .L04_scanAttempt (rawLinearKey item) :
    UnitAddress tokens) ∉ current.counter.usedRev
  scannedEdge : (.linear .L06_scannedEdgeInsert (rawLinearKey item) :
    UnitAddress tokens) ∉ current.counter.usedRev

private theorem dequeueRawItem?_workFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) (rest : List (DottedItem tokens))
    (queue : current.payload.itemQueue = item :: rest)
    (safe : PhaseAItemSafe current)
    (selected : dequeueRawItem? current = some (item, after)) :
    PhaseAItemWorkFresh after item := by
  unfold dequeueRawItem? at selected
  simp only [queue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  have used := phaseA_runMappedPrimitive?_usedRev current _ _ after nextEq
  have dequeueFresh := safe.queueFresh item (by simp [queue])
  constructor
  · rw [used]
    simp
  · intro production member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.predicted item production old)
  · intro member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.scanned item old)
  · intro member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.scannedEdge item old)

private theorem dequeueRawItem?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) (rest : List (DottedItem tokens))
    (queue : current.payload.itemQueue = item :: rest)
    (safe : PhaseAItemSafe current) :
    ∃ after, dequeueRawItem? current = some (item, after) := by
  have fresh := safe.queueFresh item (by simp [queue])
  unfold dequeueRawItem?
  rw [queue]
  simp [runMappedPrimitive?, fresh]

private theorem rawPredictionKey_waiting_eq
    {tokens : List Token} {leftWaiting rightWaiting : DottedItem tokens}
    {leftProduction rightProduction : ProductionId}
    (equal : rawPredictionKey leftWaiting leftProduction =
      rawPredictionKey rightWaiting rightProduction) :
    leftWaiting = rightWaiting :=
  dottedItem_eq_of_fields
    (congrArg (fun key => key.dotted.production) equal)
    (congrArg (fun key => key.dotted.dot.val) equal)
    (congrArg (fun key => key.origin) equal)
    (congrArg (fun key => key.current) equal)

private theorem chargePrediction_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (safe : PhaseAItemSafe current)
    (dequeued : (.linear .L01_itemDequeue (rawLinearKey waiting) :
      UnitAddress tokens) ∈ current.counter.usedRev)
    (selected : runMappedPrimitive? current
      (.prediction .R01_predictionAttempt
        (rawPredictionKey waiting production)) id = some result) :
    PhaseAItemSafe result := by
  have payload := phaseA_runMappedPrimitive?_payload current _ id result selected
  have used := phaseA_runMappedPrimitive?_usedRev current _ id result selected
  constructor
  · intro source item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · simpa [payload] using safe.inserted source item old
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · simpa [payload] using safe.dequeued item old
  · intro item predicted member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp only [UnitAddress.prediction.injEq] at equal
      have waitingEq := rawPredictionKey_waiting_eq equal.2
      rw [waitingEq, used]
      exact List.mem_cons_of_mem _ dequeued
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.predicted item predicted old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scanned item old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
  · intro item member usedItem
    rw [payload] at member
    rw [used] at usedItem
    simp only [List.mem_cons] at usedItem
    rcases usedItem with equal | old
    · simp at equal
    · exact safe.queueFresh item member old
  · simpa [payload] using safe.rawNodup
  · simpa [payload] using safe.queueNodup
  · simpa [payload] using safe.queueSubset


private theorem insertRawItem?_preserves_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (target : UnitAddress tokens)
    (notInsert : ∀ (candidateSource : RawItemInsertSource)
      (candidate : DottedItem tokens),
      target ≠ (.linear candidateSource.unitKind (rawLinearKey candidate) :
        UnitAddress tokens))
    (fresh : target ∉ current.counter.usedRev)
    (selected : insertRawItem? current source item = some result) :
    target ∉ result.counter.usedRev := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact fresh
  next absent =>
    rw [phaseA_runMappedPrimitive?_usedRev current _ _ result selected]
    simp only [List.mem_cons, not_or]
    exact ⟨notInsert source item, fresh⟩

private theorem attemptPrediction?_total_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (safe : PhaseAItemSafe current)
    (dequeued : (.linear .L01_itemDequeue (rawLinearKey waiting) :
      UnitAddress tokens) ∈ current.counter.usedRev)
    (fresh : (.prediction .R01_predictionAttempt
      (rawPredictionKey waiting production) : UnitAddress tokens) ∉
        current.counter.usedRev) :
    ∃ result, attemptPrediction? current waiting production = some result ∧
      PhaseAItemSafe result := by
  unfold attemptPrediction?
  cases prediction : predictedItem? waiting production with
  | none => exact ⟨current, rfl, safe⟩
  | some item =>
      let attempted : CountedState tokens (PhaseAOpen file tokens) := {
        payload := current.payload
        counter := current.counter.charge _ fresh
      }
      have attemptedEq : runMappedPrimitive? current
          (.prediction .R01_predictionAttempt
            (rawPredictionKey waiting production)) id = some attempted := by
        simp [runMappedPrimitive?, fresh, attempted]
      have attemptedSafe := chargePrediction_itemSafe current attempted
        waiting production safe dequeued attemptedEq
      obtain ⟨result, insertedEq⟩ := insertRawItem?_total attempted
        .seedOrPrediction item attemptedSafe
      exact ⟨result, by simp [attemptedEq, insertedEq],
        insertRawItem?_itemSafe attempted result .seedOrPrediction item
          attemptedSafe insertedEq⟩

private theorem insertRawItem?_used_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (selected : insertRawItem? current source item = some result) :
    current.counter.usedRev ⊆ result.counter.usedRev := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact fun _ => id
  next absent =>
    rw [phaseA_runMappedPrimitive?_usedRev current _ _ result selected]
    exact fun address member => List.mem_cons_of_mem _ member

private theorem attemptPrediction?_used_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (selected : attemptPrediction? current waiting production = some result) :
    current.counter.usedRev ⊆ result.counter.usedRev := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting production with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact fun _ => id
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      intro address member
      apply insertRawItem?_used_mono attempted result .seedOrPrediction item
        insertedEq
      rw [phaseA_runMappedPrimitive?_usedRev current _ id attempted attemptedEq]
      exact List.mem_cons_of_mem _ member

private theorem attemptPrediction?_preserves_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (target : UnitAddress tokens)
    (notPrediction : target ≠
      (.prediction .R01_predictionAttempt
        (rawPredictionKey waiting production) : UnitAddress tokens))
    (notInsert : ∀ (source : RawItemInsertSource)
      (item : DottedItem tokens),
      target ≠ (.linear source.unitKind (rawLinearKey item) :
        UnitAddress tokens))
    (fresh : target ∉ current.counter.usedRev)
    (selected : attemptPrediction? current waiting production = some result) :
    target ∉ result.counter.usedRev := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting production with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact fresh
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, insertedEq⟩
      apply insertRawItem?_preserves_fresh attempted result
        .seedOrPrediction item target notInsert _ insertedEq
      rw [phaseA_runMappedPrimitive?_usedRev current _ id attempted attemptedEq]
      simp only [List.mem_cons, not_or]
      exact ⟨notPrediction, fresh⟩

private theorem attemptPredictions?_total_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current : CountedState tokens (PhaseAOpen file tokens)),
      productions.Nodup →
      PhaseAItemSafe current →
      (.linear .L01_itemDequeue (rawLinearKey waiting) :
        UnitAddress tokens) ∈ current.counter.usedRev →
      (∀ production, production ∈ productions →
        (.prediction .R01_predictionAttempt
          (rawPredictionKey waiting production) : UnitAddress tokens) ∉
            current.counter.usedRev) →
      (.linear .L04_scanAttempt (rawLinearKey waiting) :
        UnitAddress tokens) ∉ current.counter.usedRev →
      (.linear .L06_scannedEdgeInsert (rawLinearKey waiting) :
        UnitAddress tokens) ∉ current.counter.usedRev →
      ∃ result, attemptPredictions? waiting productions current = some result ∧
        PhaseAItemSafe result ∧
        (.linear .L01_itemDequeue (rawLinearKey waiting) :
          UnitAddress tokens) ∈ result.counter.usedRev ∧
        (.linear .L04_scanAttempt (rawLinearKey waiting) :
          UnitAddress tokens) ∉ result.counter.usedRev ∧
        (.linear .L06_scannedEdgeInsert (rawLinearKey waiting) :
          UnitAddress tokens) ∉ result.counter.usedRev := by
  intro productions
  induction productions with
  | nil =>
      intro current unique safe dequeued predictions scanFresh edgeFresh
      exact ⟨current, rfl, safe, dequeued, scanFresh, edgeFresh⟩
  | cons head rest induction =>
      intro current unique safe dequeued predictions scanFresh edgeFresh
      rw [List.nodup_cons] at unique
      obtain ⟨next, nextEq, nextSafe⟩ :=
        attemptPrediction?_total_itemSafe current waiting head safe dequeued
          (predictions head (by simp))
      have nextDequeued := attemptPrediction?_used_mono current next
        waiting head nextEq dequeued
      have restFresh : ∀ production, production ∈ rest →
          (.prediction .R01_predictionAttempt
            (rawPredictionKey waiting production) : UnitAddress tokens) ∉
              next.counter.usedRev := by
        intro production member
        apply attemptPrediction?_preserves_fresh current next waiting head _
          _ (by simp) (predictions production (by simp [member])) nextEq
        intro equal
        simp only [UnitAddress.prediction.injEq] at equal
        have productionEq := congrArg ChartPredictionKey.production equal.2
        change production = head at productionEq
        exact unique.1 (productionEq ▸ member)
      have nextScanFresh := attemptPrediction?_preserves_fresh current next
        waiting head _ (by simp) (by
          intro source item
          cases source <;> simp [RawItemInsertSource.unitKind]) scanFresh nextEq
      have nextEdgeFresh := attemptPrediction?_preserves_fresh current next
        waiting head _ (by simp) (by
          intro source item
          cases source <;> simp [RawItemInsertSource.unitKind]) edgeFresh nextEq
      obtain ⟨result, restEq, resultSafe, resultDequeued,
        resultScanFresh, resultEdgeFresh⟩ := induction next unique.2 nextSafe
          nextDequeued restFresh nextScanFresh nextEdgeFresh
      exact ⟨result, by simp [attemptPredictions?, nextEq, restEq],
        resultSafe, resultDequeued, resultScanFresh, resultEdgeFresh⟩


private theorem chargeScan_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens) (safe : PhaseAItemSafe current)
    (dequeued : (.linear .L01_itemDequeue (rawLinearKey before) :
      UnitAddress tokens) ∈ current.counter.usedRev)
    (selected : runMappedPrimitive? current
      (.linear .L04_scanAttempt (rawLinearKey before)) id = some result) :
    PhaseAItemSafe result := by
  have payload := phaseA_runMappedPrimitive?_payload current _ id result selected
  have used := phaseA_runMappedPrimitive?_usedRev current _ id result selected
  constructor
  · intro source item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · cases source <;> simp [RawItemInsertSource.unitKind] at equal
    · simpa [payload] using safe.inserted source item old
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · simpa [payload] using safe.dequeued item old
  · intro item production member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.predicted item production old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp only [UnitAddress.linear.injEq] at equal
      rw [rawLinearKey_injective equal.2, used]
      exact List.mem_cons_of_mem _ dequeued
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scanned item old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
  · intro item member usedItem
    rw [payload] at member
    rw [used] at usedItem
    simp only [List.mem_cons] at usedItem
    rcases usedItem with equal | old
    · simp at equal
    · exact safe.queueFresh item member old
  · simpa [payload] using safe.rawNodup
  · simpa [payload] using safe.queueNodup
  · simpa [payload] using safe.queueSubset

private theorem insertScannedRawEdge?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before after : DottedItem tokens) (cursor : TerminalCursor tokens)
    (edge : PackedEdge file tokens)
    (shape : edge.val = .scanned before after cursor)
    (safe : PhaseAItemSafe current)
    (dequeued : (.linear .L01_itemDequeue (rawLinearKey before) :
      UnitAddress tokens) ∈ current.counter.usedRev)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAItemSafe result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    simp only [shape] at selected
    have payload := phaseA_runMappedPrimitive?_payload current _ _ result
      selected
    have used := phaseA_runMappedPrimitive?_usedRev current _ _ result selected
    constructor
    · intro source item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;> simp [RawItemInsertSource.unitKind] at equal
      · simpa [payload] using safe.inserted source item old
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · simpa [payload] using safe.dequeued item old
    · intro item production member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.predicted item production old)
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scanned item old)
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp only [UnitAddress.linear.injEq] at equal
        rw [rawLinearKey_injective equal.2, used]
        exact List.mem_cons_of_mem _ dequeued
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
    · intro item member usedItem
      rw [payload] at member
      rw [used] at usedItem
      simp only [List.mem_cons] at usedItem
      rcases usedItem with equal | old
      · simp at equal
      · exact safe.queueFresh item member old
    · simpa [payload] using safe.rawNodup
    · simpa [payload] using safe.queueNodup
    · simpa [payload] using safe.queueSubset

private theorem insertScannedRawEdge?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (before after : DottedItem tokens) (cursor : TerminalCursor tokens)
    (edge : PackedEdge file tokens)
    (shape : edge.val = .scanned before after cursor)
    (fresh : (.linear .L06_scannedEdgeInsert (rawLinearKey before) :
      UnitAddress tokens) ∉ current.counter.usedRev) :
    ∃ result, insertRawEdge? current edge = some result := by
  unfold insertRawEdge?
  split
  next present => exact ⟨current, rfl⟩
  next absent =>
    simp only [shape]
    simp [runMappedPrimitive?, fresh]

private theorem attemptScan?_total_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens) (safe : PhaseAItemSafe current)
    (dequeued : (.linear .L01_itemDequeue (rawLinearKey before) :
      UnitAddress tokens) ∈ current.counter.usedRev)
    (scanFresh : (.linear .L04_scanAttempt (rawLinearKey before) :
      UnitAddress tokens) ∉ current.counter.usedRev)
    (edgeFresh : (.linear .L06_scannedEdgeInsert (rawLinearKey before) :
      UnitAddress tokens) ∉ current.counter.usedRev) :
    ∃ result, attemptScan? owned current before = some result ∧
      PhaseAItemSafe result := by
  unfold attemptScan?
  split
  next applicable =>
    let attempted : CountedState tokens (PhaseAOpen file tokens) := {
      payload := current.payload
      counter := current.counter.charge _ scanFresh
    }
    have attemptedEq : runMappedPrimitive? current
        (.linear .L04_scanAttempt (rawLinearKey before)) id = some attempted := by
      simp [runMappedPrimitive?, scanFresh, attempted]
    have attemptedSafe := chargeScan_itemSafe current attempted before safe
      dequeued attemptedEq
    have attemptedDequeued : (.linear .L01_itemDequeue
        (rawLinearKey before) : UnitAddress tokens) ∈
        attempted.counter.usedRev := by
      rw [phaseA_runMappedPrimitive?_usedRev current _ id attempted attemptedEq]
      exact List.mem_cons_of_mem _ dequeued
    have attemptedEdgeFresh : (.linear .L06_scannedEdgeInsert
        (rawLinearKey before) : UnitAddress tokens) ∉
        attempted.counter.usedRev := by
      rw [phaseA_runMappedPrimitive?_usedRev current _ id attempted attemptedEq]
      simp [edgeFresh]
    cases scan : scannedEdge? owned before with
    | none => exact ⟨attempted, by simp [attemptedEq], attemptedSafe⟩
    | some pair =>
        rcases pair with ⟨after, edge⟩
        obtain ⟨withItem, itemEq⟩ := insertRawItem?_total attempted .scan after
          attemptedSafe
        have withItemSafe := insertRawItem?_itemSafe attempted withItem .scan
          after attemptedSafe itemEq
        have withItemDequeued := insertRawItem?_used_mono attempted withItem
          .scan after itemEq attemptedDequeued
        have withItemEdgeFresh := insertRawItem?_preserves_fresh attempted
          withItem .scan after _ (by
            intro source item
            cases source <;> simp [RawItemInsertSource.unitKind])
          attemptedEdgeFresh itemEq
        obtain ⟨cursor, shape⟩ := scannedEdge?_shape owned before after edge scan
        obtain ⟨result, edgeEq⟩ := insertScannedRawEdge?_total withItem
          before after cursor edge shape withItemEdgeFresh
        exact ⟨result, by simp [attemptedEq, itemEq, edgeEq],
          insertScannedRawEdge?_itemSafe withItem result before after cursor edge
            shape withItemSafe withItemDequeued edgeEq⟩
  next notApplicable => exact ⟨current, rfl, safe⟩


private def PhaseACompletionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop :=
  ∀ waiting finished,
    (.cubic .U04_completedEdgeInsert
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev →
    (.cubic .U03_completionAttempt
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev

private theorem beginPhaseA_completionSafe
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseACompletionSafe (beginPhaseA file tokens) := by
  intro waiting finished member
  simp [beginPhaseA, Counter.charge, Counter.empty] at member

private theorem runMappedPrimitive?_completionSafe_of_not_insert
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (address : UnitAddress tokens)
    (transition : PhaseAOpen file tokens → PhaseAOpen file tokens)
    (safe : PhaseACompletionSafe current)
    (notInsert : ∀ waiting finished,
      address ≠ (.cubic .U04_completedEdgeInsert
        (rawCompletionKey waiting finished) : UnitAddress tokens))
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseACompletionSafe result := by
  intro waiting finished member
  rw [phaseA_runMappedPrimitive?_usedRev current address transition result
    selected] at member ⊢
  simp only [List.mem_cons] at member ⊢
  rcases member with equal | old
  · exact (notInsert waiting finished equal.symm).elim
  · exact Or.inr (safe waiting finished old)

private theorem insertRawItem?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (safe : PhaseACompletionSafe current)
    (selected : insertRawItem? current source item = some result) :
    PhaseACompletionSafe result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    exact runMappedPrimitive?_completionSafe_of_not_insert current result _ _
      safe (by
        intro waiting finished equal
        cases source <;> simp [RawItemInsertSource.unitKind] at equal)
      selected

private theorem chargeCompletion_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens) (safe : PhaseAItemSafe current)
    (selected : runMappedPrimitive? current
      (.cubic .U03_completionAttempt (rawCompletionKey waiting finished)) id =
        some result) :
    PhaseAItemSafe result := by
  have payload := phaseA_runMappedPrimitive?_payload current _ id result selected
  have used := phaseA_runMappedPrimitive?_usedRev current _ id result selected
  constructor
  · intro source item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · cases source <;> simp [RawItemInsertSource.unitKind] at equal
    · simpa [payload] using safe.inserted source item old
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · simpa [payload] using safe.dequeued item old
  · intro item production member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.predicted item production old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scanned item old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
  · intro item member usedItem
    rw [payload] at member
    rw [used] at usedItem
    simp only [List.mem_cons] at usedItem
    rcases usedItem with equal | old
    · simp at equal
    · exact safe.queueFresh item member old
  · simpa [payload] using safe.rawNodup
  · simpa [payload] using safe.queueNodup
  · simpa [payload] using safe.queueSubset

private theorem insertCompletedRawEdge?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) (edge : PackedEdge file tokens)
    (shape : edge.val = .completed waiting finished after shared)
    (safe : PhaseAItemSafe current)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAItemSafe result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    simp only [shape] at selected
    have payload := phaseA_runMappedPrimitive?_payload current _ _ result
      selected
    have used := phaseA_runMappedPrimitive?_usedRev current _ _ result selected
    constructor
    · intro source item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · cases source <;> simp [RawItemInsertSource.unitKind] at equal
      · simpa [payload] using safe.inserted source item old
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · simpa [payload] using safe.dequeued item old
    · intro item production member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.predicted item production old)
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scanned item old)
    · intro item member
      rw [used] at member
      simp only [List.mem_cons] at member
      rcases member with equal | old
      · simp at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
    · intro item member usedItem
      rw [payload] at member
      rw [used] at usedItem
      simp only [List.mem_cons] at usedItem
      rcases usedItem with equal | old
      · simp at equal
      · exact safe.queueFresh item member old
    · simpa [payload] using safe.rawNodup
    · simpa [payload] using safe.queueNodup
    · simpa [payload] using safe.queueSubset

private theorem insertCompletedRawEdge?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) (edge : PackedEdge file tokens)
    (shape : edge.val = .completed waiting finished after shared)
    (safe : PhaseACompletionSafe current)
    (attempted : (.cubic .U03_completionAttempt
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev)
    (selected : insertRawEdge? current edge = some result) :
    PhaseACompletionSafe result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    simp only [shape] at selected
    have used := phaseA_runMappedPrimitive?_usedRev current _ _ result selected
    intro candidateWaiting candidateFinished member
    rw [used] at member ⊢
    simp only [List.mem_cons] at member ⊢
    rcases member with equal | old
    · simp only [UnitAddress.cubic.injEq] at equal
      exact Or.inr (by simpa only [equal.2] using attempted)
    · exact Or.inr (safe candidateWaiting candidateFinished old)

private theorem insertCompletedRawEdge?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) (edge : PackedEdge file tokens)
    (shape : edge.val = .completed waiting finished after shared)
    (fresh : (.cubic .U04_completedEdgeInsert
      (rawCompletionKey waiting finished) : UnitAddress tokens) ∉
        current.counter.usedRev) :
    ∃ result, insertRawEdge? current edge = some result := by
  unfold insertRawEdge?
  split
  next present => exact ⟨current, rfl⟩
  next absent =>
    simp only [shape]
    simp [runMappedPrimitive?, fresh]


private theorem attemptCompletion?_total_safe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (itemSafe : PhaseAItemSafe current)
    (completionSafe : PhaseACompletionSafe current) :
    ∃ result, attemptCompletion? current waiting finished = some result ∧
      PhaseAItemSafe result ∧ PhaseACompletionSafe result := by
  unfold attemptCompletion?
  cases completion : completedEdge? (file := file) waiting finished with
  | none => exact ⟨current, rfl, itemSafe, completionSafe⟩
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only
      let address : UnitAddress tokens :=
        .cubic .U03_completionAttempt (rawCompletionKey waiting finished)
      split
      next used => exact ⟨current, rfl, itemSafe, completionSafe⟩
      next fresh =>
        have addressFresh : address ∉ current.counter.usedRev := by
          simpa [address] using fresh
        let attemptedState : CountedState tokens (PhaseAOpen file tokens) := {
          payload := current.payload
          counter := current.counter.charge address addressFresh
        }
        have attemptedEq : runMappedPrimitive? current address id =
            some attemptedState := by
          simp [runMappedPrimitive?, addressFresh, attemptedState]
        have attemptedItemSafe := chargeCompletion_itemSafe current
          attemptedState waiting finished itemSafe attemptedEq
        have attemptedCompletionSafe :=
          runMappedPrimitive?_completionSafe_of_not_insert current
            attemptedState address id completionSafe (by simp [address]) attemptedEq
        obtain ⟨withItem, itemEq⟩ := insertRawItem?_total attemptedState
          .completion after attemptedItemSafe
        have withItemSafe := insertRawItem?_itemSafe attemptedState withItem
          .completion after attemptedItemSafe itemEq
        have withItemCompletionSafe := insertRawItem?_completionSafe
          attemptedState withItem .completion after attemptedCompletionSafe itemEq
        have attemptedUsed : address ∈ attemptedState.counter.usedRev := by
          simp [attemptedState, Counter.charge]
        have withItemUsed := insertRawItem?_used_mono attemptedState withItem
          .completion after itemEq attemptedUsed
        have beforeEdgeFresh : (.cubic .U04_completedEdgeInsert
            (rawCompletionKey waiting finished) : UnitAddress tokens) ∉
            current.counter.usedRev := by
          intro inserted
          exact fresh (completionSafe waiting finished inserted)
        have attemptedEdgeFresh : (.cubic .U04_completedEdgeInsert
            (rawCompletionKey waiting finished) : UnitAddress tokens) ∉
            attemptedState.counter.usedRev := by
          simp [attemptedState, Counter.charge, beforeEdgeFresh, address]
        have withItemEdgeFresh := insertRawItem?_preserves_fresh attemptedState
          withItem .completion after _ (by
            intro source item
            cases source <;> simp [RawItemInsertSource.unitKind])
          attemptedEdgeFresh itemEq
        obtain ⟨shared, shape⟩ := completedEdge?_shape waiting finished after
          edge completion
        obtain ⟨result, edgeEq⟩ := insertCompletedRawEdge?_total withItem
          waiting finished after shared edge shape withItemEdgeFresh
        have attemptedEq' : runMappedPrimitive? current
            (.cubic .U03_completionAttempt
              (rawCompletionKey waiting finished)) id = some attemptedState := by
          simpa [address] using attemptedEq
        exact ⟨result, by
          rw [attemptedEq']
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [itemEq]
          exact edgeEq,
          insertCompletedRawEdge?_itemSafe withItem result waiting finished
            after shared edge shape withItemSafe edgeEq,
          insertCompletedRawEdge?_completionSafe withItem result waiting finished
            after shared edge shape withItemCompletionSafe withItemUsed edgeEq⟩

private def rawEdgeInsertAddress
    {file : WorkspaceFile} {tokens : List Token}
    (edge : PackedEdge file tokens) : UnitAddress tokens :=
  match edge.val with
  | .scanned before _ _ =>
      .linear .L06_scannedEdgeInsert (rawLinearKey before)
  | .completed waiting finished _ _ =>
      .cubic .U04_completedEdgeInsert (rawCompletionKey waiting finished)

private def rawEdgeDequeueAddress
    {file : WorkspaceFile} {tokens : List Token}
    (edge : PackedEdge file tokens) : UnitAddress tokens :=
  match edge.val with
  | .scanned before _ _ =>
      .linear .L02_scannedEdgeDequeue (rawLinearKey before)
  | .completed waiting finished _ _ =>
      .cubic .U02_completedEdgeDequeue (rawCompletionKey waiting finished)

private theorem rawEdgeInsertAddress_ne_dequeueAddress
    {file : WorkspaceFile} {tokens : List Token}
    (inserted dequeued : PackedEdge file tokens) :
    rawEdgeInsertAddress inserted ≠ rawEdgeDequeueAddress dequeued := by
  rcases inserted with ⟨inserted, insertedValid⟩
  rcases dequeued with ⟨dequeued, dequeuedValid⟩
  cases inserted <;> cases dequeued <;>
    simp [rawEdgeInsertAddress, rawEdgeDequeueAddress]

private theorem rawEdgeInsertAddress_eq_of_dequeueAddress_eq
    {file : WorkspaceFile} {tokens : List Token}
    (left right : PackedEdge file tokens)
    (equal : rawEdgeDequeueAddress left = rawEdgeDequeueAddress right) :
    rawEdgeInsertAddress left = rawEdgeInsertAddress right := by
  rcases left with ⟨left, leftValid⟩
  rcases right with ⟨right, rightValid⟩
  cases left <;> cases right <;>
    simp [rawEdgeDequeueAddress, rawEdgeInsertAddress] at equal ⊢
  all_goals exact equal

private structure PhaseAEdgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop where
  inserted : ∀ edge, edge ∈ current.payload.edgeQueue →
    rawEdgeInsertAddress edge ∈ current.counter.usedRev
  causal : ∀ (edge : PackedEdge file tokens),
    rawEdgeDequeueAddress edge ∈ current.counter.usedRev →
    rawEdgeInsertAddress edge ∈ current.counter.usedRev
  queueFresh : ∀ (edge : PackedEdge file tokens),
    edge ∈ current.payload.edgeQueue →
    rawEdgeDequeueAddress edge ∉ current.counter.usedRev
  queueAddressNodup :
    (current.payload.edgeQueue.map rawEdgeDequeueAddress).Nodup

private theorem beginPhaseA_edgeSafe
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAEdgeSafe (beginPhaseA file tokens) := by
  constructor
  · intro edge member
    simp [beginPhaseA] at member
  · intro edge member
    simp [beginPhaseA, Counter.charge, Counter.empty] at member
    rcases edge with ⟨edge, valid⟩
    cases edge <;> simp [rawEdgeDequeueAddress] at member
  · intro edge member
    simp [beginPhaseA] at member
  · simp [beginPhaseA]

private theorem runMappedPrimitive?_edgeSafe_of_queue_eq
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (address : UnitAddress tokens)
    (transition : PhaseAOpen file tokens → PhaseAOpen file tokens)
    (safe : PhaseAEdgeSafe current)
    (queueEq : ∀ state, (transition state).edgeQueue = state.edgeQueue)
    (notDequeue : ∀ (edge : PackedEdge file tokens),
      address ≠ rawEdgeDequeueAddress edge)
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseAEdgeSafe result := by
  have payload := phaseA_runMappedPrimitive?_payload current address transition
    result selected
  have used := phaseA_runMappedPrimitive?_usedRev current address transition
    result selected
  have resultQueue : result.payload.edgeQueue = current.payload.edgeQueue := by
    rw [payload]
    exact queueEq current.payload
  constructor
  · intro edge member
    rw [resultQueue] at member
    rw [used]
    exact List.mem_cons_of_mem _ (safe.inserted edge member)
  · intro edge member
    rw [used] at member ⊢
    simp only [List.mem_cons] at member ⊢
    rcases member with equal | old
    · exact (notDequeue edge equal.symm).elim
    · exact Or.inr (safe.causal edge old)
  · intro edge member usedEdge
    rw [resultQueue] at member
    rw [used] at usedEdge
    simp only [List.mem_cons] at usedEdge
    rcases usedEdge with equal | old
    · exact notDequeue edge equal.symm
    · exact safe.queueFresh edge member old
  · simpa [resultQueue] using safe.queueAddressNodup

private theorem insertRawItem?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (safe : PhaseAEdgeSafe current)
    (selected : insertRawItem? current source item = some result) :
    PhaseAEdgeSafe result := by
  unfold insertRawItem? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    apply runMappedPrimitive?_edgeSafe_of_queue_eq current result _ _ safe
      (by intro state; rfl) _ selected
    intro edge equal
    rcases edge with ⟨edge, valid⟩
    cases source <;> cases edge <;>
      simp [RawItemInsertSource.unitKind, rawEdgeDequeueAddress] at equal


private theorem insertRawEdge?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (safe : PhaseAEdgeSafe current)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAEdgeSafe result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    change runMappedPrimitive? current (rawEdgeInsertAddress edge) (fun state => {
      state with
      rawEdges := state.rawEdges ++ [edge]
      edgeQueue := state.edgeQueue ++ [edge]
    }) = some result at selected
    have payload := phaseA_runMappedPrimitive?_payload current _ _ result selected
    have used := phaseA_runMappedPrimitive?_usedRev current _ _ result selected
    have insertFresh : rawEdgeInsertAddress edge ∉
        current.counter.usedRev := by
      have selectedCopy := selected
      unfold runMappedPrimitive? at selectedCopy
      split at selectedCopy
      next fresh => exact fresh
      next usedBefore => contradiction
    have payloadQueue : result.payload.edgeQueue =
        current.payload.edgeQueue ++ [edge] := by
      simp [payload]
    constructor
    · intro candidate member
      rw [payloadQueue] at member
      rw [used]
      simp only [List.mem_append, List.mem_singleton] at member ⊢
      rcases member with old | equal
      · exact List.mem_cons_of_mem _ (safe.inserted candidate old)
      · subst candidate
        exact List.mem_cons_self
    · intro candidate member
      rw [used] at member ⊢
      simp only [List.mem_cons] at member ⊢
      rcases member with equal | old
      · exact (rawEdgeInsertAddress_ne_dequeueAddress edge candidate
          equal.symm).elim
      · exact Or.inr (safe.causal candidate old)
    · intro candidate member usedCandidate
      rw [payloadQueue] at member
      rw [used] at usedCandidate
      simp only [List.mem_append, List.mem_singleton] at member
      simp only [List.mem_cons] at usedCandidate
      rcases member with old | equal
      · rcases usedCandidate with collision | oldUsed
        · exact rawEdgeInsertAddress_ne_dequeueAddress edge candidate
            collision.symm
        · exact safe.queueFresh candidate old oldUsed
      · subst candidate
        rcases usedCandidate with collision | oldUsed
        · exact rawEdgeInsertAddress_ne_dequeueAddress edge edge
            collision.symm
        · exact insertFresh (safe.causal edge oldUsed)
    · rw [payloadQueue, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨safe.queueAddressNodup, by simp, ?_⟩
      intro address addressMember singleton singletonMember equal
      obtain ⟨candidate, candidateMember, candidateAddress⟩ :=
        List.mem_map.mp addressMember
      have singletonAddress : singleton = rawEdgeDequeueAddress edge :=
        List.eq_of_mem_singleton singletonMember
      apply insertFresh
      have dequeueEqual : rawEdgeDequeueAddress candidate =
          rawEdgeDequeueAddress edge := by
        exact candidateAddress.trans (equal.trans singletonAddress)
      rw [← rawEdgeInsertAddress_eq_of_dequeueAddress_eq candidate edge
        dequeueEqual]
      exact safe.inserted candidate candidateMember

private theorem attemptCompletion?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens) (safe : PhaseAEdgeSafe current)
    (selected : attemptCompletion? current waiting finished = some result) :
    PhaseAEdgeSafe result := by
  unfold attemptCompletion? at selected
  cases completion : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completion] at selected
      cases selected
      exact safe
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completion] at selected
      split at selected
      next used =>
        cases selected
        exact safe
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq, withItem, itemEq,
          edgeEq⟩
        have attemptedSafe := runMappedPrimitive?_edgeSafe_of_queue_eq
          current attempted _ id safe (by intro state; rfl) (by
            intro candidate
            rcases candidate with ⟨candidate, valid⟩
            cases candidate <;> simp [rawEdgeDequeueAddress]) attemptedEq
        have itemSafe := insertRawItem?_edgeSafe attempted withItem .completion
          after attemptedSafe itemEq
        exact insertRawEdge?_edgeSafe withItem result edge itemSafe edgeEq

private theorem attemptCompletion?_total_allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (itemSafe : PhaseAItemSafe current)
    (completionSafe : PhaseACompletionSafe current)
    (edgeSafe : PhaseAEdgeSafe current) :
    ∃ result, attemptCompletion? current waiting finished = some result ∧
      PhaseAItemSafe result ∧ PhaseACompletionSafe result ∧
      PhaseAEdgeSafe result := by
  obtain ⟨result, selected, resultItemSafe, resultCompletionSafe⟩ :=
    attemptCompletion?_total_safe current waiting finished itemSafe completionSafe
  exact ⟨result, selected, resultItemSafe, resultCompletionSafe,
    attemptCompletion?_edgeSafe current result waiting finished edgeSafe selected⟩

private theorem attemptCompletionsWith?_total_allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others (current : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAItemSafe current → PhaseACompletionSafe current →
      PhaseAEdgeSafe current →
      ∃ result, attemptCompletionsWith? pivot others current = some result ∧
        PhaseAItemSafe result ∧ PhaseACompletionSafe result ∧
        PhaseAEdgeSafe result := by
  intro others
  induction others with
  | nil =>
      intro current itemSafe completionSafe edgeSafe
      exact ⟨current, rfl, itemSafe, completionSafe, edgeSafe⟩
  | cons other rest induction =>
      intro current itemSafe completionSafe edgeSafe
      obtain ⟨forward, forwardEq, forwardItemSafe, forwardCompletionSafe,
        forwardEdgeSafe⟩ := attemptCompletion?_total_allSafe current pivot other
          itemSafe completionSafe edgeSafe
      by_cases same : other = pivot
      · obtain ⟨result, restEq, resultItemSafe, resultCompletionSafe,
          resultEdgeSafe⟩ := induction forward forwardItemSafe
            forwardCompletionSafe forwardEdgeSafe
        exact ⟨result, by
          rw [attemptCompletionsWith?, forwardEq]
          simp only [if_pos same]
          exact restEq,
          resultItemSafe, resultCompletionSafe, resultEdgeSafe⟩
      · obtain ⟨reverse, reverseEq, reverseItemSafe, reverseCompletionSafe,
          reverseEdgeSafe⟩ := attemptCompletion?_total_allSafe forward other pivot
            forwardItemSafe forwardCompletionSafe forwardEdgeSafe
        obtain ⟨result, restEq, resultItemSafe, resultCompletionSafe,
          resultEdgeSafe⟩ := induction reverse reverseItemSafe
            reverseCompletionSafe reverseEdgeSafe
        exact ⟨result, by
          simp [attemptCompletionsWith?, forwardEq, same, reverseEq, restEq],
          resultItemSafe, resultCompletionSafe, resultEdgeSafe⟩


private theorem dequeueRawEdge?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (rest : List (PackedEdge file tokens))
    (queue : current.payload.edgeQueue = edge :: rest)
    (safe : PhaseAEdgeSafe current) :
    ∃ after, dequeueRawEdge? current = some (edge, after) := by
  have fresh := safe.queueFresh edge (by simp [queue])
  unfold dequeueRawEdge?
  rw [queue]
  change ∃ after, (do
    let next ← runMappedPrimitive? current (rawEdgeDequeueAddress edge)
      (fun state => { state with edgeQueue := rest })
    pure (edge, next)) = some (edge, after)
  simp [runMappedPrimitive?, fresh]

private theorem dequeueRawEdge?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (rest : List (PackedEdge file tokens))
    (queue : current.payload.edgeQueue = edge :: rest)
    (safe : PhaseAItemSafe current)
    (selected : dequeueRawEdge? current = some (edge, after)) :
    PhaseAItemSafe after := by
  unfold dequeueRawEdge? at selected
  rw [queue] at selected
  change (do
    let next ← runMappedPrimitive? current (rawEdgeDequeueAddress edge)
      (fun state => { state with edgeQueue := rest })
    pure (edge, next)) = some (edge, after) at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  have payload := phaseA_runMappedPrimitive?_payload current _ _ after nextEq
  have used := phaseA_runMappedPrimitive?_usedRev current _ _ after nextEq
  constructor
  · intro source item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases source <;> cases edge <;>
        simp [RawItemInsertSource.unitKind, rawEdgeDequeueAddress] at equal
    · simpa [payload] using safe.inserted source item old
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases edge <;> simp [rawEdgeDequeueAddress] at equal
    · simpa [payload] using safe.dequeued item old
  · intro item production member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases edge <;> simp [rawEdgeDequeueAddress] at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.predicted item production old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases edge <;> simp [rawEdgeDequeueAddress] at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scanned item old)
  · intro item member
    rw [used] at member
    simp only [List.mem_cons] at member
    rcases member with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases edge <;> simp [rawEdgeDequeueAddress] at equal
    · rw [used]
      exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
  · intro item member usedItem
    rw [payload] at member
    rw [used] at usedItem
    simp only [List.mem_cons] at usedItem
    rcases usedItem with equal | old
    · rcases edge with ⟨edge, valid⟩
      cases edge <;> simp [rawEdgeDequeueAddress] at equal
    · exact safe.queueFresh item member old
  · simpa [payload] using safe.rawNodup
  · simpa [payload] using safe.queueNodup
  · simpa [payload] using safe.queueSubset

private theorem dequeueRawEdge?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (rest : List (PackedEdge file tokens))
    (queue : current.payload.edgeQueue = edge :: rest)
    (safe : PhaseACompletionSafe current)
    (selected : dequeueRawEdge? current = some (edge, after)) :
    PhaseACompletionSafe after := by
  unfold dequeueRawEdge? at selected
  rw [queue] at selected
  change (do
    let next ← runMappedPrimitive? current (rawEdgeDequeueAddress edge)
      (fun state => { state with edgeQueue := rest })
    pure (edge, next)) = some (edge, after) at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  apply runMappedPrimitive?_completionSafe_of_not_insert current after _ _ safe
    _ nextEq
  intro waiting finished equal
  rcases edge with ⟨edge, valid⟩
  cases edge <;> simp [rawEdgeDequeueAddress] at equal

private theorem dequeueRawEdge?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (rest : List (PackedEdge file tokens))
    (queue : current.payload.edgeQueue = edge :: rest)
    (safe : PhaseAEdgeSafe current)
    (selected : dequeueRawEdge? current = some (edge, after)) :
    PhaseAEdgeSafe after := by
  unfold dequeueRawEdge? at selected
  rw [queue] at selected
  change (do
    let next ← runMappedPrimitive? current (rawEdgeDequeueAddress edge)
      (fun state => { state with edgeQueue := rest })
    pure (edge, next)) = some (edge, after) at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  have payload := phaseA_runMappedPrimitive?_payload current _ _ after nextEq
  have used := phaseA_runMappedPrimitive?_usedRev current _ _ after nextEq
  have queueUnique := safe.queueAddressNodup
  rw [queue, List.map_cons, List.nodup_cons] at queueUnique
  have payloadQueue : after.payload.edgeQueue = rest := by simp [payload]
  constructor
  · intro candidate member
    rw [payloadQueue] at member
    rw [used]
    exact List.mem_cons_of_mem _ (safe.inserted candidate (by simp [queue, member]))
  · intro candidate member
    rw [used] at member ⊢
    simp only [List.mem_cons] at member ⊢
    rcases member with equal | old
    · have insertEqual := rawEdgeInsertAddress_eq_of_dequeueAddress_eq
          candidate edge equal
      apply Or.inr
      simpa only [insertEqual] using safe.inserted edge (by simp [queue])
    · exact Or.inr (safe.causal candidate old)
  · intro candidate member usedCandidate
    rw [payloadQueue] at member
    rw [used] at usedCandidate
    simp only [List.mem_cons] at usedCandidate
    rcases usedCandidate with equal | old
    · apply queueUnique.1
      exact List.mem_map.mpr ⟨candidate, member, equal⟩
    · exact safe.queueFresh candidate (by simp [queue, member]) old
  · simpa [payloadQueue] using queueUnique.2


private theorem dequeueRawItem?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) (rest : List (DottedItem tokens))
    (queue : current.payload.itemQueue = item :: rest)
    (safe : PhaseACompletionSafe current)
    (selected : dequeueRawItem? current = some (item, after)) :
    PhaseACompletionSafe after := by
  unfold dequeueRawItem? at selected
  rw [queue] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  exact runMappedPrimitive?_completionSafe_of_not_insert current after _ _ safe
    (by simp) nextEq

private theorem dequeueRawItem?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) (rest : List (DottedItem tokens))
    (queue : current.payload.itemQueue = item :: rest)
    (safe : PhaseAEdgeSafe current)
    (selected : dequeueRawItem? current = some (item, after)) :
    PhaseAEdgeSafe after := by
  unfold dequeueRawItem? at selected
  rw [queue] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  apply runMappedPrimitive?_edgeSafe_of_queue_eq current after _ _ safe
    (by intro state; rfl) _ nextEq
  intro edge equal
  rcases edge with ⟨edge, valid⟩
  cases edge <;> simp [rawEdgeDequeueAddress] at equal

private theorem attemptPrediction?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (safe : PhaseACompletionSafe current)
    (selected : attemptPrediction? current waiting production = some result) :
    PhaseACompletionSafe result := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting production with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact safe
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, itemEq⟩
      have attemptedSafe := runMappedPrimitive?_completionSafe_of_not_insert
        current attempted _ id safe (by simp) attemptedEq
      exact insertRawItem?_completionSafe attempted result .seedOrPrediction
        item attemptedSafe itemEq

private theorem attemptPrediction?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (production : ProductionId)
    (safe : PhaseAEdgeSafe current)
    (selected : attemptPrediction? current waiting production = some result) :
    PhaseAEdgeSafe result := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting production with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact safe
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, itemEq⟩
      have attemptedSafe := runMappedPrimitive?_edgeSafe_of_queue_eq current
        attempted _ id safe (by intro state; rfl) (by
          intro edge equal
          rcases edge with ⟨edge, valid⟩
          cases edge <;> simp [rawEdgeDequeueAddress] at equal) attemptedEq
      exact insertRawItem?_edgeSafe attempted result .seedOrPrediction item
        attemptedSafe itemEq

private theorem attemptPredictions?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result :
        CountedState tokens (PhaseAOpen file tokens)),
      PhaseACompletionSafe current →
      attemptPredictions? waiting productions current = some result →
      PhaseACompletionSafe result := by
  intro productions
  induction productions with
  | nil =>
      intro current result safe selected
      cases selected
      exact safe
  | cons production rest induction =>
      intro current result safe selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (attemptPrediction?_completionSafe current next waiting production safe
          nextEq) restEq

private theorem attemptPredictions?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ productions (current result :
        CountedState tokens (PhaseAOpen file tokens)),
      PhaseAEdgeSafe current →
      attemptPredictions? waiting productions current = some result →
      PhaseAEdgeSafe result := by
  intro productions
  induction productions with
  | nil =>
      intro current result safe selected
      cases selected
      exact safe
  | cons production rest induction =>
      intro current result safe selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (attemptPrediction?_edgeSafe current next waiting production safe nextEq)
        restEq

private theorem insertScannedRawEdge?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before after : DottedItem tokens) (cursor : TerminalCursor tokens)
    (edge : PackedEdge file tokens)
    (shape : edge.val = .scanned before after cursor)
    (safe : PhaseACompletionSafe current)
    (selected : insertRawEdge? current edge = some result) :
    PhaseACompletionSafe result := by
  unfold insertRawEdge? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    simp only [shape] at selected
    exact runMappedPrimitive?_completionSafe_of_not_insert current result _ _
      safe (by simp) selected

private theorem attemptScan?_completionSafe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens) (safe : PhaseACompletionSafe current)
    (selected : attemptScan? owned current before = some result) :
    PhaseACompletionSafe result := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedSafe := runMappedPrimitive?_completionSafe_of_not_insert
      current attempted _ id safe (by simp) attemptedEq
    cases scan : scannedEdge? owned before with
    | none =>
        simp only [scan] at remainder
        cases remainder
        exact attemptedSafe
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scan, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have itemSafe := insertRawItem?_completionSafe attempted withItem .scan
          after attemptedSafe itemEq
        obtain ⟨cursor, shape⟩ := scannedEdge?_shape owned before after edge scan
        exact insertScannedRawEdge?_completionSafe withItem result before after
          cursor edge shape itemSafe edgeEq
  next notApplicable =>
    cases selected
    exact safe

private theorem attemptScan?_edgeSafe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens) (safe : PhaseAEdgeSafe current)
    (selected : attemptScan? owned current before = some result) :
    PhaseAEdgeSafe result := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedSafe := runMappedPrimitive?_edgeSafe_of_queue_eq current
      attempted _ id safe (by intro state; rfl) (by
        intro edge equal
        rcases edge with ⟨edge, valid⟩
        cases edge <;> simp [rawEdgeDequeueAddress] at equal) attemptedEq
    cases scan : scannedEdge? owned before with
    | none =>
        simp only [scan] at remainder
        cases remainder
        exact attemptedSafe
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scan, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have itemSafe := insertRawItem?_edgeSafe attempted withItem .scan after
          attemptedSafe itemEq
        exact insertRawEdge?_edgeSafe withItem result edge itemSafe edgeEq
  next notApplicable =>
    cases selected
    exact safe


private structure PhaseAAllSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) : Prop where
  item : PhaseAItemSafe current
  completion : PhaseACompletionSafe current
  edge : PhaseAEdgeSafe current

private theorem beginPhaseA_allSafe
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAAllSafe (beginPhaseA file tokens) :=
  ⟨beginPhaseA_itemSafe file tokens, beginPhaseA_completionSafe file tokens,
    beginPhaseA_edgeSafe file tokens⟩

private theorem insertRawSeeds?_total_allSafe
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ seeds (current : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAAllSafe current →
      ∃ result, insertRawSeeds? seeds current = some result ∧
        PhaseAAllSafe result := by
  intro seeds
  induction seeds with
  | nil =>
      intro current safe
      exact ⟨current, rfl, safe⟩
  | cons item rest induction =>
      intro current safe
      obtain ⟨next, nextEq⟩ := insertRawItem?_total current
        .seedOrPrediction item safe.item
      have nextSafe : PhaseAAllSafe next := {
        item := insertRawItem?_itemSafe current next .seedOrPrediction item
          safe.item nextEq
        completion := insertRawItem?_completionSafe current next
          .seedOrPrediction item safe.completion nextEq
        edge := insertRawItem?_edgeSafe current next .seedOrPrediction item
          safe.edge nextEq
      }
      obtain ⟨result, restEq, resultSafe⟩ := induction next nextSafe
      exact ⟨result, by simp [insertRawSeeds?, nextEq, restEq], resultSafe⟩

private theorem processRawItem?_total_allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (safe : PhaseAAllSafe current) (work : PhaseAItemWorkFresh current item) :
    ∃ result, processRawItem? owned item current = some result ∧
      PhaseAAllSafe result := by
  obtain ⟨predicted, predictedEq, predictedItemSafe, predictedDequeued,
      predictedScanFresh, predictedEdgeFresh⟩ :=
    attemptPredictions?_total_itemSafe item allProductionIds current
      allProductionIds_nodup safe.item work.dequeued
      (by intro production member; exact work.predictions production)
      work.scan work.scannedEdge
  have predictedCompletionSafe := attemptPredictions?_completionSafe item
    allProductionIds current predicted safe.completion predictedEq
  have predictedEdgeSafe := attemptPredictions?_edgeSafe item allProductionIds
    current predicted safe.edge predictedEq
  obtain ⟨scanned, scannedEq, scannedItemSafe⟩ :=
    attemptScan?_total_itemSafe owned predicted item predictedItemSafe
      predictedDequeued predictedScanFresh predictedEdgeFresh
  have scannedCompletionSafe := attemptScan?_completionSafe owned predicted scanned
    item predictedCompletionSafe scannedEq
  have scannedEdgeSafe := attemptScan?_edgeSafe owned predicted scanned item
    predictedEdgeSafe scannedEq
  obtain ⟨result, completionEq, resultItemSafe, resultCompletionSafe,
    resultEdgeSafe⟩ := attemptCompletionsWith?_total_allSafe item
      scanned.payload.rawItems scanned scannedItemSafe scannedCompletionSafe
      scannedEdgeSafe
  refine ⟨result, ?_, ⟨resultItemSafe, resultCompletionSafe,
    resultEdgeSafe⟩⟩
  unfold processRawItem?
  rw [predictedEq]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [scannedEq]
  exact completionEq

private theorem dequeueRawItem?_queue_shape
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens)
    (selected : dequeueRawItem? current = some (item, after)) :
    ∃ rest, current.payload.itemQueue = item :: rest := by
  unfold dequeueRawItem? at selected
  cases queue : current.payload.itemQueue with
  | nil => simp [queue] at selected
  | cons head rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, output⟩
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at output
      rcases output with ⟨headEq, nextEqual⟩
      subst head
      exact ⟨rest, rfl⟩

private theorem dequeueRawEdge?_queue_shape
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (selected : dequeueRawEdge? current = some (edge, after)) :
    ∃ rest, current.payload.edgeQueue = edge :: rest := by
  unfold dequeueRawEdge? at selected
  cases queue : current.payload.edgeQueue with
  | nil => simp [queue] at selected
  | cons head rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, output⟩
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at output
      rcases output with ⟨headEq, nextEqual⟩
      subst head
      exact ⟨rest, rfl⟩

private theorem dequeueRawItem?_allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (item : DottedItem tokens) (safe : PhaseAAllSafe current)
    (selected : dequeueRawItem? current = some (item, after)) :
    PhaseAAllSafe after ∧ PhaseAItemWorkFresh after item := by
  obtain ⟨rest, queue⟩ := dequeueRawItem?_queue_shape current after item selected
  exact ⟨{
    item := dequeueRawItem?_itemSafe current (item, after) safe.item selected
    completion := dequeueRawItem?_completionSafe current after item rest queue
      safe.completion selected
    edge := dequeueRawItem?_edgeSafe current after item rest queue safe.edge selected
  }, dequeueRawItem?_workFresh current after item rest queue safe.item selected⟩

private theorem dequeueRawEdge?_allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens) (safe : PhaseAAllSafe current)
    (selected : dequeueRawEdge? current = some (edge, after)) :
    PhaseAAllSafe after := by
  obtain ⟨rest, queue⟩ := dequeueRawEdge?_queue_shape current after edge selected
  exact {
    item := dequeueRawEdge?_itemSafe current after edge rest queue safe.item selected
    completion := dequeueRawEdge?_completionSafe current after edge rest queue
      safe.completion selected
    edge := dequeueRawEdge?_edgeSafe current after edge rest queue safe.edge selected
  }


private theorem processRawItem?_allSafe_of_selected
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (safe : PhaseAAllSafe current) (work : PhaseAItemWorkFresh current item)
    (selected : processRawItem? owned item current = some result) :
    PhaseAAllSafe result := by
  obtain ⟨computed, computedEq, computedSafe⟩ :=
    processRawItem?_total_allSafe owned item current safe work
  rw [selected] at computedEq
  cases computedEq
  exact computedSafe

private theorem PhaseAQueueReachable.allSafe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (start current : CountedState tokens (PhaseAOpen file tokens))
    (reachable : PhaseAQueueReachable owned start current)
    (safe : PhaseAAllSafe start) : PhaseAAllSafe current := by
  induction reachable with
  | refl => exact safe
  | item prior dequeued processed induction =>
      obtain ⟨afterSafe, work⟩ := dequeueRawItem?_allSafe _ _ _ induction
        dequeued
      exact processRawItem?_allSafe_of_selected owned _ _ _ afterSafe work
        processed
  | edge prior dequeued induction =>
      exact dequeueRawEdge?_allSafe _ _ _ induction dequeued

private theorem PhaseAAllSafe.not_blocked
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (safe : PhaseAAllSafe current) : ¬ PhaseAQueueBlocked owned current := by
  unfold PhaseAQueueBlocked
  cases items : current.payload.itemQueue with
  | nil =>
      cases edges : current.payload.edgeQueue with
      | nil => simp
      | cons edge rest =>
          intro blocked
          obtain ⟨after, selected⟩ := dequeueRawEdge?_total current edge rest
            edges safe.edge
          rw [selected] at blocked
          simp at blocked
  | cons item rest =>
      intro blocked
      rcases blocked with dequeueFailed | processFailed
      · obtain ⟨after, selected⟩ := dequeueRawItem?_total current item rest
          items safe.item
        rw [selected] at dequeueFailed
        simp at dequeueFailed
      · rcases processFailed with ⟨pivot, after, dequeued, processFailed⟩
        obtain ⟨afterSafe, work⟩ := dequeueRawItem?_allSafe current after
          pivot safe dequeued
        obtain ⟨result, processed, resultSafe⟩ :=
          processRawItem?_total_allSafe owned pivot after afterSafe work
        rw [processed] at processFailed
        simp at processFailed

private theorem executePhaseA?_total
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    ∃ result, executePhaseA? file tokens owned = some result := by
  obtain ⟨seeded, seededEq, seededSafe⟩ :=
    insertRawSeeds?_total_allSafe (rawSeedItems tokens)
      (beginPhaseA file tokens) (beginPhaseA_allSafe file tokens)
  cases execution : executePhaseA? file tokens owned with
  | some result => exact ⟨result, rfl⟩
  | none =>
      rcases executePhaseA?_failure_boundary file tokens owned execution with
        seedFailed | ⟨actualSeeded, blocked, actualSeededEq, reachable,
          operationBlocked⟩
      · rw [seededEq] at seedFailed
        simp at seedFailed
      · rw [seededEq] at actualSeededEq
        cases actualSeededEq
        have blockedSafe := PhaseAQueueReachable.allSafe owned seeded blocked
          reachable seededSafe
        exact (blockedSafe.not_blocked owned blocked operationBlocked).elim

private theorem executePhaseA?_total_membership_eq
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    ∃ result, executePhaseA? file tokens owned = some result ∧
      ∀ item, item ∈ result.payload.rawItems ↔ item ∈ rawSaturation tokens := by
  obtain ⟨result, selected⟩ := executePhaseA?_total file tokens owned
  exact ⟨result, selected,
    executePhaseA?_membership_eq file tokens owned result selected⟩

private def allEvidenceIndexKinds : List EvidenceIndexKind := [
  .terminalWindow,
  .exactSlice,
  .greatestEnd,
  .delimiterOrRegion
]

private def allEvidenceIndexSubjects :
    List (PriorityGuardId ⊕ GrammarRuleId) :=
  allPriorityGuardIds.map .inl ++ allGrammarRuleIds.map .inr

private def allEvidenceIndexAddresses (tokens : List Token) :
    List (EvidenceIndexAddress tokens) :=
  allEvidenceIndexKinds.flatMap fun kind =>
    allEvidenceIndexSubjects.flatMap fun subject =>
      (List.finRange (tokens.length + 2)).flatMap fun contextStart =>
        (List.finRange (tokens.length + 2)).flatMap fun siteCursor =>
          (List.finRange (tokens.length + 2)).map fun resultEnd => {
            kind := kind
            subject := subject
            contextStart := contextStart
            siteCursor := siteCursor
            resultEnd := resultEnd
          }

private theorem allEvidenceIndexAddresses_complete
    {tokens : List Token} (address : EvidenceIndexAddress tokens) :
    address ∈ allEvidenceIndexAddresses tokens := by
  rcases address with
    ⟨kind, subject, contextStart, siteCursor, resultEnd⟩
  rw [allEvidenceIndexAddresses, List.mem_flatMap]
  refine ⟨kind, ?_, ?_⟩
  · cases kind <;> simp [allEvidenceIndexKinds]
  · rw [List.mem_flatMap]
    refine ⟨subject, ?_, ?_⟩
    · cases subject with
      | inl guard =>
          rw [allEvidenceIndexSubjects, List.mem_append]
          left
          rw [List.mem_map]
          exact ⟨guard, by cases guard <;> simp [allPriorityGuardIds], rfl⟩
      | inr rule =>
          rw [allEvidenceIndexSubjects, List.mem_append]
          right
          rw [List.mem_map]
          exact ⟨rule, by cases rule <;> simp [allGrammarRuleIds], rfl⟩
    · rw [List.mem_flatMap]
      refine ⟨contextStart, List.mem_finRange _, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨siteCursor, List.mem_finRange _, ?_⟩
      rw [List.mem_map]
      exact ⟨resultEnd, List.mem_finRange _, rfl⟩

private structure PhaseAEvidenceEntry (tokens : List Token) where
  address : EvidenceIndexAddress tokens
  selected : Bool

private structure PhaseAIndexed
    (file : WorkspaceFile) (tokens : List Token) where
  phaseA : PhaseAOpen file tokens
  entries : List (PhaseAEvidenceEntry tokens)

private abbrev PhaseAIndexEvaluator
    (file : WorkspaceFile) (tokens : List Token) :=
  PhaseAOpen file tokens → EvidenceIndexAddress tokens → Bool

private def beginPhaseAIndexing
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    CountedState tokens (PhaseAIndexed file tokens) := {
  payload := ⟨current.payload, []⟩
  counter := current.counter
}

private def materializePhaseAIndexes?
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens) :
    List (EvidenceIndexAddress tokens) →
      CountedState tokens (PhaseAIndexed file tokens) →
      Option (CountedState tokens (PhaseAIndexed file tokens))
  | [], current => some current
  | address :: rest, current => do
      let next ← runMappedPrimitive? current
        (UnitAddress.evidenceIndex address) fun state => {
          state with entries := state.entries ++ [{
            address := address
            selected := evaluate state.phaseA address
          }]
        }
      materializePhaseAIndexes? evaluate rest next

private def indexSaturatedPhaseAWith?
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (CountedState tokens (PhaseAIndexed file tokens)) :=
  if _itemsDone : current.payload.itemQueue = [] then
    if _edgesDone : current.payload.edgeQueue = [] then
      if _saturated : current.payload.rawItems = rawSaturation tokens then
        materializePhaseAIndexes? evaluate
          (allEvidenceIndexAddresses tokens)
          (beginPhaseAIndexing current)
      else
        none
    else
      none
  else
    none

private structure PhaseBIndexed
    (file : WorkspaceFile) (tokens : List Token) where
  phaseB : PhaseBOpen file tokens
  indexes : List (PhaseAEvidenceEntry tokens)

private def enterIndexedPhaseB?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens)) :
    Option (CountedState tokens (PhaseBIndexed file tokens)) := do
  let entered ← enterPhaseB? {
    payload := current.payload.phaseA
    counter := current.counter
  }
  pure {
    payload := ⟨entered.payload, current.payload.entries⟩
    counter := entered.counter
  }

private def finalizeNextIndexedGuardWithDecision?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (decision : GuardDecision) :
    Option (CountedState tokens (PhaseBIndexed file tokens)) := do
  let finalized ← finalizeNextGuardWithDecision? {
    payload := current.payload.phaseB
    counter := current.counter
  } decision
  pure {
    payload := ⟨finalized.payload, current.payload.indexes⟩
    counter := finalized.counter
  }

private def sealIndexedPhaseB?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens)) :
    Option (CountedState tokens (PhaseBSealed file tokens)) :=
  sealPhaseB? {
    payload := current.payload.phaseB
    counter := current.counter
  }

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def rawRecognizesBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) : Bool :=
  phaseA.rawItems.any fun item =>
    item.dot.val == item.production.rhs.length &&
      item.production.lhs == symbol &&
      item.origin == start && item.current == finish

private def rawGreatestEndBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) : Bool :=
  rawRecognizesBool phaseA symbol start finish &&
    decide (finish.val ≤ upperBound.val) &&
    (List.finRange (tokens.length + 2)).all fun candidate =>
      if candidate.val ≤ upperBound.val then
        !rawRecognizesBool phaseA symbol start candidate ||
          decide (candidate.val ≤ finish.val)
      else
        true

private def phaseAGreatestEndIndexEvaluator
    {file : WorkspaceFile} {tokens : List Token} :
    PhaseAIndexEvaluator file tokens :=
  fun phaseA address =>
    match address.kind, address.subject with
    | .greatestEnd, .inr rule =>
        rawGreatestEndBool phaseA (.rule rule)
          address.contextStart address.siteCursor address.resultEnd
    | _, _ => false

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Look up one grammar terminal at an exact raw-stream boundary. -/
private def phaseATerminalAtBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) : Bool :=
  if inRange : boundary.val < tokens.length + 1 then
    let cursor : TerminalCursor tokens := ⟨boundary.val, inRange⟩
    (MatchedTerminal.atCursor? file tokens owned terminal cursor).isSome
  else
    false

/-- Look up one grammar terminal and its exact successor boundary. -/
private def phaseAImmediatelyAfterTerminalBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (boundary after : Boundary tokens) : Bool :=
  phaseATerminalAtBool owned terminal boundary &&
    decide (after.val = boundary.val + 1)

/-- Observe one retained symbol without consulting a parser judgment. -/
private def phaseASymbolAtBool
    {tokens : List Token} (boundary : Boundary tokens)
    (symbol : Symbol) : Bool :=
  if inRange : boundary.val < tokens.length then
    decide (tokens[boundary.val].payload = .symbol symbol)
  else
    false

/-- Observe one retained symbol and its exact successor boundary. -/
private def phaseAImmediatelyAfterSymbolBool
    {tokens : List Token} (symbol : Symbol)
    (boundary after : Boundary tokens) : Bool :=
  phaseASymbolAtBool boundary symbol &&
    decide (after.val = boundary.val + 1)

/-- Test one retained token against one terminal class.  Logical EOF is
intentionally excluded from exact slices. -/
private def phaseAExactSliceAtomBool
    (tokens : List Token) (terminal : TerminalSymbol)
    (absolute : Nat) : Bool :=
  if inRange : absolute < tokens.length then
    terminalMatchesBool terminal (.retained tokens[absolute])
  else
    false

/-- Execute one exact retained-terminal slice. -/
private def phaseAExactSliceBool
    (tokens : List Token) (start finish : Boundary tokens)
    (classes : List TerminalSymbol) : Bool :=
  decide (finish.val = start.val + classes.length) &&
    (List.ofFn fun index : Fin classes.length =>
      phaseAExactSliceAtomBool tokens (classes.get index)
        (start.val + index.val)).all id

/-- Test membership in one fixed nonempty symbol family. -/
private def phaseASymbolAllowedBool
    (symbol : Symbol) (allowed : NonemptyList Symbol) : Bool :=
  decide (symbol = allowed.head) ||
    allowed.tail.any fun candidate => decide (symbol = candidate)

/-- Observe an allowed retained symbol at one boundary. -/
private def phaseAAllowedSymbolAtBool
    {tokens : List Token} (boundary : Boundary tokens)
    (allowed : NonemptyList Symbol) : Bool :=
  if inRange : boundary.val < tokens.length then
    match tokens[boundary.val].payload with
    | .symbol symbol => phaseASymbolAllowedBool symbol allowed
    | _ => false
  else
    false

/-- Construct a chart boundary from a checked natural coordinate. -/
private def phaseABoundaryAt?
    (tokens : List Token) (coordinate : Nat) :
    Option (Boundary tokens) :=
  if inRange : coordinate < tokens.length + 2 then
    some ⟨coordinate, inRange⟩
  else
    none

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- The proof-free delimiter stack used only while materializing Phase A. -/
private inductive PhaseADelimiterCloser where
  | rightParen
  | rightBracket
  | rightBrace
  deriving BEq, DecidableEq

private abbrev PhaseADelimiterStack := List PhaseADelimiterCloser

/-- Execute one deterministic delimiter-stack transition. -/
private def phaseADelimiterStep? :
    PhaseADelimiterStack → TokenKind → Option PhaseADelimiterStack
  | before, .symbol .leftParen =>
      some (.rightParen :: before)
  | before, .symbol .leftBracket =>
      some (.rightBracket :: before)
  | before, .symbol .leftBrace =>
      some (.rightBrace :: before)
  | .rightParen :: rest, .symbol .rightParen => some rest
  | .rightBracket :: rest, .symbol .rightBracket => some rest
  | .rightBrace :: rest, .symbol .rightBrace => some rest
  | _, .symbol .rightParen => none
  | _, .symbol .rightBracket => none
  | _, .symbol .rightBrace => none
  | before, _ => some before

/-- Run exactly `fuel` retained-token delimiter transitions. -/
private def phaseADelimiterRunFrom?
    (tokens : List Token) : Nat → Nat → PhaseADelimiterStack →
      Option PhaseADelimiterStack
  | 0, _, before => some before
  | fuel + 1, cursor, before =>
      if inRange : cursor < tokens.length then
        match phaseADelimiterStep? before tokens[cursor].payload with
        | some after =>
            phaseADelimiterRunFrom? tokens fuel (cursor + 1) after
        | none => none
      else
        none

/-- Execute an exact half-open delimiter range. -/
private def phaseADelimiterRun?
    (tokens : List Token) (before : PhaseADelimiterStack)
    (start finish : Boundary tokens) : Option PhaseADelimiterStack :=
  if _ordered : start.val ≤ finish.val then
    phaseADelimiterRunFrom? tokens (finish.val - start.val)
      start.val before
  else
    none

/-- Test whether a half-open range returns to its starting depth. -/
private def phaseASameDelimiterDepthBool
    (tokens : List Token) (start finish : Boundary tokens) : Bool :=
  decide (phaseADelimiterRun? tokens [] start finish = some [])

/-- A protected step rejects consumption of the bottom stack entry. -/
private def phaseAProtectedDelimiterStep?
    (before : PhaseADelimiterStack) (token : TokenKind) :
    Option PhaseADelimiterStack :=
  match before with
  | [] => none
  | _ :: _ =>
      match phaseADelimiterStep? before token with
      | some after@(_ :: _) => some after
      | _ => none

/-- Run an exact range while retaining a nonempty stack. -/
private def phaseAProtectedDelimiterRunFrom?
    (tokens : List Token) : Nat → Nat → PhaseADelimiterStack →
      Option PhaseADelimiterStack
  | 0, _, [] => none
  | 0, _, before@(_ :: _) => some before
  | fuel + 1, cursor, before =>
      if inRange : cursor < tokens.length then
        match phaseAProtectedDelimiterStep?
            before tokens[cursor].payload with
        | some after =>
            phaseAProtectedDelimiterRunFrom? tokens fuel
              (cursor + 1) after
        | none => none
      else
        none

/-- Execute one protected half-open delimiter range. -/
private def phaseAProtectedDelimiterRun?
    (tokens : List Token) (before : PhaseADelimiterStack)
    (start finish : Boundary tokens) : Option PhaseADelimiterStack :=
  if _ordered : start.val ≤ finish.val then
    phaseAProtectedDelimiterRunFrom? tokens
      (finish.val - start.val) start.val before
  else
    none

/-- Select the only legal closing symbol and stack entry for an opener. -/
private def phaseADelimiterPair? :
    Symbol → Option (Symbol × PhaseADelimiterCloser)
  | .leftParen => some (.rightParen, .rightParen)
  | .leftBracket => some (.rightBracket, .rightBracket)
  | .leftBrace => some (.rightBrace, .rightBrace)
  | _ => none

/-- Test one exact matched-delimiter pair with a protected interior. -/
private def phaseAMatchingDelimiterBool
    (tokens : List Token) (openCursor closeCursor : Boundary tokens)
    (opening closing : Symbol) : Bool :=
  match phaseADelimiterPair? opening with
  | none => false
  | some (expectedClosing, closer) =>
      decide (closing = expectedClosing) &&
        phaseASymbolAtBool openCursor opening &&
        phaseASymbolAtBool closeCursor closing &&
        match phaseABoundaryAt? tokens (openCursor.val + 1) with
        | none => false
        | some interiorStart =>
            decide (phaseAProtectedDelimiterRun? tokens [closer]
              interiorStart closeCursor = some [closer])

/-- Test that `cursor` is the first allowed symbol back at the starting
delimiter depth. -/
private def phaseANextSameDepthDelimiterBool
    (tokens : List Token) (start cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) : Bool :=
  phaseASameDelimiterDepthBool tokens start cursor &&
    phaseAAllowedSymbolAtBool cursor allowed &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if start.val ≤ earlier.val && earlier.val < cursor.val &&
          phaseASameDelimiterDepthBool tokens start earlier then
        !phaseAAllowedSymbolAtBool earlier allowed
      else
        true

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Recognize the fixed match-arm pattern-list header at one same-depth pipe. -/
private def phaseAArmHeaderBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (regionStart cursor : Boundary tokens) : Bool :=
  decide (regionStart.val ≤ cursor.val) &&
    phaseASameDelimiterDepthBool tokens regionStart cursor &&
    phaseASymbolAtBool cursor .pipe &&
    match phaseABoundaryAt? tokens (cursor.val + 1) with
    | none => false
    | some patternStart =>
        phaseAImmediatelyAfterSymbolBool .pipe cursor patternStart &&
          (List.finRange (tokens.length + 2)).any fun arrowCursor =>
            phaseANextSameDepthDelimiterBool tokens patternStart
                arrowCursor ⟨.fatArrow, []⟩ &&
              rawGreatestEndBool phaseA
                (.aux Grammar.matchArmPatternListSite.site)
                patternStart arrowCursor arrowCursor

/-- Test one brace frame strictly containing a cursor. -/
private def phaseAContainingBraceFrameBool
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Bool :=
  decide (openCursor.val < cursor.val) &&
    decide (cursor.val < closeCursor.val) &&
    phaseAMatchingDelimiterBool tokens openCursor closeCursor
      .leftBrace .rightBrace

/-- Test that a containing brace frame has the greatest opening cursor. -/
private def phaseAInnermostContainingBraceFrameBool
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Bool :=
  phaseAContainingBraceFrameBool tokens cursor openCursor closeCursor &&
    (List.finRange (tokens.length + 2)).all fun otherOpen =>
      (List.finRange (tokens.length + 2)).all fun otherClose =>
        !phaseAContainingBraceFrameBool tokens cursor otherOpen otherClose ||
          decide (otherOpen.val ≤ openCursor.val)

/-- Test the first same-frame next-arm header or containing close brace. -/
private def phaseANextArmOrCloseBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (regionStart closeCursor regionEnd : Boundary tokens) : Bool :=
  decide (regionStart.val ≤ regionEnd.val) &&
    decide (regionEnd.val ≤ closeCursor.val) &&
    phaseASameDelimiterDepthBool tokens regionStart regionEnd &&
    (decide (regionEnd = closeCursor) ||
      phaseAArmHeaderBool phaseA regionStart regionEnd) &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if regionStart.val ≤ earlier.val &&
          earlier.val < regionEnd.val &&
          phaseASameDelimiterDepthBool tokens regionStart earlier then
        !(decide (earlier = closeCursor) ||
          phaseAArmHeaderBool phaseA regionStart earlier)
      else
        true

/-- Test the exact nearest braced-body or match-arm statement region. -/
private def phaseANearestStatementRegionBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (regionStart regionEnd : Boundary tokens) : Bool :=
  let bracedBody :=
    (List.finRange (tokens.length + 2)).any fun openCursor =>
      phaseAImmediatelyAfterSymbolBool .leftBrace openCursor regionStart &&
        phaseAMatchingDelimiterBool tokens openCursor regionEnd
          .leftBrace .rightBrace
  let armBody :=
    (List.finRange (tokens.length + 2)).any fun arrowCursor =>
      phaseAImmediatelyAfterSymbolBool .fatArrow arrowCursor regionStart &&
        (List.finRange (tokens.length + 2)).any fun openCursor =>
          (List.finRange (tokens.length + 2)).any fun closeCursor =>
            phaseAInnermostContainingBraceFrameBool tokens arrowCursor
                openCursor closeCursor &&
              phaseANextArmOrCloseBool phaseA regionStart closeCursor regionEnd
  bracedBody || armBody

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Guard-specific terminal observations.  Simple windows retain an exact
successor; G01 canonicalizes both terminal windows into one collision-free
whole-condition cell keyed by its guard site and closing parenthesis. -/
private def phaseATerminalWindowGuardBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Bool :=
  match guard with
  | .G01_statementIf =>
      decide (resultEnd = siteCursor) &&
        match phaseABoundaryAt? tokens (contextStart.val + 1),
            phaseABoundaryAt? tokens (contextStart.val + 2),
            phaseABoundaryAt? tokens (siteCursor.val + 1) with
        | some openCursor, some expressionStart, some afterClose =>
            phaseAImmediatelyAfterTerminalBool owned (.hardKeyword .ifKw)
                contextStart openCursor &&
              phaseAImmediatelyAfterTerminalBool owned (.symbol .leftParen)
                openCursor expressionStart &&
              phaseAImmediatelyAfterTerminalBool owned (.symbol .rightParen)
                siteCursor afterClose &&
              phaseATerminalAtBool owned (.symbol .leftBrace) afterClose
        | _, _, _ => false
  | .G02_matchArmBoundary =>
      phaseAImmediatelyAfterTerminalBool owned (.symbol .pipe)
        siteCursor resultEnd
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime | .G06_patternComptime =>
      phaseAImmediatelyAfterTerminalBool owned
        (.contextualKeyword .comptimeKw) siteCursor resultEnd
  | .G07_leadingDotArguments =>
      phaseAImmediatelyAfterTerminalBool owned (.symbol .leftParen)
        siteCursor resultEnd
  | .G08_terminalExpression => false
  | .G09_genericContext =>
      phaseATerminalAtBool owned (.symbol .fatArrow) resultEnd

/-- The only guard whose decision needs a fixed retained-terminal slice. -/
private def phaseAExactSliceGuardBool
    (tokens : List Token) (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Bool :=
  match guard with
  | .G07_leadingDotArguments =>
      decide (resultEnd = siteCursor) &&
        phaseAExactSliceBool tokens contextStart siteCursor [
          .symbol .dot,
          .category .identifier
        ]
  | _ => false

/-- Guard-specific delimiter and nearest-region observations. -/
private def phaseADelimiterOrRegionGuardBool
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Bool :=
  match guard with
  | .G01_statementIf =>
      decide (resultEnd = siteCursor) &&
        phaseAMatchingDelimiterBool tokens contextStart siteCursor
          .leftParen .rightParen
  | .G02_matchArmBoundary =>
      decide (resultEnd = siteCursor) &&
        phaseAArmHeaderBool phaseA contextStart siteCursor
  | .G06_patternComptime =>
      decide (resultEnd = siteCursor) &&
        phaseANextSameDepthDelimiterBool tokens contextStart siteCursor {
          head := .comma,
          tail := [.rightParen, .fatArrow]
        }
  | .G08_terminalExpression =>
      phaseANearestStatementRegionBool phaseA contextStart resultEnd
  | _ => false

/-- Complete proof-free U01 evaluator for the current four index families.
Rule subjects select greatest-end cells; guard subjects select only the
terminal, exact-slice, delimiter, and region meanings relevant to that guard. -/
private def phaseAObservationIndexEvaluator
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    PhaseAIndexEvaluator file tokens :=
  fun phaseA address =>
    match address.kind, address.subject with
    | .terminalWindow, .inl guard =>
        phaseATerminalWindowGuardBool owned guard
          address.contextStart address.siteCursor address.resultEnd
    | .exactSlice, .inl guard =>
        phaseAExactSliceGuardBool tokens guard
          address.contextStart address.siteCursor address.resultEnd
    | .greatestEnd, .inr rule =>
        rawGreatestEndBool phaseA (.rule rule)
          address.contextStart address.siteCursor address.resultEnd
    | .delimiterOrRegion, .inl guard =>
        phaseADelimiterOrRegionGuardBool phaseA guard
          address.contextStart address.siteCursor address.resultEnd
    | _, _ => false

/-- Compare evidence addresses without exposing the private carrier. -/
private def phaseAEvidenceAddressEqBool
    {tokens : List Token}
    (left right : EvidenceIndexAddress tokens) : Bool :=
  left.kind == right.kind && left.subject == right.subject &&
    left.contextStart == right.contextStart &&
    left.siteCursor == right.siteCursor &&
    left.resultEnd == right.resultEnd

/-- Read one fully materialized U01 cell while retaining absence explicitly. -/
private def phaseAEvidenceEntryAt?
    {tokens : List Token} :
    List (PhaseAEvidenceEntry tokens) → EvidenceIndexAddress tokens →
      Option Bool
  | [], _ => none
  | entry :: rest, address =>
      if phaseAEvidenceAddressEqBool entry.address address then
        some entry.selected
      else
        phaseAEvidenceEntryAt? rest address

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Canonical set presentation in the stable dotted-item enumeration order. -/
private def canonicalRawItems (tokens : List Token)
    (items : List (DottedItem tokens)) : List (DottedItem tokens) :=
  (allDottedItems tokens).filter fun item => rawMemberBool items item

private theorem rawMemberBool_eq_true_iff
    {tokens : List Token} (items : List (DottedItem tokens))
    (item : DottedItem tokens) :
    rawMemberBool items item = true ↔ item ∈ items := by
  rw [rawMemberBool, List.any_eq_true]
  simp only [decide_eq_true_iff]
  constructor
  · rintro ⟨candidate, member, rfl⟩
    exact member
  · intro member
    exact ⟨item, member, rfl⟩

private theorem mem_canonicalRawItems_iff
    {tokens : List Token} (items : List (DottedItem tokens))
    (item : DottedItem tokens) :
    item ∈ canonicalRawItems tokens items ↔ item ∈ items := by
  rw [canonicalRawItems, List.mem_filter,
    rawMemberBool_eq_true_iff]
  exact and_iff_right (allDottedItems_complete item)

/-- Canonical equality is exactly extensional item-membership equality. -/
private theorem canonicalRawItems_eq_iff
    {tokens : List Token} (left right : List (DottedItem tokens)) :
    canonicalRawItems tokens left = canonicalRawItems tokens right ↔
      ∀ item, item ∈ left ↔ item ∈ right := by
  constructor
  · intro equal item
    constructor
    · intro member
      have canonicalMember :=
        (mem_canonicalRawItems_iff left item).mpr member
      rw [equal] at canonicalMember
      exact (mem_canonicalRawItems_iff right item).mp canonicalMember
    · intro member
      have canonicalMember :=
        (mem_canonicalRawItems_iff right item).mpr member
      rw [← equal] at canonicalMember
      exact (mem_canonicalRawItems_iff left item).mp canonicalMember
  · intro sameMembers
    unfold canonicalRawItems
    congr 1
    funext item
    apply Bool.eq_iff_iff.mpr
    simpa only [rawMemberBool_eq_true_iff] using sameMembers item

private def normalizePhaseARawItems
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (_sameMembers :
      canonicalRawItems tokens current.payload.rawItems =
        canonicalRawItems tokens (rawSaturation tokens)) :
    CountedState tokens (PhaseAOpen file tokens) := {
  current with
  payload := {
    current.payload with
    rawItems := rawSaturation tokens
  }
}

/-- The checked normalization changes order only, never item membership. -/
private theorem normalizePhaseARawItems_membership
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (same :
      canonicalRawItems tokens current.payload.rawItems =
        canonicalRawItems tokens (rawSaturation tokens))
    (item : DottedItem tokens) :
    item ∈ (normalizePhaseARawItems current same).payload.rawItems ↔
      item ∈ current.payload.rawItems := by
  have extensional := (canonicalRawItems_eq_iff
    current.payload.rawItems (rawSaturation tokens)).mp same item
  simpa only [normalizePhaseARawItems] using extensional.symm

/-- Order-insensitive Phase-A sealing through the existing exact gate. -/
private def enterPhaseBCanonical?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (CountedState tokens (PhaseBOpen file tokens)) :=
  if _sameMembers :
      canonicalRawItems tokens current.payload.rawItems =
        canonicalRawItems tokens (rawSaturation tokens) then
    enterPhaseB? (normalizePhaseARawItems current _sameMembers)
  else
    none

/-- Order-insensitive Phase-A indexing through the existing exact gate. -/
private def indexSaturatedPhaseACanonicalWith?
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens)) :
    Option (CountedState tokens (PhaseAIndexed file tokens)) :=
  if _sameMembers :
      canonicalRawItems tokens current.payload.rawItems =
        canonicalRawItems tokens (rawSaturation tokens) then
    indexSaturatedPhaseAWith? evaluate
      (normalizePhaseARawItems current _sameMembers)
  else
    none

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Read one exact materialized U01 address. -/
private def phaseBReadIndex?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (kind : EvidenceIndexKind)
    (subject : PriorityGuardId ⊕ GrammarRuleId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Option Bool :=
  phaseAEvidenceEntryAt? entries {
    kind := kind
    subject := subject
    contextStart := contextStart
    siteCursor := siteCursor
    resultEnd := resultEnd
  }

/-- Conjoin materialized reads without treating absence as false. -/
private def phaseBAllReads? : List (Option Bool) → Option Bool
  | [] => some true
  | read :: rest => do
      let selected ← read
      let restSelected ← phaseBAllReads? rest
      pure (selected && restSelected)

/-- Disjoin materialized reads without allowing a successful earlier read to
hide an absent later candidate. -/
private def phaseBAnyReads? : List (Option Bool) → Option Bool
  | [] => some false
  | read :: rest => do
      let selected ← read
      let restSelected ← phaseBAnyReads? rest
      pure (selected || restSelected)

private def phaseBReadTerminalGuard?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Option Bool :=
  phaseBReadIndex? entries .terminalWindow (.inl guard)
    contextStart siteCursor resultEnd

private def phaseBReadExactSliceGuard?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Option Bool :=
  phaseBReadIndex? entries .exactSlice (.inl guard)
    contextStart siteCursor resultEnd

private def phaseBReadGreatestRule?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (rule : GrammarRuleId)
    (start upperBound finish : Boundary tokens) : Option Bool :=
  phaseBReadIndex? entries .greatestEnd (.inr rule)
    start upperBound finish

private def phaseBReadDelimiterGuard?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (guard : PriorityGuardId)
    (contextStart siteCursor resultEnd : Boundary tokens) : Option Bool :=
  phaseBReadIndex? entries .delimiterOrRegion (.inl guard)
    contextStart siteCursor resultEnd

/-- A coordinate outside the boundary universe is a genuine failed
observation, not an absent table cell. -/
private def phaseBWithBoundary?
    (tokens : List Token) (coordinate : Nat)
    (read : Boundary tokens → Option Bool) : Option Bool :=
  match phaseABoundaryAt? tokens coordinate with
  | none => some false
  | some boundary => read boundary

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- G01: `if (` window, exact closing paren, complete expression, and the
adjacent `) {` window. -/
private def phaseBG01Positive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBWithBoundary? tokens (key.siteCursor.val + 1) fun openCursor =>
    phaseBWithBoundary? tokens (key.siteCursor.val + 2) fun expressionStart =>
      phaseBAllReads? [
        phaseBAnyReads?
          ((List.finRange (tokens.length + 2)).map fun closeCursor =>
            phaseBAllReads? [
              phaseBReadTerminalGuard? entries .G01_statementIf
                key.siteCursor closeCursor closeCursor,
              phaseBReadDelimiterGuard? entries .G01_statementIf
                openCursor closeCursor closeCursor,
              phaseBReadGreatestRule? entries .expression
                expressionStart closeCursor closeCursor
            ])
      ]

/-- G02's header and raw pipe observations remain separate because only this
guard has a neutral result. -/
private def phaseBG02Observations?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option (Bool × Bool) := do
  let header ← phaseBReadDelimiterGuard? entries
    .G02_matchArmBoundary key.contextStart key.siteCursor key.siteCursor
  let pipe ← phaseBWithBoundary? tokens (key.siteCursor.val + 1) fun after =>
    phaseBReadTerminalGuard? entries .G02_matchArmBoundary
      key.contextStart key.siteCursor after
  pure (header, pipe)

/-- G03--G05: contextual `comptime` at the exact guard site. -/
private def phaseBComptimeAtSitePositive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBWithBoundary? tokens (key.siteCursor.val + 1) fun after =>
    phaseBReadTerminalGuard? entries key.guard
      key.contextStart key.siteCursor after

/-- G06: contextual `comptime`, then the first same-depth pattern delimiter,
with the greatest expression ending exactly there. -/
private def phaseBG06Positive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBWithBoundary? tokens (key.siteCursor.val + 1) fun expressionStart =>
    phaseBAllReads? [
      phaseBReadTerminalGuard? entries .G06_patternComptime
        key.contextStart key.siteCursor expressionStart,
      phaseBAnyReads?
        ((List.finRange (tokens.length + 2)).map fun limit =>
          phaseBAllReads? [
            phaseBReadDelimiterGuard? entries .G06_patternComptime
              expressionStart limit limit,
            phaseBReadGreatestRule? entries .expression
              expressionStart limit limit
          ])
    ]

/-- G07: exact `. identifier` slice from the retained postfix origin and an
opening parenthesis at the site. -/
private def phaseBG07Positive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBWithBoundary? tokens (key.siteCursor.val + 1) fun after =>
    phaseBAllReads? [
      phaseBReadExactSliceGuard? entries .G07_leadingDotArguments
        key.contextStart key.siteCursor key.siteCursor,
      phaseBReadTerminalGuard? entries .G07_leadingDotArguments
        key.contextStart key.siteCursor after
    ]

/-- G08: the nearest statement-region end is also the greatest complete
expression end from the guarded site. -/
private def phaseBG08Positive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBAnyReads?
    ((List.finRange (tokens.length + 2)).map fun regionEnd =>
      phaseBAllReads? [
        phaseBReadDelimiterGuard? entries .G08_terminalExpression
          key.contextStart key.siteCursor regionEnd,
        phaseBReadGreatestRule? entries .expression
          key.siteCursor regionEnd regionEnd
      ])

/-- G09: the greatest nonempty predicate-list end is an exact fat arrow. -/
private def phaseBG09Positive?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option Bool :=
  phaseBAnyReads?
    ((List.finRange (tokens.length + 2)).map fun arrowCursor =>
      phaseBAllReads? [
        phaseBReadTerminalGuard? entries .G09_genericContext
          key.contextStart key.siteCursor arrowCursor,
        phaseBReadGreatestRule? entries .predicateList
          key.siteCursor arrowCursor arrowCursor
      ])

/-- Derive the declarative table's unique final decision from finalized U01
observations.  Only G02 can return neutral. -/
private def phaseBGuardDecisionFromIndexes?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option GuardDecision :=
  match key.guard with
  | .G01_statementIf => do
      let positive ← phaseBG01Positive? entries key
      pure (if positive then .positive else .negative)
  | .G02_matchArmBoundary => do
      let (header, pipe) ← phaseBG02Observations? entries key
      pure (if header then .positive else if pipe then .negative else .neutral)
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime => do
      let positive ← phaseBComptimeAtSitePositive? entries key
      pure (if positive then .positive else .negative)
  | .G06_patternComptime => do
      let positive ← phaseBG06Positive? entries key
      pure (if positive then .positive else .negative)
  | .G07_leadingDotArguments => do
      let positive ← phaseBG07Positive? entries key
      pure (if positive then .positive else .negative)
  | .G08_terminalExpression => do
      let positive ← phaseBG08Positive? entries key
      pure (if positive then .positive else .negative)
  | .G09_genericContext => do
      let positive ← phaseBG09Positive? entries key
      pure (if positive then .positive else .negative)

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Finalize the next guard using only the materialized Phase-A indexes.
The schedule consumes exactly initialization, the six fixed lookup slots, and
the final write slot for this key. -/
private def finalizeNextIndexedGuard?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens)) :
    Option (CountedState tokens (PhaseBIndexed file tokens)) :=
  match current.payload.phaseB.remaining with
  | [] => none
  | key :: rest => do
      let initialized ← runMappedPrimitive? current
        (.guardFinalize .initializeUndecided key)
        fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            state.phaseB with
            cells := fun candidate =>
              if candidate = key then some .undecided
              else state.phaseB.cells candidate
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)
      let lookups ← chargeAddresses? initialized
        (preFinalGuardSlots.map fun slot => .guardFinalize slot key)
      let decision ← phaseBGuardDecisionFromIndexes?
        lookups.payload.indexes key
      runMappedPrimitive? lookups
        (.guardFinalize .writeFinalDecision key)
        fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            phaseA := state.phaseB.phaseA
            cells := fun candidate =>
              if candidate = key then some (.final decision)
              else state.phaseB.cells candidate
            remaining := rest
            finalizedRev := key :: state.phaseB.finalizedRev
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)

/-- Run the external-decision-free Phase-B worklist. -/
private def runIndexedPhaseB?
    {file : WorkspaceFile} {tokens : List Token} :
    Nat → CountedState tokens (PhaseBIndexed file tokens) →
      Option (CountedState tokens (PhaseBIndexed file tokens))
  | 0, current =>
      if current.payload.phaseB.remaining = [] then some current else none
  | fuel + 1, current =>
      match current.payload.phaseB.remaining with
      | [] => some current
      | _ :: _ => do
          let next ← finalizeNextIndexedGuard? current
          runIndexedPhaseB? fuel next

/-- A successful Phase-B worklist run has consumed every guard key. -/
private theorem runIndexedPhaseB?_remaining_empty
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ fuel
      (current result : CountedState tokens (PhaseBIndexed file tokens)),
      runIndexedPhaseB? fuel current = some result →
        result.payload.phaseB.remaining = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result selected
      rw [runIndexedPhaseB?] at selected
      split at selected
      · cases selected
        assumption
      · contradiction
  | succ previous induction =>
      intro current result selected
      rw [runIndexedPhaseB?] at selected
      cases remaining : current.payload.phaseB.remaining with
      | nil =>
          simp only [remaining] at selected
          cases selected
          exact remaining
      | cons key rest =>
          simp only [remaining] at selected
          cases finalized : finalizeNextIndexedGuard? current with
          | none => simp [finalized] at selected
          | some next =>
              rw [finalized] at selected
              exact induction next result selected

/-- Enter, exhaust, and seal Phase B with no caller-supplied decisions. -/
private def executeIndexedPhaseB?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens)) :
    Option (CountedState tokens (PhaseBSealed file tokens)) := do
  let entered ← enterIndexedPhaseB? current
  let finalized ← runIndexedPhaseB?
    (allGuardInstanceKeys tokens).length entered
  sealIndexedPhaseB? finalized

/-- Execute the landed raw Phase A, materialize the proof-free observations,
then derive and seal every Phase-B guard decision. -/
private def executeObservedPhaseAB?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    Option (CountedState tokens (PhaseBSealed file tokens)) := do
  let phaseA ← executePhaseA? file tokens owned
  let indexed ← indexSaturatedPhaseACanonicalWith?
    (phaseAObservationIndexEvaluator owned) phaseA
  executeIndexedPhaseB? indexed

end Chart

namespace Chart
open Grammar
open Solcore.Workspace
private theorem phaseBFinRange_nodup (size : Nat) :
    (List.finRange size).Nodup := by
  induction size with
  | zero => simp
  | succ size induction =>
      rw [show List.finRange (size + 1) =
        0 :: (List.finRange size).map Fin.succ from List.finRange_succ]
      rw [List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_map] at member
        rcases member with ⟨value, _, equal⟩
        exact Fin.succ_ne_zero value equal
      · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        exact induction.imp fun different equal =>
          different (Fin.succ_inj.mp equal)

private structure EvidenceBoundaryPair (tokens : List Token) where
  siteCursor : Boundary tokens
  resultEnd : Boundary tokens
private theorem EvidenceBoundaryPair.eq_of_fields
    {tokens : List Token} {left right : EvidenceBoundaryPair tokens}
    (siteCursor : left.siteCursor = right.siteCursor)
    (resultEnd : left.resultEnd = right.resultEnd) : left = right := by
  cases left
  cases right
  simp only at siteCursor resultEnd
  cases siteCursor
  cases resultEnd
  rfl
private def allEvidenceBoundaryPairs (tokens : List Token) :
    List (EvidenceBoundaryPair tokens) :=
  (List.finRange (tokens.length + 2)).flatMap fun siteCursor =>
    (List.finRange (tokens.length + 2)).map fun resultEnd =>
      ⟨siteCursor, resultEnd⟩

private theorem allEvidenceBoundaryPairs_nodup (tokens : List Token) :
    (allEvidenceBoundaryPairs tokens).Nodup := by
  apply dependentEnumeration_nodup
    (List.finRange (tokens.length + 2))
    (fun _ => List.finRange (tokens.length + 2))
    (fun siteCursor resultEnd =>
      (⟨siteCursor, resultEnd⟩ : EvidenceBoundaryPair tokens))
    (phaseBFinRange_nodup _)
    (fun _ => phaseBFinRange_nodup _)
  intro left right leftEnd rightEnd equal
  have owner : left = right :=
    congrArg EvidenceBoundaryPair.siteCursor equal
  subst right
  have item : leftEnd = rightEnd :=
    congrArg EvidenceBoundaryPair.resultEnd equal
  subst rightEnd
  rfl

private structure EvidenceBoundaryTriple (tokens : List Token) where
  contextStart : Boundary tokens
  pair : EvidenceBoundaryPair tokens

private theorem EvidenceBoundaryTriple.eq_of_fields
    {tokens : List Token} {left right : EvidenceBoundaryTriple tokens}
    (contextStart : left.contextStart = right.contextStart)
    (pair : left.pair = right.pair) : left = right := by
  cases left
  cases right
  simp only at contextStart pair
  cases contextStart
  cases pair
  rfl

private def allEvidenceBoundaryTriples (tokens : List Token) :
    List (EvidenceBoundaryTriple tokens) :=
  (List.finRange (tokens.length + 2)).flatMap fun contextStart =>
    (allEvidenceBoundaryPairs tokens).map fun pair =>
      ⟨contextStart, pair⟩

private theorem allEvidenceBoundaryTriples_nodup (tokens : List Token) :
    (allEvidenceBoundaryTriples tokens).Nodup := by
  apply dependentEnumeration_nodup
    (List.finRange (tokens.length + 2))
    (fun _ => allEvidenceBoundaryPairs tokens)
    (fun contextStart pair =>
      (⟨contextStart, pair⟩ : EvidenceBoundaryTriple tokens))
    (phaseBFinRange_nodup _)
    (fun _ => allEvidenceBoundaryPairs_nodup tokens)
  intro left right leftPair rightPair equal
  have owner : left = right :=
    congrArg EvidenceBoundaryTriple.contextStart equal
  subst right
  have item : leftPair = rightPair :=
    congrArg EvidenceBoundaryTriple.pair equal
  subst rightPair
  rfl

private structure EvidenceSubjectCoordinates (tokens : List Token) where
  subject : PriorityGuardId ⊕ GrammarRuleId
  boundaries : EvidenceBoundaryTriple tokens

private theorem EvidenceSubjectCoordinates.eq_of_fields
    {tokens : List Token} {left right : EvidenceSubjectCoordinates tokens}
    (subject : left.subject = right.subject)
    (boundaries : left.boundaries = right.boundaries) : left = right := by
  cases left
  cases right
  simp only at subject boundaries
  cases subject
  cases boundaries
  rfl

private def allEvidenceSubjectCoordinates (tokens : List Token) :
    List (EvidenceSubjectCoordinates tokens) :=
  allEvidenceIndexSubjects.flatMap fun subject =>
    (allEvidenceBoundaryTriples tokens).map fun boundaries =>
      ⟨subject, boundaries⟩

private theorem allEvidenceIndexSubjects_nodup :
    allEvidenceIndexSubjects.Nodup := by
  decide

private theorem allEvidenceSubjectCoordinates_nodup (tokens : List Token) :
    (allEvidenceSubjectCoordinates tokens).Nodup := by
  apply dependentEnumeration_nodup
    allEvidenceIndexSubjects
    (fun _ => allEvidenceBoundaryTriples tokens)
    (fun subject boundaries =>
      (⟨subject, boundaries⟩ : EvidenceSubjectCoordinates tokens))
    allEvidenceIndexSubjects_nodup
    (fun _ => allEvidenceBoundaryTriples_nodup tokens)
  intro left right leftBoundaries rightBoundaries equal
  have owner : left = right :=
    congrArg EvidenceSubjectCoordinates.subject equal
  subst right
  have item : leftBoundaries = rightBoundaries :=
    congrArg EvidenceSubjectCoordinates.boundaries equal
  subst rightBoundaries
  rfl

private def EvidenceIndexAddress.ofCoordinates
    {tokens : List Token} (kind : EvidenceIndexKind)
    (coordinates : EvidenceSubjectCoordinates tokens) :
    EvidenceIndexAddress tokens := {
  kind := kind
  subject := coordinates.subject
  contextStart := coordinates.boundaries.contextStart
  siteCursor := coordinates.boundaries.pair.siteCursor
  resultEnd := coordinates.boundaries.pair.resultEnd
}

private def canonicalEvidenceIndexAddresses (tokens : List Token) :
    List (EvidenceIndexAddress tokens) :=
  allEvidenceIndexKinds.flatMap fun kind =>
    (allEvidenceSubjectCoordinates tokens).map
      (EvidenceIndexAddress.ofCoordinates kind)

private theorem allEvidenceIndexKinds_nodup :
    allEvidenceIndexKinds.Nodup := by
  decide

private theorem canonicalEvidenceIndexAddresses_nodup
    (tokens : List Token) :
    (canonicalEvidenceIndexAddresses tokens).Nodup := by
  apply dependentEnumeration_nodup
    allEvidenceIndexKinds
    (fun _ => allEvidenceSubjectCoordinates tokens)
    EvidenceIndexAddress.ofCoordinates
    allEvidenceIndexKinds_nodup
    (fun _ => allEvidenceSubjectCoordinates_nodup tokens)
  intro left right leftCoordinates rightCoordinates equal
  have owner : left = right := congrArg EvidenceIndexAddress.kind equal
  subst right
  have subject : leftCoordinates.subject = rightCoordinates.subject :=
    congrArg EvidenceIndexAddress.subject equal
  have contextStart : leftCoordinates.boundaries.contextStart =
      rightCoordinates.boundaries.contextStart :=
    congrArg EvidenceIndexAddress.contextStart equal
  have siteCursor : leftCoordinates.boundaries.pair.siteCursor =
      rightCoordinates.boundaries.pair.siteCursor :=
    congrArg EvidenceIndexAddress.siteCursor equal
  have resultEnd : leftCoordinates.boundaries.pair.resultEnd =
      rightCoordinates.boundaries.pair.resultEnd :=
    congrArg EvidenceIndexAddress.resultEnd equal
  have pair : leftCoordinates.boundaries.pair =
      rightCoordinates.boundaries.pair :=
    EvidenceBoundaryPair.eq_of_fields siteCursor resultEnd
  have boundaries : leftCoordinates.boundaries =
      rightCoordinates.boundaries :=
    EvidenceBoundaryTriple.eq_of_fields contextStart pair
  have coordinates : leftCoordinates = rightCoordinates :=
    EvidenceSubjectCoordinates.eq_of_fields subject boundaries
  subst rightCoordinates
  rfl

private theorem allEvidenceIndexAddresses_eq_canonical
    (tokens : List Token) :
    allEvidenceIndexAddresses tokens =
      canonicalEvidenceIndexAddresses tokens := by
  simp only [allEvidenceIndexAddresses, canonicalEvidenceIndexAddresses,
    allEvidenceSubjectCoordinates, allEvidenceBoundaryTriples,
    allEvidenceBoundaryPairs, EvidenceIndexAddress.ofCoordinates,
    List.map_flatMap, List.map_map, Function.comp_def]

private theorem allEvidenceIndexAddresses_nodup (tokens : List Token) :
    (allEvidenceIndexAddresses tokens).Nodup := by
  rw [allEvidenceIndexAddresses_eq_canonical]
  exact canonicalEvidenceIndexAddresses_nodup tokens

private def EvidenceEntriesAddressNodup
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens)) :
    Prop :=
  (entries.map PhaseAEvidenceEntry.address).Nodup

private def EvidenceEntriesCover
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens)) :
    Prop :=
  ∀ address, ∃ selected,
    ({ address := address, selected := selected } :
      PhaseAEvidenceEntry tokens) ∈ entries

private def FullyMaterializedEvidenceEntries
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens)) :
    Prop :=
  EvidenceEntriesAddressNodup entries ∧ EvidenceEntriesCover entries

private def canonicalEvidenceEntries
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (phaseA : PhaseAOpen file tokens) :
    List (PhaseAEvidenceEntry tokens) :=
  (allEvidenceIndexAddresses tokens).map fun address => {
    address := address
    selected := evaluate phaseA address
  }

private theorem canonicalEvidenceEntries_fullyMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (phaseA : PhaseAOpen file tokens) :
    FullyMaterializedEvidenceEntries
      (canonicalEvidenceEntries evaluate phaseA) := by
  constructor
  · unfold EvidenceEntriesAddressNodup canonicalEvidenceEntries
    rw [List.map_map]
    change (List.map id (allEvidenceIndexAddresses tokens)).Nodup
    rw [List.map_id]
    exact allEvidenceIndexAddresses_nodup tokens
  · intro address
    refine ⟨evaluate phaseA address, ?_⟩
    rw [canonicalEvidenceEntries, List.mem_map]
    exact ⟨address, allEvidenceIndexAddresses_complete address, rfl⟩

private theorem evidenceIndexKind_beq_self (kind : EvidenceIndexKind) :
    (kind == kind) = true := by cases kind <;> rfl

private theorem evidenceSubject_beq_self
    (subject : PriorityGuardId ⊕ GrammarRuleId) :
    (subject == subject) = true := by
  cases subject with
  | inl guard => cases guard <;> rfl
  | inr rule => cases rule <;> rfl

private theorem phaseAEvidenceAddressEqBool_self
    {tokens : List Token} (address : EvidenceIndexAddress tokens) :
    phaseAEvidenceAddressEqBool address address = true := by
  cases address
  simp [phaseAEvidenceAddressEqBool, evidenceIndexKind_beq_self,
    evidenceSubject_beq_self]

private theorem phaseAEvidenceEntryAt?_some_of_mem
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    {address : EvidenceIndexAddress tokens} {selected : Bool}
    (member : ({ address := address, selected := selected } :
      PhaseAEvidenceEntry tokens) ∈ entries) :
    ∃ observed, phaseAEvidenceEntryAt? entries address = some observed := by
  induction entries with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact ⟨selected, by
          simp [phaseAEvidenceEntryAt?, phaseAEvidenceAddressEqBool_self]⟩
      · rw [phaseAEvidenceEntryAt?]
        split
        · exact ⟨head.selected, rfl⟩
        · exact induction member

private theorem phaseAEvidenceEntryAt?_total_of_fullyMaterialized
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (address : EvidenceIndexAddress tokens) :
    ∃ selected, phaseAEvidenceEntryAt? entries address = some selected := by
  obtain ⟨selected, member⟩ := complete.2 address
  exact phaseAEvidenceEntryAt?_some_of_mem entries member

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem phaseB_runMappedPrimitive?_payload
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    {result : CountedState tokens after}
    (selected : runMappedPrimitive? current address transition = some result) :
    result.payload = transition current.payload := by
  unfold runMappedPrimitive? at selected
  split at selected
  · cases selected
    rfl
  · contradiction

private theorem materializePhaseAIndexes?_payload
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens) :
    ∀ addresses
      (current result : CountedState tokens (PhaseAIndexed file tokens)),
      materializePhaseAIndexes? evaluate addresses current = some result →
        result.payload.phaseA = current.payload.phaseA ∧
        result.payload.entries = current.payload.entries ++
          addresses.map fun address => ({
            address := address
            selected := evaluate current.payload.phaseA address
          } : PhaseAEvidenceEntry tokens) := by
  intro addresses
  induction addresses with
  | nil =>
      intro current result selected
      rw [materializePhaseAIndexes?] at selected
      cases selected
      exact ⟨rfl, by simp⟩
  | cons address rest induction =>
      intro current result selected
      rw [materializePhaseAIndexes?] at selected
      cases charged : runMappedPrimitive? current
          (UnitAddress.evidenceIndex address)
          (fun (state : PhaseAIndexed file tokens) => ({
            state with entries := state.entries ++ [{
              address := address
              selected := evaluate state.phaseA address
            }]
          } : PhaseAIndexed file tokens)) with
      | none => simp [charged] at selected
      | some next =>
          rw [charged] at selected
          have nextPayload := phaseB_runMappedPrimitive?_payload current
            (UnitAddress.evidenceIndex address)
            (fun (state : PhaseAIndexed file tokens) => ({
              state with entries := state.entries ++ [{
                address := address
                selected := evaluate state.phaseA address
              }]
            } : PhaseAIndexed file tokens)) charged
          rcases induction next result selected with
            ⟨phaseSame, entriesSame⟩
          have nextPhase :
              next.payload.phaseA = current.payload.phaseA := by
            rw [nextPayload]
          have nextEntries : next.payload.entries =
              current.payload.entries ++ [{
                address := address
                selected := evaluate current.payload.phaseA address
              }] := by
            rw [nextPayload]
          constructor
          · exact phaseSame.trans nextPhase
          · rw [entriesSame, nextEntries, nextPhase]
            simp [List.append_assoc]

private theorem materializeAllPhaseAIndexes?_entries_eq_canonical
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : materializePhaseAIndexes? evaluate
      (allEvidenceIndexAddresses tokens) (beginPhaseAIndexing current) =
        some result) :
    result.payload.entries =
      canonicalEvidenceEntries evaluate current.payload := by
  have shape := materializePhaseAIndexes?_payload evaluate
    (allEvidenceIndexAddresses tokens) (beginPhaseAIndexing current)
    result selected
  simpa [beginPhaseAIndexing, canonicalEvidenceEntries] using shape.2

private theorem materializeAllPhaseAIndexes?_fullyMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : materializePhaseAIndexes? evaluate
      (allEvidenceIndexAddresses tokens) (beginPhaseAIndexing current) =
        some result) :
    FullyMaterializedEvidenceEntries result.payload.entries := by
  rw [materializeAllPhaseAIndexes?_entries_eq_canonical
    evaluate current result selected]
  exact canonicalEvidenceEntries_fullyMaterialized evaluate current.payload

private theorem indexSaturatedPhaseAWith?_fullyMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : indexSaturatedPhaseAWith? evaluate current = some result) :
    FullyMaterializedEvidenceEntries result.payload.entries := by
  unfold indexSaturatedPhaseAWith? at selected
  split at selected
  next itemsDone =>
    split at selected
    next edgesDone =>
      split at selected
      next saturated =>
        exact materializeAllPhaseAIndexes?_fullyMaterialized
          evaluate current result selected
      next notSaturated => contradiction
    next edgesRemain => contradiction
  next itemsRemain => contradiction

private theorem indexSaturatedPhaseACanonicalWith?_fullyMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : indexSaturatedPhaseACanonicalWith? evaluate current =
      some result) :
    FullyMaterializedEvidenceEntries result.payload.entries := by
  unfold indexSaturatedPhaseACanonicalWith? at selected
  split at selected
  next sameMembers =>
    exact indexSaturatedPhaseAWith?_fullyMaterialized evaluate
      (normalizePhaseARawItems current sameMembers) result selected
  next differentMembers => contradiction

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem phaseBReadIndex?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (kind : EvidenceIndexKind)
    (subject : PriorityGuardId ⊕ GrammarRuleId)
    (contextStart siteCursor resultEnd : Boundary tokens) :
    ∃ selected, phaseBReadIndex? entries kind subject
      contextStart siteCursor resultEnd = some selected := by
  exact phaseAEvidenceEntryAt?_total_of_fullyMaterialized entries complete {
    kind := kind
    subject := subject
    contextStart := contextStart
    siteCursor := siteCursor
    resultEnd := resultEnd
  }

private theorem phaseBAllReads?_total :
    ∀ reads : List (Option Bool),
      (∀ read, read ∈ reads → ∃ selected, read = some selected) →
      ∃ selected, phaseBAllReads? reads = some selected
  | [], _ => ⟨true, rfl⟩
  | read :: rest, total => by
      obtain ⟨head, headSelected⟩ := total read (by simp)
      obtain ⟨tail, tailSelected⟩ := phaseBAllReads?_total rest
        (by
          intro candidate member
          exact total candidate (by simp [member]))
      exact ⟨head && tail, by
        simp [phaseBAllReads?, headSelected, tailSelected]⟩

private theorem phaseBAnyReads?_total :
    ∀ reads : List (Option Bool),
      (∀ read, read ∈ reads → ∃ selected, read = some selected) →
      ∃ selected, phaseBAnyReads? reads = some selected
  | [], _ => ⟨false, rfl⟩
  | read :: rest, total => by
      obtain ⟨head, headSelected⟩ := total read (by simp)
      obtain ⟨tail, tailSelected⟩ := phaseBAnyReads?_total rest
        (by
          intro candidate member
          exact total candidate (by simp [member]))
      exact ⟨head || tail, by
        simp [phaseBAnyReads?, headSelected, tailSelected]⟩

private theorem phaseBWithBoundary?_total
    (tokens : List Token) (coordinate : Nat)
    (read : Boundary tokens → Option Bool)
    (total : ∀ boundary, ∃ selected, read boundary = some selected) :
    ∃ selected, phaseBWithBoundary? tokens coordinate read = some selected := by
  unfold phaseBWithBoundary?
  cases boundary : phaseABoundaryAt? tokens coordinate with
  | none => exact ⟨false, rfl⟩
  | some value => exact total value

private theorem phaseBG01Positive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG01Positive? entries key = some selected := by
  unfold phaseBG01Positive?
  apply phaseBWithBoundary?_total
  intro openCursor
  apply phaseBWithBoundary?_total
  intro expressionStart
  apply phaseBAllReads?_total
  intro outer outerMember
  simp only [List.mem_singleton] at outerMember
  subst outer
  apply phaseBAnyReads?_total
  intro candidate candidateMember
  rw [List.mem_map] at candidateMember
  rcases candidateMember with ⟨closeCursor, _, rfl⟩
  apply phaseBAllReads?_total
  intro read readMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at readMember
  rcases readMember with rfl | rfl | rfl
  · exact phaseBReadIndex?_total entries complete .terminalWindow
      (.inl .G01_statementIf) key.siteCursor closeCursor closeCursor
  · exact phaseBReadIndex?_total entries complete .delimiterOrRegion
      (.inl .G01_statementIf) openCursor closeCursor closeCursor
  · exact phaseBReadIndex?_total entries complete .greatestEnd
      (.inr .expression) expressionStart closeCursor closeCursor

private theorem phaseBG02Observations?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG02Observations? entries key = some selected := by
  obtain ⟨header, headerSelected⟩ := phaseBReadIndex?_total entries complete
    .delimiterOrRegion (.inl .G02_matchArmBoundary)
    key.contextStart key.siteCursor key.siteCursor
  change phaseBReadDelimiterGuard? entries .G02_matchArmBoundary
    key.contextStart key.siteCursor key.siteCursor = some header
    at headerSelected
  obtain ⟨pipe, pipeSelected⟩ := phaseBWithBoundary?_total tokens
    (key.siteCursor.val + 1)
    (fun after => phaseBReadTerminalGuard? entries .G02_matchArmBoundary
      key.contextStart key.siteCursor after)
    (fun after => phaseBReadIndex?_total entries complete
      .terminalWindow (.inl .G02_matchArmBoundary)
      key.contextStart key.siteCursor after)
  exact ⟨(header, pipe), by
    simp [phaseBG02Observations?, headerSelected, pipeSelected]⟩

private theorem phaseBComptimeAtSitePositive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected,
      phaseBComptimeAtSitePositive? entries key = some selected := by
  unfold phaseBComptimeAtSitePositive?
  apply phaseBWithBoundary?_total
  intro after
  exact phaseBReadIndex?_total entries complete .terminalWindow
    (.inl key.guard) key.contextStart key.siteCursor after

private theorem phaseBG06Positive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG06Positive? entries key = some selected := by
  unfold phaseBG06Positive?
  apply phaseBWithBoundary?_total
  intro expressionStart
  apply phaseBAllReads?_total
  intro read readMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at readMember
  rcases readMember with rfl | rfl
  · exact phaseBReadIndex?_total entries complete .terminalWindow
      (.inl .G06_patternComptime) key.contextStart key.siteCursor
      expressionStart
  · apply phaseBAnyReads?_total
    intro candidate candidateMember
    rw [List.mem_map] at candidateMember
    rcases candidateMember with ⟨limit, _, rfl⟩
    apply phaseBAllReads?_total
    intro inner innerMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at innerMember
    rcases innerMember with rfl | rfl
    · exact phaseBReadIndex?_total entries complete .delimiterOrRegion
        (.inl .G06_patternComptime) expressionStart limit limit
    · exact phaseBReadIndex?_total entries complete .greatestEnd
        (.inr .expression) expressionStart limit limit

private theorem phaseBG07Positive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG07Positive? entries key = some selected := by
  unfold phaseBG07Positive?
  apply phaseBWithBoundary?_total
  intro after
  apply phaseBAllReads?_total
  intro read readMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at readMember
  rcases readMember with rfl | rfl
  · exact phaseBReadIndex?_total entries complete .exactSlice
      (.inl .G07_leadingDotArguments) key.contextStart key.siteCursor
      key.siteCursor
  · exact phaseBReadIndex?_total entries complete .terminalWindow
      (.inl .G07_leadingDotArguments) key.contextStart key.siteCursor after

private theorem phaseBG08Positive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG08Positive? entries key = some selected := by
  unfold phaseBG08Positive?
  apply phaseBAnyReads?_total
  intro candidate candidateMember
  rw [List.mem_map] at candidateMember
  rcases candidateMember with ⟨regionEnd, _, rfl⟩
  apply phaseBAllReads?_total
  intro read readMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at readMember
  rcases readMember with rfl | rfl
  · exact phaseBReadIndex?_total entries complete .delimiterOrRegion
      (.inl .G08_terminalExpression) key.contextStart key.siteCursor regionEnd
  · exact phaseBReadIndex?_total entries complete .greatestEnd
      (.inr .expression) key.siteCursor regionEnd regionEnd

private theorem phaseBG09Positive?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ selected, phaseBG09Positive? entries key = some selected := by
  unfold phaseBG09Positive?
  apply phaseBAnyReads?_total
  intro candidate candidateMember
  rw [List.mem_map] at candidateMember
  rcases candidateMember with ⟨arrowCursor, _, rfl⟩
  apply phaseBAllReads?_total
  intro read readMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at readMember
  rcases readMember with rfl | rfl
  · exact phaseBReadIndex?_total entries complete .terminalWindow
      (.inl .G09_genericContext) key.contextStart key.siteCursor arrowCursor
  · exact phaseBReadIndex?_total entries complete .greatestEnd
      (.inr .predicateList) key.siteCursor arrowCursor arrowCursor

private theorem phaseBGuardDecisionFromIndexes?_total
    {tokens : List Token} (entries : List (PhaseAEvidenceEntry tokens))
    (complete : FullyMaterializedEvidenceEntries entries)
    (key : GuardInstanceKey tokens) :
    ∃ decision, phaseBGuardDecisionFromIndexes? entries key = some decision := by
  cases guard : key.guard <;>
    simp only [phaseBGuardDecisionFromIndexes?, guard]
  · obtain ⟨selected, equal⟩ := phaseBG01Positive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ := phaseBG02Observations?_total entries complete key
    rcases selected with ⟨header, pipe⟩
    rw [equal]
    exact ⟨if header then .positive else if pipe then .negative else .neutral,
      rfl⟩
  · obtain ⟨selected, equal⟩ :=
      phaseBComptimeAtSitePositive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ :=
      phaseBComptimeAtSitePositive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ :=
      phaseBComptimeAtSitePositive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ := phaseBG06Positive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ := phaseBG07Positive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ := phaseBG08Positive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩
  · obtain ⟨selected, equal⟩ := phaseBG09Positive?_total entries complete key
    rw [equal]
    exact ⟨if selected then .positive else .negative, rfl⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseBFinalizationInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (state : PhaseBIndexed file tokens) : Prop :=
  (∀ key, key ∈ state.phaseB.remaining ∨
      key ∈ state.phaseB.finalizedRev) ∧
    (∀ key, key ∈ state.phaseB.finalizedRev →
      ∃ decision, state.phaseB.cells key = some (.final decision))

private theorem phaseB_chargeAddresses?_payload
    {tokens : List Token} {state : Type}
    (current : CountedState tokens state) :
    ∀ addresses (result : CountedState tokens state),
      chargeAddresses? current addresses = some result →
        result.payload = current.payload := by
  intro addresses
  induction addresses generalizing current with
  | nil =>
      intro result selected
      cases selected
      rfl
  | cons address rest induction =>
      intro result selected
      rw [chargeAddresses?] at selected
      cases charged : runMappedPrimitive? current address id with
      | none => simp [charged] at selected
      | some next =>
          rw [charged] at selected
          exact (induction next result selected).trans
            (phaseB_runMappedPrimitive?_payload current address id charged)

private theorem enterPhaseB?_initializes
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseBOpen file tokens))
    (selected : enterPhaseB? current = some result) :
    result.payload.remaining = allGuardInstanceKeys tokens ∧
      result.payload.finalizedRev = [] := by
  unfold enterPhaseB? at selected
  split at selected
  next itemsDone =>
    split at selected
    next edgesDone =>
      split at selected
      next saturated =>
        have payload := phaseB_runMappedPrimitive?_payload current
          (.phase .sealAEnterB) (fun state => ({
            phaseA := ⟨state.rawItems, state.rawEdges⟩
            cells := fun _ => none
            remaining := allGuardInstanceKeys tokens
            finalizedRev := []
          } : PhaseBOpen file tokens)) selected
        rw [payload]
        exact ⟨rfl, rfl⟩
      next notSaturated => contradiction
    next edgesRemain => contradiction
  next itemsRemain => contradiction

private theorem enterIndexedPhaseB?_invariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBIndexed file tokens))
    (selected : enterIndexedPhaseB? current = some result) :
    PhaseBFinalizationInvariant result.payload := by
  unfold enterIndexedPhaseB? at selected
  cases entered : enterPhaseB? {
      payload := current.payload.phaseA
      counter := current.counter
    } with
  | none => simp [entered] at selected
  | some phaseB =>
      rw [entered] at selected
      cases selected
      have initialized := enterPhaseB?_initializes {
        payload := current.payload.phaseA
        counter := current.counter
      } phaseB entered
      constructor
      · intro key
        left
        rw [initialized.1]
        exact allGuardInstanceKeys_complete key
      · simp [initialized.2]

private theorem finalizeNextIndexedGuard?_shape
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseBIndexed file tokens))
    (selected : finalizeNextIndexedGuard? current = some result) :
    ∃ key rest decision,
      current.payload.phaseB.remaining = key :: rest ∧
      result.payload.phaseB.remaining = rest ∧
      result.payload.phaseB.finalizedRev =
        key :: current.payload.phaseB.finalizedRev ∧
      ∀ candidate, result.payload.phaseB.cells candidate =
        if candidate = key then some (.final decision)
        else current.payload.phaseB.cells candidate := by
  unfold finalizeNextIndexedGuard? at selected
  cases remaining : current.payload.phaseB.remaining with
  | nil => simp [remaining] at selected
  | cons key rest =>
      simp only [remaining] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨afterInitialize, initialized,
        afterLookups, charged, decision, decided, finalSelected⟩
      have initializePayload := phaseB_runMappedPrimitive?_payload current
        (.guardFinalize .initializeUndecided key)
        (fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            state.phaseB with
            cells := fun candidate =>
              if candidate = key then some .undecided
              else state.phaseB.cells candidate
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)) initialized
      have lookupPayload := phaseB_chargeAddresses?_payload afterInitialize
        (preFinalGuardSlots.map fun slot => .guardFinalize slot key)
        afterLookups charged
      have finalPayload := phaseB_runMappedPrimitive?_payload afterLookups
        (.guardFinalize .writeFinalDecision key)
        (fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            phaseA := state.phaseB.phaseA
            cells := fun candidate =>
              if candidate = key then some (.final decision)
              else state.phaseB.cells candidate
            remaining := rest
            finalizedRev := key :: state.phaseB.finalizedRev
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)) finalSelected
      refine ⟨key, rest, decision, rfl, ?_, ?_, ?_⟩
      · rw [finalPayload]
      · rw [finalPayload, lookupPayload, initializePayload]
      · intro candidate
        rw [finalPayload, lookupPayload, initializePayload]
        by_cases same : candidate = key
        · simp [same]
        · simp [same]

private theorem finalizeNextIndexedGuard?_invariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseBIndexed file tokens))
    (invariant : PhaseBFinalizationInvariant current.payload)
    (selected : finalizeNextIndexedGuard? current = some result) :
    PhaseBFinalizationInvariant result.payload := by
  obtain ⟨key, rest, decision, currentRemaining, resultRemaining,
    resultFinalized, resultCells⟩ :=
    finalizeNextIndexedGuard?_shape current result selected
  constructor
  · intro candidate
    rcases invariant.1 candidate with remaining | finalized
    · rw [currentRemaining, List.mem_cons] at remaining
      rcases remaining with equal | remaining
      · right
        rw [resultFinalized, List.mem_cons]
        exact Or.inl equal
      · left
        simpa [resultRemaining] using remaining
    · right
      rw [resultFinalized, List.mem_cons]
      exact Or.inr finalized
  · intro candidate member
    rw [resultFinalized, List.mem_cons] at member
    rcases member with equal | oldMember
    · subst candidate
      exact ⟨decision, by simp [resultCells]⟩
    · by_cases same : candidate = key
      · subst candidate
        exact ⟨decision, by simp [resultCells]⟩
      · obtain ⟨oldDecision, oldFinal⟩ := invariant.2 candidate oldMember
        exact ⟨oldDecision, by simp [resultCells, same, oldFinal]⟩

private theorem runIndexedPhaseB?_invariant
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ fuel
      (current result : CountedState tokens (PhaseBIndexed file tokens)),
      PhaseBFinalizationInvariant current.payload →
      runIndexedPhaseB? fuel current = some result →
        PhaseBFinalizationInvariant result.payload := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      split at selected
      · cases selected
        exact invariant
      · contradiction
  | succ fuel induction =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      cases remaining : current.payload.phaseB.remaining with
      | nil =>
          simp only [remaining] at selected
          cases selected
          exact invariant
      | cons key rest =>
          simp only [remaining] at selected
          cases finalized : finalizeNextIndexedGuard? current with
          | none => simp [finalized] at selected
          | some next =>
              rw [finalized] at selected
              exact induction next result
                (finalizeNextIndexedGuard?_invariant
                  current next invariant finalized) selected

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem sealIndexedPhaseB?_allFinal
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (invariant : PhaseBFinalizationInvariant current.payload)
    (selected : sealIndexedPhaseB? current = some result) :
    AllGuardsFinal result.payload.memo := by
  unfold sealIndexedPhaseB? sealPhaseB? at selected
  cases remaining : current.payload.phaseB.remaining with
  | cons key rest => simp [remaining] at selected
  | nil =>
      simp only [remaining] at selected
      have payload := phaseB_runMappedPrimitive?_payload {
        payload := current.payload.phaseB
        counter := current.counter
      } (.phase .sealBEnterC) (fun state => ({
        phaseA := state.phaseA
        memo := fun key =>
          match state.cells key with
          | some value => value
          | none => .undecided
        finalizedRev := state.finalizedRev
      } : PhaseBSealed file tokens)) selected
      intro lookupKey
      have finalized :
          lookupKey ∈ current.payload.phaseB.finalizedRev := by
        rcases invariant.1 lookupKey with pending | finalized
        · rw [remaining] at pending
          contradiction
        · exact finalized
      obtain ⟨decision, cell⟩ := invariant.2 lookupKey finalized
      refine ⟨decision, ?_⟩
      rw [payload]
      simp [cell]

private theorem executeIndexedPhaseB?_allFinal
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (selected : executeIndexedPhaseB? current = some result) :
    AllGuardsFinal result.payload.memo := by
  unfold executeIndexedPhaseB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enterSelected,
    finalized, runSelected, sealSelected⟩
  have enteredInvariant :=
    enterIndexedPhaseB?_invariant current entered enterSelected
  have finalInvariant := runIndexedPhaseB?_invariant
    (allGuardInstanceKeys tokens).length entered finalized
    enteredInvariant runSelected
  exact sealIndexedPhaseB?_allFinal finalized result
    finalInvariant sealSelected

private theorem executeObservedPhaseAB?_allFinal
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseBSealed file tokens))
    (selected : executeObservedPhaseAB? file tokens owned = some result) :
    AllGuardsFinal result.payload.memo := by
  unfold executeObservedPhaseAB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseA, phaseASelected,
    indexed, indexedSelected, phaseBSelected⟩
  exact executeIndexedPhaseB?_allFinal indexed result phaseBSelected

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def phaseBTotalityWitnessPhaseA
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAOpen file tokens := {
  rawItems := rawSaturation tokens
  itemQueue := []
  rawEdges := []
  edgeQueue := []
}

private def phaseBTotalityWitnessEvaluator
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAIndexEvaluator file tokens := fun _ _ => false

/-- The current carrier admits a fully materialized saturated state whose
ledger has already consumed the next phase-transition address. -/
private def phaseBTotalityCollisionInput
    (file : WorkspaceFile) (tokens : List Token) :
    CountedState tokens (PhaseAIndexed file tokens) := {
  payload := {
    phaseA := phaseBTotalityWitnessPhaseA file tokens
    entries := canonicalEvidenceEntries
      (phaseBTotalityWitnessEvaluator file tokens)
      (phaseBTotalityWitnessPhaseA file tokens)
  }
  counter := {
    usedRev := [.phase .sealAEnterB]
    unique := by simp
  }
}

private theorem phaseBTotalityCollisionInput_fullyMaterialized
    (file : WorkspaceFile) (tokens : List Token) :
    FullyMaterializedEvidenceEntries
      (phaseBTotalityCollisionInput file tokens).payload.entries := by
  exact canonicalEvidenceEntries_fullyMaterialized
    (phaseBTotalityWitnessEvaluator file tokens)
    (phaseBTotalityWitnessPhaseA file tokens)

private theorem executeIndexedPhaseB?_not_total_from_carrier
    (file : WorkspaceFile) (tokens : List Token) :
    executeIndexedPhaseB? (phaseBTotalityCollisionInput file tokens) = none := by
  simp [executeIndexedPhaseB?, enterIndexedPhaseB?, enterPhaseB?,
    phaseBTotalityCollisionInput, phaseBTotalityWitnessPhaseA,
    runMappedPrimitive?]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def phaseAReservedAddress {tokens : List Token} :
    UnitAddress tokens → Prop
  | .phase .sealAEnterB => True
  | .phase .sealBEnterC => True
  | .guardFinalize _ _ => True
  | .production _ => True
  | .guardWitness _ _ => True
  | .linear _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | .prediction _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | .cubic .U01_evidenceIndex _ => True
  | .cubic _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | _ => False

private def PhaseAReservedFresh {tokens : List Token}
    (counter : Counter tokens) : Prop :=
  ∀ address, phaseAReservedAddress address →
    address ∉ counter.usedRev

private theorem runMappedPrimitive?_reservedFresh
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (invariant : PhaseAReservedFresh current.counter)
    (available : ¬ phaseAReservedAddress address)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseAReservedFresh result.counter := by
  unfold runMappedPrimitive? at selected
  split at selected
  next fresh =>
    cases selected
    intro candidate reserved member
    simp only [Counter.charge, List.mem_cons] at member
    rcases member with equal | old
    · exact available (equal ▸ reserved)
    · exact invariant candidate reserved old
  next collision => contradiction

private theorem runMappedPrimitive?_usedRev
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition = some result) :
    result.counter.usedRev = address :: current.counter.usedRev := by
  unfold runMappedPrimitive? at selected
  split at selected
  next fresh =>
    cases selected
    rfl
  next collision => contradiction

private theorem beginPhaseA_reservedFresh
    (file : WorkspaceFile) (tokens : List Token) :
    PhaseAReservedFresh (beginPhaseA file tokens).counter := by
  intro address reserved member
  simp only [beginPhaseA, Counter.charge, Counter.empty,
    List.mem_cons, List.not_mem_nil, or_false] at member
  subst address
  exact reserved

private theorem insertRawItem?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (source : RawItemInsertSource) (item : DottedItem tokens)
    (invariant : PhaseAReservedFresh current.counter)
    (selected : insertRawItem? current source item = some result) :
    PhaseAReservedFresh result.counter := by
  unfold insertRawItem? at selected
  split at selected
  · cases selected
    exact invariant
  · apply runMappedPrimitive?_reservedFresh current _ _ invariant _
      result selected
    cases source <;> simp [phaseAReservedAddress, rawLinearKey]

private theorem insertRawEdge?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (edge : PackedEdge file tokens)
    (invariant : PhaseAReservedFresh current.counter)
    (selected : insertRawEdge? current edge = some result) :
    PhaseAReservedFresh result.counter := by
  unfold insertRawEdge? at selected
  split at selected
  · cases selected
    exact invariant
  · apply runMappedPrimitive?_reservedFresh current _ _ invariant _
      result selected
    cases edge.val <;> simp [phaseAReservedAddress,
      rawLinearKey, rawCompletionKey]

private theorem dequeueRawItem?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : DottedItem tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseAReservedFresh current.counter)
    (selected : dequeueRawItem? current = some result) :
    PhaseAReservedFresh result.2.counter := by
  unfold dequeueRawItem? at selected
  cases queue : current.payload.itemQueue with
  | nil => simp [queue] at selected
  | cons item rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, stepped, output⟩
      simp only [pure, Option.some.injEq] at output
      subst result
      exact runMappedPrimitive?_reservedFresh current _ _ invariant
        (by simp [phaseAReservedAddress, rawLinearKey]) next stepped

private theorem dequeueRawEdge?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : PackedEdge file tokens ×
      CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseAReservedFresh current.counter)
    (selected : dequeueRawEdge? current = some result) :
    PhaseAReservedFresh result.2.counter := by
  unfold dequeueRawEdge? at selected
  cases queue : current.payload.edgeQueue with
  | nil => simp [queue] at selected
  | cons edge rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, stepped, output⟩
      simp only [pure, Option.some.injEq] at output
      subst result
      apply runMappedPrimitive?_reservedFresh current _ _ invariant _
        next stepped
      cases edge.val <;> simp [phaseAReservedAddress,
        rawLinearKey, rawCompletionKey]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem insertRawSeeds?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ items
      (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAReservedFresh current.counter →
      insertRawSeeds? items current = some result →
      PhaseAReservedFresh result.counter := by
  intro items
  induction items with
  | nil =>
      intro current result invariant selected
      cases selected
      exact invariant
  | cons item rest induction =>
      intro current result invariant selected
      rw [insertRawSeeds?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, inserted, continued⟩
      exact induction next result
        (insertRawItem?_reservedFresh current next .seedOrPrediction item
          invariant inserted) continued

private theorem attemptPrediction?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting : DottedItem tokens) (predicted : ProductionId)
    (invariant : PhaseAReservedFresh current.counter)
    (selected : attemptPrediction? current waiting predicted = some result) :
    PhaseAReservedFresh result.counter := by
  unfold attemptPrediction? at selected
  cases prediction : predictedItem? waiting predicted with
  | none =>
      simp only [prediction] at selected
      cases selected
      exact invariant
  | some item =>
      simp only [prediction, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨attempted, attemptedEq, inserted⟩
      have attemptedInvariant := runMappedPrimitive?_reservedFresh
        current _ id invariant
          (by simp [phaseAReservedAddress, rawPredictionKey])
        attempted attemptedEq
      exact insertRawItem?_reservedFresh attempted result
        .seedOrPrediction item attemptedInvariant inserted

private theorem attemptPredictions?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : DottedItem tokens) :
    ∀ candidates
      (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAReservedFresh current.counter →
      attemptPredictions? waiting candidates current = some result →
      PhaseAReservedFresh result.counter := by
  intro candidates
  induction candidates with
  | nil =>
      intro current result invariant selected
      cases selected
      exact invariant
  | cons candidate rest induction =>
      intro current result invariant selected
      rw [attemptPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, attempted, continued⟩
      exact induction next result
        (attemptPrediction?_reservedFresh current next waiting candidate
          invariant attempted) continued

private theorem attemptScan?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (before : DottedItem tokens)
    (invariant : PhaseAReservedFresh current.counter)
    (selected : attemptScan? owned current before = some result) :
    PhaseAReservedFresh result.counter := by
  unfold attemptScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedInvariant := runMappedPrimitive?_reservedFresh
      current _ id invariant
        (by simp [phaseAReservedAddress, rawLinearKey])
      attempted attemptedEq
    cases scan : scannedEdge? owned before with
    | none =>
        simp only [scan] at remainder
        cases remainder
        exact attemptedInvariant
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scan, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        exact insertRawEdge?_reservedFresh withItem result edge
          (insertRawItem?_reservedFresh attempted withItem .scan after
            attemptedInvariant itemEq) edgeEq
  next notApplicable =>
    cases selected
    exact invariant

private theorem attemptCompletion?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (waiting finished : DottedItem tokens)
    (invariant : PhaseAReservedFresh current.counter)
    (selected : attemptCompletion? current waiting finished = some result) :
    PhaseAReservedFresh result.counter := by
  unfold attemptCompletion? at selected
  cases completion : completedEdge? (file := file) waiting finished with
  | none =>
      simp only [completion] at selected
      cases selected
      exact invariant
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completion] at selected
      split at selected
      next attemptedBefore =>
        cases selected
        exact invariant
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with ⟨attempted, attemptedEq,
          withItem, itemEq, edgeEq⟩
        have attemptedInvariant := runMappedPrimitive?_reservedFresh
          current _ id invariant
            (by simp [phaseAReservedAddress, rawCompletionKey])
          attempted attemptedEq
        exact insertRawEdge?_reservedFresh withItem result edge
          (insertRawItem?_reservedFresh attempted withItem .completion after
            attemptedInvariant itemEq) edgeEq

private theorem attemptCompletionsWith?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : DottedItem tokens) :
    ∀ others
      (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAReservedFresh current.counter →
      attemptCompletionsWith? pivot others current = some result →
      PhaseAReservedFresh result.counter := by
  intro others
  induction others with
  | nil =>
      intro current result invariant selected
      cases selected
      exact invariant
  | cons other rest induction =>
      intro current result invariant selected
      rw [attemptCompletionsWith?] at selected
      cases forwardEq : attemptCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardInvariant := attemptCompletion?_reservedFresh
            current forward pivot other invariant forwardEq
          split at selected
          next same =>
            exact induction forward result forwardInvariant selected
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact induction reverse result
                  (attemptCompletion?_reservedFresh forward reverse
                    other pivot forwardInvariant reverseEq) selected

private theorem processRawItem?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) (item : DottedItem tokens)
    (current result : CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseAReservedFresh current.counter)
    (selected : processRawItem? owned item current = some result) :
    PhaseAReservedFresh result.counter := by
  unfold processRawItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨predicted, predictedEq,
    scanned, scannedEq, completionEq⟩
  exact attemptCompletionsWith?_reservedFresh item
    scanned.payload.rawItems scanned result
    (attemptScan?_reservedFresh owned predicted scanned item
      (attemptPredictions?_reservedFresh item allProductionIds
        current predicted invariant predictedEq) scannedEq)
    completionEq

private theorem runPhaseAQueues?_reservedFresh
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result : CountedState tokens (PhaseAOpen file tokens)),
      PhaseAReservedFresh current.counter →
      runPhaseAQueues? owned fuel current = some result →
      PhaseAReservedFresh result.counter := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runPhaseAQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact invariant
  | succ fuel induction =>
      intro current result invariant selected
      rw [runPhaseAQueues?] at selected
      cases items : current.payload.itemQueue with
      | nil =>
          cases edges : current.payload.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact invariant
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueRawEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueRawEdge?_reservedFresh current pair invariant
                      dequeued) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueRawItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨dequeuedItem, afterDequeue⟩
              simp only at selected
              cases processed :
                  processRawItem? owned dequeuedItem afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  exact induction next result
                    (processRawItem?_reservedFresh owned dequeuedItem
                      afterDequeue next
                      (dequeueRawItem?_reservedFresh current
                        (dequeuedItem, afterDequeue) invariant dequeued)
                      processed) selected

private theorem executePhaseA?_reservedFresh
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result) :
    PhaseAReservedFresh result.counter := by
  unfold executePhaseA? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨seeded, seededEq, runEq⟩
  exact runPhaseAQueues?_reservedFresh owned _ seeded result
    (insertRawSeeds?_reservedFresh (rawSeedItems tokens)
      (beginPhaseA file tokens) seeded
      (beginPhaseA_reservedFresh file tokens) seededEq) runEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def phaseBEntryReservedAddress {tokens : List Token} :
    UnitAddress tokens → Prop
  | .phase .sealAEnterB => True
  | .phase .sealBEnterC => True
  | .guardFinalize _ _ => True
  | _ => False

private def PhaseBEntryFresh {tokens : List Token}
    (counter : Counter tokens) : Prop :=
  ∀ address, phaseBEntryReservedAddress address →
    address ∉ counter.usedRev

private theorem PhaseAReservedFresh.phaseBEntryFresh
    {tokens : List Token} {counter : Counter tokens}
    (invariant : PhaseAReservedFresh counter) :
    PhaseBEntryFresh counter := by
  intro address reserved
  apply invariant address
  cases address with
  | phase slot =>
      cases slot <;>
        simp_all [phaseAReservedAddress, phaseBEntryReservedAddress]
  | guardFinalize => simp [phaseAReservedAddress]
  | production => simp_all [phaseBEntryReservedAddress]
  | guardWitness => simp_all [phaseBEntryReservedAddress]
  | linear => simp_all [phaseBEntryReservedAddress]
  | prediction => simp_all [phaseBEntryReservedAddress]
  | cubic kind key =>
      cases kind <;>
        simp_all [phaseBEntryReservedAddress]

private theorem runMappedPrimitive?_phaseBEntryFresh
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (invariant : PhaseBEntryFresh current.counter)
    (available : ¬ phaseBEntryReservedAddress address)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition = some result) :
    PhaseBEntryFresh result.counter := by
  unfold runMappedPrimitive? at selected
  split at selected
  next fresh =>
    cases selected
    intro candidate reserved member
    simp only [Counter.charge, List.mem_cons] at member
    rcases member with equal | old
    · exact available (equal ▸ reserved)
    · exact invariant candidate reserved old
  next collision => contradiction

private theorem materializePhaseAIndexes?_total_owned
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens) :
    ∀ addresses (current : CountedState tokens (PhaseAIndexed file tokens)),
      addresses.Nodup →
      (∀ address, address ∈ addresses →
        UnitAddress.evidenceIndex address ∉ current.counter.usedRev) →
      PhaseBEntryFresh current.counter →
      ∃ result,
        materializePhaseAIndexes? evaluate addresses current = some result ∧
        PhaseBEntryFresh result.counter := by
  intro addresses
  induction addresses with
  | nil =>
      intro current unique pending invariant
      exact ⟨current, rfl, invariant⟩
  | cons address rest induction =>
      intro current unique pending invariant
      rw [List.nodup_cons] at unique
      have fresh := pending address (by simp)
      let transition := fun (state : PhaseAIndexed file tokens) => ({
        state with entries := state.entries ++ [{
          address := address
          selected := evaluate state.phaseA address
        }]
      } : PhaseAIndexed file tokens)
      let next : CountedState tokens (PhaseAIndexed file tokens) := {
        payload := transition current.payload
        counter := current.counter.charge
          (UnitAddress.evidenceIndex address) fresh
      }
      have stepped : runMappedPrimitive? current
          (UnitAddress.evidenceIndex address) transition = some next := by
        simp [runMappedPrimitive?, fresh, next]
      have nextInvariant := runMappedPrimitive?_phaseBEntryFresh
        current (UnitAddress.evidenceIndex address) transition invariant
        (by simp [phaseBEntryReservedAddress, UnitAddress.evidenceIndex])
        next stepped
      have restPending : ∀ candidate, candidate ∈ rest →
          UnitAddress.evidenceIndex candidate ∉ next.counter.usedRev := by
        intro candidate member used
        rw [runMappedPrimitive?_usedRev current
          (UnitAddress.evidenceIndex address) transition next stepped,
          List.mem_cons] at used
        rcases used with equal | old
        · have same := UnitAddress.evidenceIndex_injective equal
          exact unique.1 (same.symm ▸ member)
        · exact pending candidate (by simp [member]) old
      obtain ⟨result, continued, resultInvariant⟩ :=
        induction next unique.2 restPending nextInvariant
      exact ⟨result, by
        rw [materializePhaseAIndexes?, stepped]
        exact continued, resultInvariant⟩

private theorem materializeAllPhaseAIndexes?_total_owned
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (invariant : PhaseAReservedFresh current.counter) :
    ∃ result,
      materializePhaseAIndexes? evaluate
        (allEvidenceIndexAddresses tokens) (beginPhaseAIndexing current) =
          some result ∧
      PhaseBEntryFresh result.counter := by
  apply materializePhaseAIndexes?_total_owned evaluate
    (allEvidenceIndexAddresses tokens) (beginPhaseAIndexing current)
    (allEvidenceIndexAddresses_nodup tokens)
  · intro address member
    exact invariant (UnitAddress.evidenceIndex address)
      (by simp [phaseAReservedAddress, UnitAddress.evidenceIndex,
        evidenceIndexUnitAddress])
  · exact invariant.phaseBEntryFresh

private def PhaseBIndexedReady
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens)) : Prop :=
  current.payload.phaseA.itemQueue = [] ∧
  current.payload.phaseA.edgeQueue = [] ∧
  current.payload.phaseA.rawItems = rawSaturation tokens ∧
  FullyMaterializedEvidenceEntries current.payload.entries ∧
  PhaseBEntryFresh current.counter

private theorem indexSaturatedPhaseACanonicalWith?_total_owned
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (itemsDone : current.payload.itemQueue = [])
    (edgesDone : current.payload.edgeQueue = [])
    (sameMembers : canonicalRawItems tokens current.payload.rawItems =
      canonicalRawItems tokens (rawSaturation tokens))
    (invariant : PhaseAReservedFresh current.counter) :
    ∃ result,
      indexSaturatedPhaseACanonicalWith? evaluate current = some result ∧
      PhaseBIndexedReady result := by
  obtain ⟨result, materialized, resultFresh⟩ :=
    materializeAllPhaseAIndexes?_total_owned evaluate
      (normalizePhaseARawItems current sameMembers) invariant
  have indexed : indexSaturatedPhaseACanonicalWith? evaluate current =
      some result := by
    unfold indexSaturatedPhaseACanonicalWith?
    rw [dif_pos sameMembers]
    unfold indexSaturatedPhaseAWith?
    rw [dif_pos (by simpa [normalizePhaseARawItems] using itemsDone)]
    rw [dif_pos (by simpa [normalizePhaseARawItems] using edgesDone)]
    rw [dif_pos (by rfl)]
    exact materialized
  have shape := materializePhaseAIndexes?_payload evaluate
    (allEvidenceIndexAddresses tokens)
    (beginPhaseAIndexing
      (normalizePhaseARawItems current sameMembers)) result materialized
  refine ⟨result, indexed, ?_, ?_, ?_, ?_, resultFresh⟩
  · rw [shape.1]
    simpa [beginPhaseAIndexing, normalizePhaseARawItems] using itemsDone
  · rw [shape.1]
    simpa [beginPhaseAIndexing, normalizePhaseARawItems] using edgesDone
  · rw [shape.1]
    rfl
  · exact indexSaturatedPhaseACanonicalWith?_fullyMaterialized
      evaluate current result indexed

private theorem executePhaseA?_index_total_owned
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (phaseA : CountedState tokens (PhaseAOpen file tokens))
    (executed : executePhaseA? file tokens owned = some phaseA)
    (sameMembers : canonicalRawItems tokens phaseA.payload.rawItems =
      canonicalRawItems tokens (rawSaturation tokens)) :
    ∃ indexed,
      indexSaturatedPhaseACanonicalWith?
        (phaseAObservationIndexEvaluator owned) phaseA = some indexed ∧
      PhaseBIndexedReady indexed := by
  have invariant := executePhaseA?_reservedFresh
    file tokens owned phaseA executed
  have execution := executed
  unfold executePhaseA? at execution
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at execution
  rcases execution with ⟨seeded, seededEq, runEq⟩
  have queues := runPhaseAQueues?_queues_empty owned
    (chartGBound (tokens.length + 1)) seeded phaseA runEq
  exact indexSaturatedPhaseACanonicalWith?_total_owned
    (phaseAObservationIndexEvaluator owned) phaseA queues.1 queues.2
    sameMembers invariant

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def guardKeysAt
    (tokens : List Token) (guard : PriorityGuardId)
    (contextStart : Boundary tokens) : List (GuardInstanceKey tokens) :=
  (List.finRange (tokens.length + 2)).filterMap fun siteCursor =>
    if ordered : contextStart.val ≤ siteCursor.val then
      some {
        guard := guard
        contextStart := contextStart
        siteCursor := siteCursor
        ordered := ordered
      }
    else
      none

private theorem mem_guardKeysAt_fields
    {tokens : List Token} {guard : PriorityGuardId}
    {contextStart : Boundary tokens} {key : GuardInstanceKey tokens}
    (member : key ∈ guardKeysAt tokens guard contextStart) :
    key.guard = guard ∧ key.contextStart = contextStart := by
  rw [guardKeysAt, List.mem_filterMap] at member
  rcases member with ⟨siteCursor, _, selected⟩
  split at selected
  · simp only [Option.some.injEq] at selected
    subst key
    exact ⟨rfl, rfl⟩
  · contradiction

private theorem guardKeysAt_nodup
    (tokens : List Token) (guard : PriorityGuardId)
    (contextStart : Boundary tokens) :
    (guardKeysAt tokens guard contextStart).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  apply List.Pairwise.filterMap _ _
    (phaseBFinRange_nodup (tokens.length + 2))
  intro left right different leftKey leftEq rightKey rightEq equal
  unfold guardKeysAt at leftEq rightEq
  split at leftEq
  next leftOrdered =>
    simp only [Option.some.injEq] at leftEq
    split at rightEq
    next rightOrdered =>
      simp only [Option.some.injEq] at rightEq
      have leftCursor := congrArg GuardInstanceKey.siteCursor leftEq
      have sameCursor := congrArg GuardInstanceKey.siteCursor equal
      have rightCursor := congrArg GuardInstanceKey.siteCursor rightEq
      exact different (leftCursor.trans (sameCursor.trans rightCursor.symm))
    next => contradiction
  next => contradiction

private def guardKeysFor
    (tokens : List Token) (guard : PriorityGuardId) :
    List (GuardInstanceKey tokens) :=
  (List.finRange (tokens.length + 2)).flatMap fun contextStart =>
    guardKeysAt tokens guard contextStart

private theorem mem_guardKeysFor_guard
    {tokens : List Token} {guard : PriorityGuardId}
    {key : GuardInstanceKey tokens}
    (member : key ∈ guardKeysFor tokens guard) : key.guard = guard := by
  rw [guardKeysFor, List.mem_flatMap] at member
  rcases member with ⟨contextStart, _, keyMember⟩
  exact (mem_guardKeysAt_fields keyMember).1

private theorem guardKeysFor_nodup
    (tokens : List Token) (guard : PriorityGuardId) :
    (guardKeysFor tokens guard).Nodup := by
  unfold guardKeysFor
  have blocks : ∀ contexts : List (Boundary tokens), contexts.Nodup →
      (contexts.flatMap fun contextStart =>
        guardKeysAt tokens guard contextStart).Nodup := by
    intro contexts unique
    induction contexts with
    | nil => simp
    | cons contextStart rest induction =>
        rw [List.nodup_cons] at unique
        simp only [List.flatMap_cons]
        rw [List.nodup_append]
        refine ⟨guardKeysAt_nodup tokens guard contextStart,
          induction unique.2, ?_⟩
        intro left leftMember right rightMember equal
        have leftContext := (mem_guardKeysAt_fields leftMember).2
        rw [List.mem_flatMap] at rightMember
        rcases rightMember with ⟨other, otherMember, keyMember⟩
        have rightContext := (mem_guardKeysAt_fields keyMember).2
        have sameContext : contextStart = other := by
          rw [← leftContext, equal, rightContext]
        exact unique.1 (sameContext ▸ otherMember)
  exact blocks _ (phaseBFinRange_nodup _)

private theorem allPriorityGuardIds_nodup :
    allPriorityGuardIds.Nodup := by decide

private theorem allGuardInstanceKeys_nodup (tokens : List Token) :
    (allGuardInstanceKeys tokens).Nodup := by
  have blocks : ∀ guards : List PriorityGuardId, guards.Nodup →
      (guards.flatMap fun guard => guardKeysFor tokens guard).Nodup := by
    intro guards unique
    induction guards with
    | nil => simp
    | cons guard rest induction =>
        rw [List.nodup_cons] at unique
        simp only [List.flatMap_cons]
        rw [List.nodup_append]
        refine ⟨guardKeysFor_nodup tokens guard,
          induction unique.2, ?_⟩
        intro left leftMember right rightMember equal
        have leftGuard := mem_guardKeysFor_guard leftMember
        rw [List.mem_flatMap] at rightMember
        rcases rightMember with ⟨other, otherMember, keyMember⟩
        have rightGuard := mem_guardKeysFor_guard keyMember
        have sameGuard : guard = other := by
          rw [← leftGuard, equal, rightGuard]
        exact unique.1 (sameGuard ▸ otherMember)
  change (allPriorityGuardIds.flatMap fun guard =>
    guardKeysFor tokens guard).Nodup
  exact blocks allPriorityGuardIds allPriorityGuardIds_nodup

private def PhaseBRunFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens)) : Prop :=
  current.payload.phaseB.remaining.Nodup ∧
  (∀ key, key ∈ current.payload.phaseB.remaining →
    ∀ slot, UnitAddress.guardFinalize slot key ∉
      current.counter.usedRev) ∧
  UnitAddress.phase .sealBEnterC ∉ current.counter.usedRev

private def PhaseBRunnerReady
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens)) : Prop :=
  FullyMaterializedEvidenceEntries current.payload.indexes ∧
    PhaseBRunFresh current

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem enterIndexedPhaseB?_total_ready
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (ready : PhaseBIndexedReady current) :
    ∃ result,
      enterIndexedPhaseB? current = some result ∧
      result.payload.phaseB.remaining = allGuardInstanceKeys tokens ∧
      PhaseBRunnerReady result := by
  let phaseAInput : CountedState tokens (PhaseAOpen file tokens) := {
    payload := current.payload.phaseA
    counter := current.counter
  }
  let transition := fun (state : PhaseAOpen file tokens) => ({
    phaseA := ⟨state.rawItems, state.rawEdges⟩
    cells := fun _ => none
    remaining := allGuardInstanceKeys tokens
    finalizedRev := []
  } : PhaseBOpen file tokens)
  have sealFresh : UnitAddress.phase .sealAEnterB ∉
      phaseAInput.counter.usedRev :=
    ready.2.2.2.2 (.phase .sealAEnterB)
      (by simp [phaseBEntryReservedAddress])
  let entered : CountedState tokens (PhaseBOpen file tokens) := {
    payload := transition phaseAInput.payload
    counter := phaseAInput.counter.charge (.phase .sealAEnterB) sealFresh
  }
  have stepped : runMappedPrimitive? phaseAInput (.phase .sealAEnterB)
      transition = some entered := by
    simp [runMappedPrimitive?, sealFresh, entered]
  have enteredEq : enterPhaseB? phaseAInput = some entered := by
    unfold enterPhaseB?
    rw [dif_pos (by simpa [phaseAInput] using ready.1)]
    rw [dif_pos (by simpa [phaseAInput] using ready.2.1)]
    rw [dif_pos (by simpa [phaseAInput] using ready.2.2.1)]
    exact stepped
  let result : CountedState tokens (PhaseBIndexed file tokens) := {
    payload := ⟨entered.payload, current.payload.entries⟩
    counter := entered.counter
  }
  have selected : enterIndexedPhaseB? current = some result := by
    simp [enterIndexedPhaseB?, phaseAInput, enteredEq, result]
  refine ⟨result, selected, by rfl, ready.2.2.2.1, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [result, entered, transition] using
      allGuardInstanceKeys_nodup tokens
  · intro key member slot used
    simp only [result, entered, phaseAInput, Counter.charge,
      List.mem_cons] at used
    rcases used with equal | old
    · cases equal
    · exact ready.2.2.2.2 (.guardFinalize slot key)
        (by simp [phaseBEntryReservedAddress]) old
  · intro used
    simp only [result, entered, phaseAInput, Counter.charge,
      List.mem_cons] at used
    rcases used with equal | old
    · cases equal
    · exact ready.2.2.2.2 (.phase .sealBEnterC)
        (by simp [phaseBEntryReservedAddress]) old

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem chargeAddresses?_total_usedRev
    {tokens : List Token} {state : Type} :
    ∀ addresses (current : CountedState tokens state),
      addresses.Nodup →
      (∀ address, address ∈ addresses →
        address ∉ current.counter.usedRev) →
      ∃ result, chargeAddresses? current addresses = some result ∧
        result.counter.usedRev =
          addresses.reverse ++ current.counter.usedRev := by
  intro addresses
  induction addresses with
  | nil =>
      intro current unique fresh
      exact ⟨current, rfl, by simp⟩
  | cons address rest induction =>
      intro current unique pending
      rw [List.nodup_cons] at unique
      have fresh := pending address (by simp)
      let next : CountedState tokens state := {
        payload := current.payload
        counter := current.counter.charge address fresh
      }
      have stepped : runMappedPrimitive? current address id = some next := by
        simp [runMappedPrimitive?, fresh, next]
      have restFresh : ∀ candidate, candidate ∈ rest →
          candidate ∉ next.counter.usedRev := by
        intro candidate member used
        rw [runMappedPrimitive?_usedRev current address id next stepped,
          List.mem_cons] at used
        rcases used with equal | old
        · exact unique.1 (equal.symm ▸ member)
        · exact pending candidate (by simp [member]) old
      obtain ⟨result, continued, resultUsed⟩ :=
        induction next unique.2 restFresh
      refine ⟨result, ?_, ?_⟩
      · rw [chargeAddresses?, stepped]
        exact continued
      · rw [resultUsed,
          runMappedPrimitive?_usedRev current address id next stepped]
        simp [List.reverse_cons, List.append_assoc]

private theorem preFinalGuardSlots_nodup : preFinalGuardSlots.Nodup := by
  decide

private theorem preFinalGuardAddresses_nodup
    {tokens : List Token} (key : GuardInstanceKey tokens) :
    (preFinalGuardSlots.map fun slot =>
      UnitAddress.guardFinalize slot key).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact preFinalGuardSlots_nodup.imp fun different equal =>
    different (UnitAddress.guardFinalize.inj equal).1

private theorem finalizeNextIndexedGuard?_total_ready
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (key : GuardInstanceKey tokens) (rest : List (GuardInstanceKey tokens))
    (remaining : current.payload.phaseB.remaining = key :: rest)
    (ready : PhaseBRunnerReady current) :
    ∃ result,
      finalizeNextIndexedGuard? current = some result ∧
      result.payload.phaseB.remaining = rest ∧
      PhaseBRunnerReady result := by
  have unique := ready.2.1
  rw [remaining, List.nodup_cons] at unique
  have keyMember : key ∈ current.payload.phaseB.remaining := by
    rw [remaining]
    simp
  have initializeFresh := ready.2.2.1 key keyMember
    .initializeUndecided
  let initializeTransition := fun (state : PhaseBIndexed file tokens) => ({
    phaseB := {
      state.phaseB with
      cells := fun candidate =>
        if candidate = key then some .undecided
        else state.phaseB.cells candidate
    }
    indexes := state.indexes
  } : PhaseBIndexed file tokens)
  let initialized : CountedState tokens (PhaseBIndexed file tokens) := {
    payload := initializeTransition current.payload
    counter := current.counter.charge
      (.guardFinalize .initializeUndecided key) initializeFresh
  }
  have initializedEq : runMappedPrimitive? current
      (.guardFinalize .initializeUndecided key) initializeTransition =
      some initialized := by
    simp [runMappedPrimitive?, initializeFresh, initialized]
  let lookupAddresses := preFinalGuardSlots.map fun slot =>
    UnitAddress.guardFinalize slot key
  have lookupFresh : ∀ address, address ∈ lookupAddresses →
      address ∉ initialized.counter.usedRev := by
    intro address member used
    simp only [lookupAddresses, List.mem_map] at member
    rcases member with ⟨slot, slotMember, rfl⟩
    rw [runMappedPrimitive?_usedRev current _ initializeTransition
      initialized initializedEq, List.mem_cons] at used
    rcases used with equal | old
    · have sameSlot := (UnitAddress.guardFinalize.inj equal).1
      subst slot
      simp [preFinalGuardSlots] at slotMember
    · exact ready.2.2.1 key keyMember _ old
  obtain ⟨lookedUp, lookedUpEq, lookedUpUsed⟩ :=
    chargeAddresses?_total_usedRev lookupAddresses initialized
      (preFinalGuardAddresses_nodup key) lookupFresh
  have initializedPayload := phaseB_runMappedPrimitive?_payload current
    (.guardFinalize .initializeUndecided key) initializeTransition
    initializedEq
  have lookedUpPayload := phaseB_chargeAddresses?_payload initialized
    lookupAddresses lookedUp lookedUpEq
  have complete : FullyMaterializedEvidenceEntries
      lookedUp.payload.indexes := by
    rw [lookedUpPayload, initializedPayload]
    exact ready.1
  obtain ⟨decision, decisionEq⟩ :=
    phaseBGuardDecisionFromIndexes?_total lookedUp.payload.indexes
      complete key
  have writeFresh : UnitAddress.guardFinalize .writeFinalDecision key ∉
      lookedUp.counter.usedRev := by
    intro used
    rw [lookedUpUsed, List.mem_append, List.mem_reverse,
      runMappedPrimitive?_usedRev current _ initializeTransition
        initialized initializedEq,
      List.mem_cons] at used
    rcases used with lookup | initMember | old
    · simp only [lookupAddresses, List.mem_map] at lookup
      rcases lookup with ⟨slot, slotMember, equal⟩
      have sameSlot := (UnitAddress.guardFinalize.inj equal).1
      subst slot
      simp [preFinalGuardSlots] at slotMember
    · cases initMember
    · exact ready.2.2.1 key keyMember .writeFinalDecision old
  let finalTransition := fun (state : PhaseBIndexed file tokens) => ({
    phaseB := {
      phaseA := state.phaseB.phaseA
      cells := fun candidate =>
        if candidate = key then some (.final decision)
        else state.phaseB.cells candidate
      remaining := rest
      finalizedRev := key :: state.phaseB.finalizedRev
    }
    indexes := state.indexes
  } : PhaseBIndexed file tokens)
  let result : CountedState tokens (PhaseBIndexed file tokens) := {
    payload := finalTransition lookedUp.payload
    counter := lookedUp.counter.charge
      (.guardFinalize .writeFinalDecision key) writeFresh
  }
  have finalEq : runMappedPrimitive? lookedUp
      (.guardFinalize .writeFinalDecision key) finalTransition =
      some result := by
    simp [runMappedPrimitive?, writeFresh, result]
  have selected : finalizeNextIndexedGuard? current = some result := by
    simpa [finalizeNextIndexedGuard?, remaining, initializeTransition,
      lookupAddresses, finalTransition, initializedEq, lookedUpEq,
      decisionEq] using finalEq
  refine ⟨result, selected, by rfl, ?_⟩
  constructor
  · rw [phaseB_runMappedPrimitive?_payload lookedUp _ finalTransition finalEq,
      lookedUpPayload, initializedPayload]
    exact ready.1
  refine ⟨unique.2, ?_, ?_⟩
  · intro candidate candidateMember slot used
    have candidateRest : candidate ∈ rest := by
      simpa [result, finalTransition] using candidateMember
    have different : candidate ≠ key := by
      intro equal
      exact unique.1 (equal ▸ candidateRest)
    rw [runMappedPrimitive?_usedRev lookedUp _ finalTransition result finalEq,
      lookedUpUsed, List.mem_cons, List.mem_append, List.mem_reverse,
      runMappedPrimitive?_usedRev current _ initializeTransition
        initialized initializedEq, List.mem_cons] at used
    rcases used with final | lookup | initMember | old
    · exact different (UnitAddress.guardFinalize.inj final).2
    · simp only [lookupAddresses, List.mem_map] at lookup
      rcases lookup with ⟨oldSlot, _, equal⟩
      exact different (UnitAddress.guardFinalize.inj equal).2.symm
    · exact different (UnitAddress.guardFinalize.inj initMember).2
    · exact ready.2.2.1 candidate
        (by rw [remaining, List.mem_cons]; exact Or.inr candidateRest)
        slot old
  · intro used
    rw [runMappedPrimitive?_usedRev lookedUp _ finalTransition result finalEq,
      lookedUpUsed, List.mem_cons, List.mem_append, List.mem_reverse,
      runMappedPrimitive?_usedRev current _ initializeTransition
        initialized initializedEq, List.mem_cons] at used
    rcases used with final | lookup | initMember | old
    · cases final
    · simp only [lookupAddresses, List.mem_map] at lookup
      rcases lookup with ⟨slot, _, equal⟩
      cases equal
    · cases initMember
    · exact ready.2.2.2 old

private theorem runIndexedPhaseB?_total_ready
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ remaining (current : CountedState tokens (PhaseBIndexed file tokens)),
      current.payload.phaseB.remaining = remaining →
      PhaseBRunnerReady current →
      ∃ result,
        runIndexedPhaseB? remaining.length current = some result ∧
        result.payload.phaseB.remaining = [] ∧
        PhaseBRunnerReady result := by
  intro remaining
  induction remaining with
  | nil =>
      intro current remainingEq ready
      exact ⟨current, by simp [runIndexedPhaseB?, remainingEq],
        remainingEq, ready⟩
  | cons key rest induction =>
      intro current remainingEq ready
      obtain ⟨next, nextEq, nextRemaining, nextReady⟩ :=
        finalizeNextIndexedGuard?_total_ready current key rest
          remainingEq ready
      obtain ⟨result, runEq, done, resultReady⟩ :=
        induction next nextRemaining nextReady
      refine ⟨result, ?_, done, resultReady⟩
      rw [List.length_cons, runIndexedPhaseB?, remainingEq, nextEq]
      exact runEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem sealIndexedPhaseB?_total_ready
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (remaining : current.payload.phaseB.remaining = [])
    (ready : PhaseBRunnerReady current) :
    ∃ result, sealIndexedPhaseB? current = some result := by
  let phaseBInput : CountedState tokens (PhaseBOpen file tokens) := {
    payload := current.payload.phaseB
    counter := current.counter
  }
  have sealFresh : UnitAddress.phase .sealBEnterC ∉
      phaseBInput.counter.usedRev := by
    simpa [phaseBInput] using ready.2.2.2
  let transition := fun (state : PhaseBOpen file tokens) => ({
    phaseA := state.phaseA
    memo := fun key =>
      match state.cells key with
      | some value => value
      | none => .undecided
    finalizedRev := state.finalizedRev
  } : PhaseBSealed file tokens)
  let result : CountedState tokens (PhaseBSealed file tokens) := {
    payload := transition phaseBInput.payload
    counter := phaseBInput.counter.charge (.phase .sealBEnterC) sealFresh
  }
  have stepped : runMappedPrimitive? phaseBInput (.phase .sealBEnterC)
      transition = some result := by
    simp [runMappedPrimitive?, sealFresh, result]
  refine ⟨result, ?_⟩
  simpa [sealIndexedPhaseB?, sealPhaseB?, phaseBInput, remaining,
    transition] using stepped

private theorem executeIndexedPhaseB?_total_ready
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (ready : PhaseBIndexedReady current) :
    ∃ result, executeIndexedPhaseB? current = some result := by
  obtain ⟨entered, enteredEq, enteredRemaining, enteredReady⟩ :=
    enterIndexedPhaseB?_total_ready current ready
  obtain ⟨finalized, runEq, finalizedRemaining, finalizedReady⟩ :=
    runIndexedPhaseB?_total_ready (allGuardInstanceKeys tokens)
      entered enteredRemaining enteredReady
  obtain ⟨result, sealedEq⟩ := sealIndexedPhaseB?_total_ready
    finalized finalizedRemaining finalizedReady
  exact ⟨result, by
    unfold executeIndexedPhaseB?
    rw [enteredEq]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [runEq]
    simp only [Option.bind_some]
    exact sealedEq⟩

private theorem executeObservedPhaseAB?_total_of_phaseA_ready
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (phaseA : CountedState tokens (PhaseAOpen file tokens))
    (executed : executePhaseA? file tokens owned = some phaseA)
    (sameMembers : canonicalRawItems tokens phaseA.payload.rawItems =
      canonicalRawItems tokens (rawSaturation tokens)) :
    ∃ result, executeObservedPhaseAB? file tokens owned = some result := by
  obtain ⟨indexed, indexedEq, indexedReady⟩ :=
    executePhaseA?_index_total_owned file tokens owned phaseA executed
      sameMembers
  obtain ⟨result, phaseBEq⟩ :=
    executeIndexedPhaseB?_total_ready indexed indexedReady
  exact ⟨result, by
    unfold executeObservedPhaseAB?
    rw [executed]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [indexedEq]
    simp only [Option.bind_some]
    exact phaseBEq⟩

private def ObservedPhaseABPrerequisites
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) : Prop :=
  ∃ phaseA : CountedState tokens (PhaseAOpen file tokens),
    executePhaseA? file tokens owned = some phaseA ∧
    canonicalRawItems tokens phaseA.payload.rawItems =
      canonicalRawItems tokens (rawSaturation tokens)

private theorem executeObservedPhaseAB?_total_iff_prerequisites
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    (∃ result, executeObservedPhaseAB? file tokens owned = some result) ↔
      ObservedPhaseABPrerequisites file tokens owned := by
  constructor
  · rintro ⟨result, selected⟩
    unfold executeObservedPhaseAB? at selected
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨phaseA, phaseAEq,
      indexed, indexedEq, phaseBEq⟩
    refine ⟨phaseA, phaseAEq, ?_⟩
    unfold indexSaturatedPhaseACanonicalWith? at indexedEq
    split at indexedEq
    next sameMembers => exact sameMembers
    next differentMembers => contradiction
  · rintro ⟨phaseA, phaseAEq, sameMembers⟩
    exact executeObservedPhaseAB?_total_of_phaseA_ready
      file tokens owned phaseA phaseAEq sameMembers

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- The exact completion coordinates erased by the target item. -/
private abbrev CompletionBackpointerCoordinates (tokens : List Token) :=
  Boundary tokens × ProductionId

/-- One executable association-list row, keyed by the exact contextual target. -/
private structure CompletionBackpointerEntry (tokens : List Token) where
  after : ContextualItemKey tokens
  shared : Boundary tokens
  finishedProduction : ProductionId
  deriving Repr, BEq, DecidableEq

namespace CompletionBackpointerEntry

private def coordinates {tokens : List Token}
    (entry : CompletionBackpointerEntry tokens) :
    CompletionBackpointerCoordinates tokens :=
  (entry.shared, entry.finishedProduction)

private def ofCompleted
    {file : WorkspaceFile} {tokens : List Token}
    (edge : StructurallyValidContextualCompletedEdge file tokens) :
    CompletionBackpointerEntry tokens := {
  after := edge.after
  shared := edge.shared
  finishedProduction := edge.finished.raw.production
}

end CompletionBackpointerEntry

/-- The machine stores at most one row for each exact contextual target. -/
private abbrev CompletionBackpointerLedger (tokens : List Token) :=
  List (CompletionBackpointerEntry tokens)

namespace CompletionBackpointerLedger

private def lookup? {tokens : List Token}
    (after : ContextualItemKey tokens) :
    CompletionBackpointerLedger tokens →
      Option (CompletionBackpointerCoordinates tokens)
  | [] => none
  | entry :: rest =>
      if entry.after = after then some entry.coordinates
      else lookup? after rest

/-- Insert a new target, reuse an agreeing row, and reject a conflict. -/
private def insert? {tokens : List Token}
    (ledger : CompletionBackpointerLedger tokens)
    (entry : CompletionBackpointerEntry tokens) :
    Option (CompletionBackpointerLedger tokens) :=
  match lookup? entry.after ledger with
  | none => some (entry :: ledger)
  | some stored =>
      if stored = entry.coordinates then some ledger else none

private theorem lookup?_eq_none_iff
    {tokens : List Token}
    (ledger : CompletionBackpointerLedger tokens)
    (after : ContextualItemKey tokens) :
    lookup? after ledger = none ↔
      ∀ entry, entry ∈ ledger → entry.after ≠ after := by
  induction ledger with
  | nil => simp [lookup?]
  | cons head tail induction =>
      by_cases equal : head.after = after
      · simp [lookup?, equal]
      · simp [lookup?, equal, induction]

private theorem insert?_covers
    {tokens : List Token}
    {ledger result : CompletionBackpointerLedger tokens}
    (entry : CompletionBackpointerEntry tokens)
    (selected : insert? ledger entry = some result) :
    lookup? entry.after result = some entry.coordinates := by
  unfold insert? at selected
  split at selected
  next absent =>
    cases selected
    simp [lookup?]
  next stored present =>
    split at selected
    next equal =>
      cases selected
      exact present.trans (congrArg some equal)
    next different => contradiction

private theorem insert?_preserves_lookup
    {tokens : List Token}
    {ledger result : CompletionBackpointerLedger tokens}
    (entry : CompletionBackpointerEntry tokens)
    (selected : insert? ledger entry = some result)
    {after : ContextualItemKey tokens}
    {coordinates : CompletionBackpointerCoordinates tokens}
    (covered : lookup? after ledger = some coordinates) :
    lookup? after result = some coordinates := by
  unfold insert? at selected
  split at selected
  next absent =>
    cases selected
    by_cases equal : entry.after = after
    · subst after
      rw [absent] at covered
      contradiction
    · simp [lookup?, equal, covered]
  next stored present =>
    split at selected
    next equal => cases selected; exact covered
    next different => contradiction

private def CoversCompleted
    {tokens : List Token}
    (ledger : CompletionBackpointerLedger tokens)
    (after : ContextualItemKey tokens)
    (shared : Boundary tokens)
    (finishedProduction : ProductionId) : Prop :=
  lookup? after ledger = some (shared, finishedProduction)

private def CoversPackedEdges
    (file : WorkspaceFile) (tokens : List Token)
    (ledger : CompletionBackpointerLedger tokens)
    (edges : List (StructurallyValidContextualPackedEdge file tokens)) : Prop :=
  ∀ edge, edge ∈ edges →
    match edge.1 with
    | .scanned _ _ _ => True
    | .completed _ finished after shared =>
        CoversCompleted ledger after shared finished.raw.production

private def packCompleted
    {file : WorkspaceFile} {tokens : List Token}
    (edge : StructurallyValidContextualCompletedEdge file tokens) :
    StructurallyValidContextualPackedEdge file tokens :=
  ⟨.completed edge.waiting edge.finished edge.after edge.shared,
    edge.structural⟩

private def packScanned
    {file : WorkspaceFile} {tokens : List Token}
    (edge : StructurallyValidContextualScannedEdge file tokens) :
    StructurallyValidContextualPackedEdge file tokens :=
  ⟨.scanned edge.before edge.after edge.cursor, edge.structural⟩

private theorem coversPackedEdges_nil
    (file : WorkspaceFile) (tokens : List Token) :
    CoversPackedEdges file tokens [] [] := by
  intro edge member
  simp at member

private theorem coversPackedEdges_cons_scanned
    {file : WorkspaceFile} {tokens : List Token}
    {ledger : CompletionBackpointerLedger tokens}
    {edges : List (StructurallyValidContextualPackedEdge file tokens)}
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (covers : CoversPackedEdges file tokens ledger edges) :
    CoversPackedEdges file tokens ledger (edges ++ [packScanned edge]) := by
  intro candidate member
  rw [List.mem_append] at member
  rcases member with oldMember | inserted
  · exact covers candidate oldMember
  · simp only [List.mem_singleton] at inserted
    subst candidate
    trivial

private theorem insert?_coversPackedEdges
    {file : WorkspaceFile} {tokens : List Token}
    {ledger result : CompletionBackpointerLedger tokens}
    {edges : List (StructurallyValidContextualPackedEdge file tokens)}
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : insert? ledger
      (CompletionBackpointerEntry.ofCompleted edge) = some result)
    (covers : CoversPackedEdges file tokens ledger edges) :
    CoversPackedEdges file tokens result (edges ++ [packCompleted edge]) := by
  intro candidate member
  rw [List.mem_append] at member
  rcases member with oldMember | inserted
  · have oldCovered := covers candidate oldMember
    cases key : candidate.1 with
    | scanned before after cursor =>
        simp only [key] at oldCovered
        trivial
    | completed waiting finished after shared =>
        simp only [key] at oldCovered
        unfold CoversCompleted at oldCovered ⊢
        exact insert?_preserves_lookup
          (CompletionBackpointerEntry.ofCompleted edge) selected oldCovered
  · simp only [List.mem_singleton] at inserted
    subst candidate
    change lookup? edge.after result =
      some (edge.shared, edge.finished.raw.production)
    exact insert?_covers (CompletionBackpointerEntry.ofCompleted edge) selected

/-- The atomic proof-free state update used inside the U04 edge insertion. -/
private def insertCompleted?
    {file : WorkspaceFile} {tokens : List Token}
    (ledger : CompletionBackpointerLedger tokens)
    (edges : List (StructurallyValidContextualPackedEdge file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens) :
    Option (CompletionBackpointerLedger tokens ×
      List (StructurallyValidContextualPackedEdge file tokens)) := do
  let nextLedger ← insert? ledger
    (CompletionBackpointerEntry.ofCompleted edge)
  pure (nextLedger, edges ++ [packCompleted edge])

private theorem insertCompleted?_coversPackedEdges
    {file : WorkspaceFile} {tokens : List Token}
    {ledger resultLedger : CompletionBackpointerLedger tokens}
    {edges resultEdges :
      List (StructurallyValidContextualPackedEdge file tokens)}
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : insertCompleted? ledger edges edge =
      some (resultLedger, resultEdges))
    (covers : CoversPackedEdges file tokens ledger edges) :
    CoversPackedEdges file tokens resultLedger resultEdges := by
  unfold insertCompleted? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨nextLedger, inserted, equal⟩
  cases equal
  exact insert?_coversPackedEdges edge inserted covers

end CompletionBackpointerLedger

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def contextualPredictionKey {tokens : List Token}
    (waiting : ContextualItemKey tokens) (predicted : ProductionId) :
    ChartPredictionKey tokens := {
  source := .contextual waiting.context
  dotted := ⟨waiting.raw.production, waiting.raw.dot⟩
  production := predicted
  origin := waiting.raw.origin
  current := waiting.raw.current
}

private def contextualCompletionKey {tokens : List Token}
    (waiting finished : ContextualItemKey tokens) : ChartCubicKey tokens := {
  source := .contextual waiting.context
  waiting := ⟨waiting.raw.production, waiting.raw.dot⟩
  finished := ⟨finished.raw.production, finished.raw.dot⟩
  origin := waiting.raw.origin
  shared := waiting.raw.current
  current := finished.raw.current
}

/-- Form the exact dot-zero prediction and its guarded production instance. -/
private def contextualPredictedItem?
    {tokens : List Token}
    (waiting : ContextualItemKey tokens) (predicted : ProductionId) :
    Option (ContextualItemKey tokens × ProductionInstanceKey tokens) :=
  match waiting.raw.production.rhs[waiting.raw.dot.val]? with
  | some (.nonterminal symbol) =>
      if _sameLhs : predicted.lhs = symbol then
        let context := descendContext waiting predicted
        let item : ContextualItemKey tokens := {
          raw := {
            production := predicted
            dot := ⟨0, Nat.zero_lt_succ _⟩
            origin := waiting.raw.current
            current := waiting.raw.current
          }
          context := context
        }
        some (item, {
          production := predicted
          origin := waiting.raw.current
          context := context
        })
      else
        none
  | _ => none

/-- Construct a checked contextual scan directly from Core terminal evidence. -/
private def contextualScannedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before : ContextualItemKey tokens) :
    Option (ContextualItemKey tokens ×
      StructurallyValidContextualScannedEdge file tokens) :=
  if nextInRange :
      before.raw.dot.val < before.raw.production.rhs.length then
    match nextEq : before.raw.production.rhs[before.raw.dot.val] with
    | .terminal terminal =>
        if currentInRange : before.raw.current.val < tokens.length + 1 then
          let cursor : TerminalCursor tokens :=
            ⟨before.raw.current.val, currentInRange⟩
          match MatchedTerminal.atCursor?
              file tokens owned terminal cursor with
          | none => none
          | some matched =>
              let afterRaw : DottedItem tokens := {
                production := before.raw.production
                dot := ⟨before.raw.dot.val + 1, by omega⟩
                origin := before.raw.origin
                current := cursor.afterBoundary
              }
              let after : ContextualItemKey tokens := {
                raw := afterRaw
                context := before.context
              }
              let witness : ScannedEdgeWitness
                  file tokens before.raw after.raw cursor := {
                terminal := terminal
                matched := matched.val
                sameCursor := matched.property
                next := by
                  constructor
                  · exact nextInRange
                  · rw [List.getElem?_eq_getElem nextInRange, nextEq]
                atCurrent := Fin.ext rfl
                advance := by
                  rw [matched.property]
                  simp [AdvanceItem, after, afterRaw]
              }
              let rawValid : PackedEdgeKey.Valid file tokens
                  (.scanned before.raw after.raw cursor) :=
                packedEdge_scanned_valid_iff.mpr ⟨witness⟩
              let structural :
                  ContextualPackedEdgeKey.StructurallyValid file tokens
                    (.scanned before after cursor) := ⟨rawValid, rfl⟩
              some (after, {
                before := before
                after := after
                cursor := cursor
                structural := structural
              })
        else
          none
    | _ => none
  else
    none

/-- Construct a checked contextual completion with both context equations. -/
private def contextualCompletedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished : ContextualItemKey tokens) :
    Option (ContextualItemKey tokens ×
      StructurallyValidContextualCompletedEdge file tokens) :=
  if nextInRange :
      waiting.raw.dot.val < waiting.raw.production.rhs.length then
    match nextEq : waiting.raw.production.rhs[waiting.raw.dot.val] with
    | .nonterminal symbol =>
        if sameLhs : symbol = finished.raw.production.lhs then
          if complete :
              finished.raw.dot.val = finished.raw.production.rhs.length then
            if sameCursor : waiting.raw.current = finished.raw.origin then
              if sameContext : finished.context =
                  descendContext waiting finished.raw.production then
                let afterRaw : DottedItem tokens := {
                  production := waiting.raw.production
                  dot := ⟨waiting.raw.dot.val + 1, by omega⟩
                  origin := waiting.raw.origin
                  current := finished.raw.current
                }
                let after : ContextualItemKey tokens := {
                  raw := afterRaw
                  context := waiting.context
                }
                let witness : CompletedEdgeWitness tokens waiting.raw
                    finished.raw after.raw waiting.raw.current := {
                  next := by
                    constructor
                    · exact nextInRange
                    · rw [List.getElem?_eq_getElem nextInRange,
                        nextEq, sameLhs]
                  complete := complete
                  waitingAtShared := rfl
                  finishedAtShared := sameCursor.symm
                  advance := by simp [AdvanceItem, after, afterRaw]
                }
                let rawValid : PackedEdgeKey.Valid file tokens
                    (.completed waiting.raw finished.raw after.raw
                      waiting.raw.current) :=
                  packedEdge_completed_valid_iff.mpr ⟨witness⟩
                let structural :
                    ContextualPackedEdgeKey.StructurallyValid file tokens
                      (.completed waiting finished after
                        waiting.raw.current) :=
                  ⟨rawValid, sameContext, rfl⟩
                some (after, {
                  waiting := waiting
                  finished := finished
                  after := after
                  shared := waiting.raw.current
                  structural := structural
                })
              else none
            else none
          else none
        else none
    | _ => none
  else
    none

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Phase-C chart state extended with the single-valued completion ledger. -/
private structure PhaseCWorklist
    (file : WorkspaceFile) (tokens : List Token) where
  phaseC : PhaseCOpen file tokens
  completionBackpointers : CompletionBackpointerLedger tokens

private def beginPhaseCWorklist?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens)) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) := do
  let entered ← enterPhaseC? current
  pure {
    payload := ⟨entered.payload, []⟩
    counter := entered.counter
  }

/-- Lift the existing production/guard activation machine without separating
its witness updates from the worklist carrier. -/
private def activateWorklistProduction?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens) × Bool) := do
  let (activated, accepted) ← activateProduction? {
    payload := current.payload.phaseC
    counter := current.counter
  } productionInstance
  pure ({
    payload := ⟨activated.payload,
      current.payload.completionBackpointers⟩
    counter := activated.counter
  }, accepted)

private def phaseCItemMemberBool
    {tokens : List Token} (items : List (ContextualItemKey tokens))
    (item : ContextualItemKey tokens) : Bool :=
  items.any fun candidate => decide (candidate = item)

private def phaseCEdgeMemberBool
    {file : WorkspaceFile} {tokens : List Token}
    (edges : List (StructurallyValidContextualPackedEdge file tokens))
    (edge : StructurallyValidContextualPackedEdge file tokens) : Bool :=
  edges.any fun candidate => decide (candidate.val = edge.val)

private inductive ContextualItemInsertSource where
  | prediction
  | scan
  | completion

private def ContextualItemInsertSource.unitKind :
    ContextualItemInsertSource → ChartLinearUnitKind
  | .prediction => .L03_itemInsert
  | .scan => .L05_scannedItemInsert
  | .completion => .L07_completedItemInsert

private def insertContextualItem?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  if phaseCItemMemberBool current.payload.phaseC.contextualItems item then
    some current
  else
    runMappedPrimitive? current
      (.linear source.unitKind (contextualLinearKey item))
      fun (state : PhaseCWorklist file tokens) => ({
        phaseC := {
          state.phaseC with
          contextualItems := state.phaseC.contextualItems ++ [item]
          itemQueue := state.phaseC.itemQueue ++ [item]
        }
        completionBackpointers := state.completionBackpointers
      } : PhaseCWorklist file tokens)

/-- Insert a checked scan; the completion ledger is unchanged. -/
private def insertContextualScannedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  let packed := CompletionBackpointerLedger.packScanned edge
  if phaseCEdgeMemberBool current.payload.phaseC.contextualEdges packed then
    some current
  else
    runMappedPrimitive? current
      (.linear .L06_scannedEdgeInsert
        (contextualLinearKey edge.before))
      fun (state : PhaseCWorklist file tokens) => ({
        phaseC := {
          state.phaseC with
          contextualEdges := state.phaseC.contextualEdges ++ [packed]
          edgeQueue := state.phaseC.edgeQueue ++ [packed]
        }
        completionBackpointers := state.completionBackpointers
      } : PhaseCWorklist file tokens)

/-- Atomically add a checked completion, its single-valued backpointer, and
the exact packed edge queue entry under the one U04 charge. -/
private def insertContextualCompletedEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  let packed := CompletionBackpointerLedger.packCompleted edge
  if phaseCEdgeMemberBool current.payload.phaseC.contextualEdges packed then
    some current
  else do
    let (nextLedger, nextEdges) ←
      CompletionBackpointerLedger.insertCompleted?
        current.payload.completionBackpointers
        current.payload.phaseC.contextualEdges edge
    runMappedPrimitive? current
      (.cubic .U04_completedEdgeInsert
        (contextualCompletionKey edge.waiting edge.finished))
      fun (state : PhaseCWorklist file tokens) => ({
        phaseC := {
          state.phaseC with
          contextualEdges := nextEdges
          edgeQueue := state.phaseC.edgeQueue ++ [packed]
        }
        completionBackpointers := nextLedger
      } : PhaseCWorklist file tokens)

private def dequeueContextualItem?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens)) :
    Option (ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens)) :=
  match current.payload.phaseC.itemQueue with
  | [] => none
  | item :: rest => do
      let next ← runMappedPrimitive? current
        (.linear .L01_itemDequeue (contextualLinearKey item))
        fun (state : PhaseCWorklist file tokens) => ({
          phaseC := { state.phaseC with itemQueue := rest }
          completionBackpointers := state.completionBackpointers
        } : PhaseCWorklist file tokens)
      pure (item, next)

private def dequeueContextualEdge?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens)) :
    Option (StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens)) :=
  match current.payload.phaseC.edgeQueue with
  | [] => none
  | edge :: rest => do
      let address : UnitAddress tokens :=
        match edge.val with
        | .scanned before _ _ =>
            .linear .L02_scannedEdgeDequeue (contextualLinearKey before)
        | .completed waiting finished _ _ =>
            .cubic .U02_completedEdgeDequeue
              (contextualCompletionKey waiting finished)
      let next ← runMappedPrimitive? current address
        fun (state : PhaseCWorklist file tokens) => ({
          phaseC := { state.phaseC with edgeQueue := rest }
          completionBackpointers := state.completionBackpointers
        } : PhaseCWorklist file tokens)
      pure (edge, next)

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Attempt one applicable contextual prediction, then activate its exact
production instance once.  A rejected guard set is a charged no-op. -/
private def attemptContextualPrediction?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  match contextualPredictedItem? waiting predicted with
  | none => some current
  | some (item, productionInstance) => do
      let attempted ← runMappedPrimitive? current
        (.prediction .R01_predictionAttempt
          (contextualPredictionKey waiting predicted)) id
      let activationAddress : UnitAddress tokens :=
        .production productionInstance
      if activationAddress ∈ attempted.counter.usedRev then
        some attempted
      else do
        let (activated, accepted) ←
          activateWorklistProduction? attempted productionInstance
        if accepted then
          insertContextualItem? activated .prediction item
        else
          some activated

private def attemptContextualPredictions?
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    List ProductionId →
      CountedState tokens (PhaseCWorklist file tokens) →
      Option (CountedState tokens (PhaseCWorklist file tokens))
  | [], current => some current
  | predicted :: rest, current => do
      let next ← attemptContextualPrediction? current waiting predicted
      attemptContextualPredictions? waiting rest next

private def contextualScanApplicable {tokens : List Token}
    (item : ContextualItemKey tokens) : Bool :=
  match item.raw.production.rhs[item.raw.dot.val]? with
  | some (.terminal _) =>
      decide (item.raw.current.val < tokens.length + 1)
  | _ => false

/-- Every applicable terminal scan consumes L04, including a mismatch. -/
private def attemptContextualScan?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  if contextualScanApplicable before then do
    let attempted ← runMappedPrimitive? current
      (.linear .L04_scanAttempt (contextualLinearKey before)) id
    match contextualScannedEdge? owned before with
    | none => some attempted
    | some (after, edge) => do
        let withItem ← insertContextualItem? attempted .scan after
        insertContextualScannedEdge? withItem edge
  else
    some current

/-- Charge U03 only for a structurally and contextually compatible pair.
U04 remains the atomic completed-edge/backpointer insertion. -/
private def attemptContextualCompletion?
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished : ContextualItemKey tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) :=
  match contextualCompletedEdge? (file := file) waiting finished with
  | none => some current
  | some (after, edge) =>
      let address : UnitAddress tokens :=
        .cubic .U03_completionAttempt
          (contextualCompletionKey waiting finished)
      if address ∈ current.counter.usedRev then
        some current
      else do
        let attempted ← runMappedPrimitive? current address id
        let withItem ← insertContextualItem? attempted .completion after
        insertContextualCompletedEdge? withItem edge

private def attemptContextualCompletionsWith?
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    List (ContextualItemKey tokens) →
      CountedState tokens (PhaseCWorklist file tokens) →
      Option (CountedState tokens (PhaseCWorklist file tokens))
  | [], current => some current
  | other :: rest, current => do
      let forward ← attemptContextualCompletion? current pivot other
      let reverse ←
        if other = pivot then
          some forward
        else
          attemptContextualCompletion? forward other pivot
      attemptContextualCompletionsWith? pivot rest reverse

private def processContextualItem?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (current : CountedState tokens (PhaseCWorklist file tokens)) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) := do
  let predicted ←
    attemptContextualPredictions? item allProductionIds current
  let scanned ← attemptContextualScan? owned predicted item
  attemptContextualCompletionsWith? item
    scanned.payload.phaseC.contextualItems scanned

/-- Drain item work before checked-edge work.  Edge dequeues are retained here;
semantic action reductions belong to the later value/frontier slice. -/
private def runPhaseCQueues?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Nat → CountedState tokens (PhaseCWorklist file tokens) →
      Option (CountedState tokens (PhaseCWorklist file tokens))
  | 0, current =>
      if current.payload.phaseC.itemQueue.isEmpty &&
          current.payload.phaseC.edgeQueue.isEmpty then
        some current
      else
        none
  | fuel + 1, current =>
      match current.payload.phaseC.itemQueue with
      | _ :: _ =>
          match dequeueContextualItem? current with
          | none => none
          | some (item, afterDequeue) => do
              let processed ←
                processContextualItem? owned item afterDequeue
              runPhaseCQueues? owned fuel processed
      | [] =>
          match current.payload.phaseC.edgeQueue with
          | _ :: _ =>
              match dequeueContextualEdge? current with
              | none => none
              | some (_, afterDequeue) =>
                  runPhaseCQueues? owned fuel afterDequeue
          | [] => some current

private def executePhaseCWorklist?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens)) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) := do
  let entered ← beginPhaseCWorklist? current
  runPhaseCQueues? owned (chartGBound (tokens.length + 1)) entered

/-- Execute the landed observed Phase A/B pipeline through the contextual
worklist drain.  Saturation correspondence, values, diagnostics, and outcome
selection are deliberately proved by later layers. -/
private def executeObservedPhaseABCWorklist?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    Option (CountedState tokens (PhaseCWorklist file tokens)) := do
  let phaseB ← executeObservedPhaseAB? file tokens owned
  executePhaseCWorklist? owned phaseB

private theorem runPhaseCQueues?_queues_empty
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      runPhaseCQueues? owned fuel current = some result →
        result.payload.phaseC.itemQueue = [] ∧
          result.payload.phaseC.edgeQueue = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result selected
      rw [runPhaseCQueues?] at selected
      split at selected
      · cases selected
        rename_i condition
        have queues := Bool.and_eq_true_iff.mp condition
        exact ⟨List.isEmpty_iff.mp queues.1,
          List.isEmpty_iff.mp queues.2⟩
      · contradiction
  | succ previous induction =>
      intro current result selected
      rw [runPhaseCQueues?] at selected
      cases items : current.payload.phaseC.itemQueue with
      | nil =>
          cases edges : current.payload.phaseC.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact ⟨items, edges⟩
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueContextualEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueContextualItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨dequeuedItem, afterDequeue⟩
              simp only at selected
              cases processing :
                  processContextualItem? owned dequeuedItem afterDequeue with
              | none => simp [processing] at selected
              | some processed =>
                  rw [processing] at selected
                  exact induction processed result selected

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- The executable completion ledger covers every retained completed edge. -/
private def PhaseCBackpointerInvariant
    (file : WorkspaceFile) (tokens : List Token)
    (state : PhaseCWorklist file tokens) : Prop :=
  CompletionBackpointerLedger.CoversPackedEdges file tokens
    state.completionBackpointers state.phaseC.contextualEdges

private theorem runMappedPrimitive?_payload
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    {result : CountedState tokens after}
    (selected : runMappedPrimitive? current address transition = some result) :
    result.payload = transition current.payload := by
  unfold runMappedPrimitive? at selected
  split at selected
  · cases selected
    rfl
  · contradiction

private theorem chargeAddresses?_payload
    {tokens : List Token} {state : Type}
    (addresses : List (UnitAddress tokens))
    (current result : CountedState tokens state)
    (selected : chargeAddresses? current addresses = some result) :
    result.payload = current.payload := by
  induction addresses generalizing current result with
  | nil =>
      simp only [chargeAddresses?] at selected
      cases selected
      rfl
  | cons address rest induction =>
      simp only [chargeAddresses?] at selected
      cases stepped : runMappedPrimitive? current address id with
      | none => simp [stepped] at selected
      | some next =>
          rw [stepped] at selected
          exact (induction next result selected).trans
            (runMappedPrimitive?_payload current address id stepped)

private theorem processGuardCell?_contextualEdges
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result) :
    result.1.payload.contextualEdges = current.payload.contextualEdges := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  have inspectedPayload := chargeAddresses?_payload
    (preInsertWitnessSlots.map fun slot =>
      .guardWitness slot (guardCellAddress productionInstance index))
    current inspected inspectedEq
  have insertedPayload := runMappedPrimitive?_payload inspected
    (.guardWitness .insertWitness
      (guardCellAddress productionInstance index)) _ insertedEq
  rw [insertedPayload, inspectedPayload]
  split <;> rfl

private theorem processGuardCells?_contextualEdges
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ (indices : List (Fin (guardOf productionInstance.production).length))
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
        result.1.payload.contextualEdges = current.payload.contextualEdges := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected
      simp only [processGuardCells?, Option.some.injEq] at selected
      cases selected
      rfl
  | cons index rest induction =>
      intro current result selected
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨processed, processedEq, finished, finishedEq, resultEq⟩
      cases resultEq
      exact (induction processed.1 finished finishedEq).trans
        (processGuardCell?_contextualEdges current productionInstance index
          processed processedEq)

private theorem activateProduction?_contextualEdges
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : activateProduction? current productionInstance = some result) :
    result.1.payload.contextualEdges = current.payload.contextualEdges := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  exact (processGuardCells?_contextualEdges productionInstance _
    attempted result processedEq).trans
      (congrArg PhaseCOpen.contextualEdges
        (runMappedPrimitive?_payload current
          (.production productionInstance) id attemptedEq))

private theorem beginPhaseCWorklist?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : beginPhaseCWorklist? current = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  have enteredPayload := runMappedPrimitive?_payload current
    (.linear .L03_itemInsert (contextualLinearKey (contextualRoot tokens))) _
    enteredEq
  unfold PhaseCBackpointerInvariant
  rw [enteredPayload]
  exact CompletionBackpointerLedger.coversPackedEdges_nil file tokens

private theorem activateWorklistProduction?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCBackpointerInvariant file tokens result.1.payload := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  unfold PhaseCBackpointerInvariant at invariant ⊢
  rw [activateProduction?_contextualEdges
    { payload := current.payload.phaseC, counter := current.counter }
    productionInstance activated activatedEq]
  exact invariant

private theorem insertContextualItem?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold insertContextualItem? at selected
  split at selected
  · cases selected
    exact invariant
  · rw [runMappedPrimitive?_payload current
      (.linear source.unitKind (contextualLinearKey item)) _ selected]
    exact invariant

private theorem insertContextualScannedEdge?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : insertContextualScannedEdge? current edge = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold insertContextualScannedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    exact invariant
  · rw [runMappedPrimitive?_payload current
      (.linear .L06_scannedEdgeInsert (contextualLinearKey edge.before)) _
      selected]
    exact CompletionBackpointerLedger.coversPackedEdges_cons_scanned edge
      invariant

private theorem insertContextualCompletedEdge?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : insertContextualCompletedEdge? current edge = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold insertContextualCompletedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    exact invariant
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with
      ⟨pair, insertedEq, chargedEq⟩
    rw [runMappedPrimitive?_payload current
      (.cubic .U04_completedEdgeInsert
        (contextualCompletionKey edge.waiting edge.finished)) _ chargedEq]
    exact CompletionBackpointerLedger.insertCompleted?_coversPackedEdges edge
      insertedEq invariant

private theorem dequeueContextualItem?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : dequeueContextualItem? current = some result) :
    PhaseCBackpointerInvariant file tokens result.2.payload := by
  unfold dequeueContextualItem? at selected
  cases queueEq : current.payload.phaseC.itemQueue with
  | nil => simp [queueEq] at selected
  | cons item rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      rw [runMappedPrimitive?_payload current
        (.linear .L01_itemDequeue (contextualLinearKey item)) _ nextEq]
      exact invariant

private theorem dequeueContextualEdge?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : dequeueContextualEdge? current = some result) :
    PhaseCBackpointerInvariant file tokens result.2.payload := by
  unfold dequeueContextualEdge? at selected
  cases queueEq : current.payload.phaseC.edgeQueue with
  | nil => simp [queueEq] at selected
  | cons edge rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      rw [runMappedPrimitive?_payload current _ _ nextEq]
      exact invariant

end Chart

namespace Chart
open Solcore.Workspace
private theorem attemptContextualPrediction?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold attemptContextualPrediction? at selected
  cases predictedEq : contextualPredictedItem? waiting predicted with
  | none =>
      simp only [predictedEq, Option.some.injEq] at selected
      cases selected
      exact invariant
  | some pair =>
      rcases pair with ⟨item, productionInstance⟩
      simp only [predictedEq] at selected
      cases attemptedEq : runMappedPrimitive? current
          (.prediction .R01_predictionAttempt
            (contextualPredictionKey waiting predicted)) id with
      | none => simp [attemptedEq] at selected
      | some attempted =>
          have attemptedInvariant :
              PhaseCBackpointerInvariant file tokens attempted.payload := by
            rw [runMappedPrimitive?_payload current
              (.prediction .R01_predictionAttempt
                (contextualPredictionKey waiting predicted)) id attemptedEq]
            exact invariant
          by_cases used : (UnitAddress.production productionInstance) ∈
              attempted.counter.usedRev
          · simp [attemptedEq, used] at selected
            cases selected
            exact attemptedInvariant
          · cases activatedEq :
                activateWorklistProduction? attempted productionInstance with
            | none => simp [attemptedEq, used, activatedEq] at selected
            | some activated =>
                have activatedInvariant :=
                  activateWorklistProduction?_backpointerInvariant attempted
                    productionInstance activated attemptedInvariant activatedEq
                cases acceptedEq : activated.2
                · simp [attemptedEq, used, activatedEq, acceptedEq] at selected
                  cases selected
                  exact activatedInvariant
                · simp [attemptedEq, used, activatedEq, acceptedEq] at selected
                  exact insertContextualItem?_backpointerInvariant
                    activated.1 result .prediction item activatedInvariant
                      selected

private theorem attemptContextualPredictions?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    ∀ (productions : List ProductionId)
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCBackpointerInvariant file tokens current.payload →
      attemptContextualPredictions? waiting productions current = some result →
      PhaseCBackpointerInvariant file tokens result.payload := by
  intro productions
  induction productions with
  | nil =>
      intro current result invariant selected
      simp only [attemptContextualPredictions?, Option.some.injEq] at selected
      cases selected
      exact invariant
  | cons predicted rest induction =>
      intro current result invariant selected
      simp only [attemptContextualPredictions?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      exact induction next result
        (attemptContextualPrediction?_backpointerInvariant current next
          waiting predicted invariant nextEq) restEq

private theorem attemptContextualScan?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : attemptContextualScan? owned current before = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold attemptContextualScan? at selected
  split at selected
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainderEq⟩
    have attemptedInvariant :
        PhaseCBackpointerInvariant file tokens attempted.payload := by
      rw [runMappedPrimitive?_payload current
        (.linear .L04_scanAttempt (contextualLinearKey before)) id attemptedEq]
      exact invariant
    cases scannedEq : contextualScannedEdge? owned before with
    | none =>
        simp only [scannedEq, Option.some.injEq] at remainderEq
        cases remainderEq
        exact attemptedInvariant
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scannedEq, Option.bind_eq_some_iff] at remainderEq
        rcases remainderEq with ⟨withItem, itemEq, edgeEq⟩
        exact insertContextualScannedEdge?_backpointerInvariant
          withItem result edge
          (insertContextualItem?_backpointerInvariant attempted withItem
            .scan after attemptedInvariant itemEq) edgeEq
  · cases selected
    exact invariant

private theorem attemptContextualCompletion?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished : ContextualItemKey tokens)
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold attemptContextualCompletion? at selected
  cases completionEq : contextualCompletedEdge?
      (file := file) waiting finished with
  | none =>
      simp only [completionEq, Option.some.injEq] at selected
      cases selected
      exact invariant
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completionEq] at selected
      split at selected
      · cases selected
        exact invariant
      · simp only [Option.bind_eq_bind,
          Option.bind_eq_some_iff] at selected
        rcases selected with
          ⟨attempted, attemptedEq, withItem, itemEq, edgeEq⟩
        have attemptedInvariant :
            PhaseCBackpointerInvariant file tokens attempted.payload := by
          rw [runMappedPrimitive?_payload current
            (.cubic .U03_completionAttempt
              (contextualCompletionKey waiting finished)) id attemptedEq]
          exact invariant
        exact insertContextualCompletedEdge?_backpointerInvariant
          withItem result edge
          (insertContextualItem?_backpointerInvariant attempted withItem
            .completion after attemptedInvariant itemEq) edgeEq

private theorem attemptContextualCompletionsWith?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    ∀ (others : List (ContextualItemKey tokens))
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCBackpointerInvariant file tokens current.payload →
      attemptContextualCompletionsWith? pivot others current = some result →
      PhaseCBackpointerInvariant file tokens result.payload := by
  intro others
  induction others with
  | nil =>
      intro current result invariant selected
      simp only [attemptContextualCompletionsWith?, Option.some.injEq] at selected
      cases selected
      exact invariant
  | cons other rest induction =>
      intro current result invariant selected
      rw [attemptContextualCompletionsWith?] at selected
      cases forwardEq :
          attemptContextualCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          have remainderEq := selected
          simp only [forwardEq] at remainderEq
          change (if other = pivot then
              attemptContextualCompletionsWith? pivot rest forward
            else
              (attemptContextualCompletion? forward other pivot).bind
                (attemptContextualCompletionsWith? pivot rest)) =
            some result at remainderEq
          have forwardInvariant :=
            attemptContextualCompletion?_backpointerInvariant current forward
              pivot other invariant forwardEq
          by_cases same : other = pivot
          · rw [if_pos same] at remainderEq
            exact induction forward result forwardInvariant remainderEq
          · rw [if_neg same] at remainderEq
            cases reverseEq :
                attemptContextualCompletion? forward other pivot with
            | none => simp [reverseEq] at remainderEq
            | some reverse =>
                rw [reverseEq] at remainderEq
                exact induction reverse result
                  (attemptContextualCompletion?_backpointerInvariant
                    forward reverse other pivot forwardInvariant reverseEq)
                  remainderEq

private theorem processContextualItem?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCBackpointerInvariant file tokens current.payload)
    (selected : processContextualItem? owned item current = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predicted, predictedEq, scanned, scannedEq, completedEq⟩
  have predictedInvariant :=
    attemptContextualPredictions?_backpointerInvariant item allProductionIds
      current predicted invariant predictedEq
  have scannedInvariant :=
    attemptContextualScan?_backpointerInvariant owned predicted scanned item
      predictedInvariant scannedEq
  exact attemptContextualCompletionsWith?_backpointerInvariant item
    scanned.payload.phaseC.contextualItems scanned result scannedInvariant
      completedEq

private theorem runPhaseCQueues?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result :
      CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCBackpointerInvariant file tokens current.payload →
      runPhaseCQueues? owned fuel current = some result →
      PhaseCBackpointerInvariant file tokens result.payload := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runPhaseCQueues?] at selected
      split at selected
      · cases selected
        exact invariant
      · contradiction
  | succ previous induction =>
      intro current result invariant selected
      rw [runPhaseCQueues?] at selected
      cases itemsEq : current.payload.phaseC.itemQueue with
      | nil =>
          cases edgesEq : current.payload.phaseC.edgeQueue with
          | nil =>
              simp only [itemsEq, edgesEq] at selected
              cases selected
              exact invariant
          | cons edge rest =>
              simp only [itemsEq, edgesEq] at selected
              cases dequeuedEq : dequeueContextualEdge? current with
              | none => simp [dequeuedEq] at selected
              | some dequeued =>
                  rw [dequeuedEq] at selected
                  exact induction dequeued.2 result
                    (dequeueContextualEdge?_backpointerInvariant current
                      dequeued invariant dequeuedEq) selected
      | cons item rest =>
          simp only [itemsEq] at selected
          cases dequeuedEq : dequeueContextualItem? current with
          | none => simp [dequeuedEq] at selected
          | some dequeued =>
              rw [dequeuedEq] at selected
              rcases dequeued with ⟨dequeuedItem, afterDequeue⟩
              simp only at selected
              cases processedEq :
                  processContextualItem? owned dequeuedItem afterDequeue with
              | none => simp [processedEq] at selected
              | some processed =>
                  rw [processedEq] at selected
                  have dequeuedInvariant :=
                    dequeueContextualItem?_backpointerInvariant current
                      (dequeuedItem, afterDequeue) invariant dequeuedEq
                  exact induction processed result
                    (processContextualItem?_backpointerInvariant owned
                      dequeuedItem afterDequeue processed dequeuedInvariant
                        processedEq) selected

private theorem executePhaseCWorklist?_backpointerInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executePhaseCWorklist? owned current = some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold executePhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, runEq⟩
  exact runPhaseCQueues?_backpointerInvariant owned
    (chartGBound (tokens.length + 1)) entered result
      (beginPhaseCWorklist?_backpointerInvariant current entered enteredEq)
      runEq

private theorem executeObservedPhaseABCWorklist?_backpointerInvariant
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    PhaseCBackpointerInvariant file tokens result.payload := by
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, _phaseBEq, phaseCEq⟩
  exact executePhaseCWorklist?_backpointerInvariant owned phaseB result phaseCEq

end Chart


namespace Chart

/-- Classify one normalized Phase-B observation.  Every guard is binary
except G02, whose failed header is negative at a pipe and neutral elsewhere. -/
def classifyGuardObservation
    (guard : PriorityGuardId) (positive pipeAtSite : Bool) :
    GuardDecision :=
  if positive then
    .positive
  else
    match guard with
    | .G02_matchArmBoundary =>
        if pipeAtSite then .negative else .neutral
    | _ => .negative

/-- Normalize the private U01 table reads to the two semantic bits consumed
by the public Phase-B classifier. -/
private def phaseBGuardObservationFromIndexes?
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) : Option (Bool × Bool) :=
  match key.guard with
  | .G01_statementIf => do
      let positive ← phaseBG01Positive? entries key
      pure (positive, false)
  | .G02_matchArmBoundary =>
      phaseBG02Observations? entries key
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime => do
      let positive ← phaseBComptimeAtSitePositive? entries key
      pure (positive, false)
  | .G06_patternComptime => do
      let positive ← phaseBG06Positive? entries key
      pure (positive, false)
  | .G07_leadingDotArguments => do
      let positive ← phaseBG07Positive? entries key
      pure (positive, false)
  | .G08_terminalExpression => do
      let positive ← phaseBG08Positive? entries key
      pure (positive, false)
  | .G09_genericContext => do
      let positive ← phaseBG09Positive? entries key
      pure (positive, false)

/-- The U01-backed Phase-B evaluator factors exactly through the public
two-bit classifier; it has no further decision semantics of its own. -/
private theorem phaseBGuardDecisionFromIndexes?_eq_classifier
    {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (key : GuardInstanceKey tokens) :
    phaseBGuardDecisionFromIndexes? entries key = (do
      let observation ← phaseBGuardObservationFromIndexes? entries key
      pure (classifyGuardObservation key.guard
        observation.1 observation.2)) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  cases guard <;>
    simp [phaseBGuardDecisionFromIndexes?,
      phaseBGuardObservationFromIndexes?, classifyGuardObservation,
      Option.bind_assoc]

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

/-- Proof-free terminal observation at one exact chart boundary. -/
def observedTerminalAtBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) : Bool :=
  if inRange : boundary.val < tokens.length + 1 then
    let cursor : TerminalCursor tokens := ⟨boundary.val, inRange⟩
    (MatchedTerminal.atCursor? file tokens owned terminal cursor).isSome
  else
    false

/-- Proof-free exact retained-terminal slice. -/
def observedExactSliceBool
    (tokens : List Token) (start finish : Boundary tokens)
    (classes : List TerminalSymbol) : Bool :=
  decide (finish.val = start.val + classes.length) &&
    (List.ofFn fun index : Fin classes.length =>
      if inRange : start.val + index.val < tokens.length then
        terminalMatchesBool (classes.get index)
          (.retained tokens[start.val + index.val])
      else
        false).all id

/-- Positive observations that do not depend on raw saturation. -/
def basicGuardPositiveObservation?
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) : Option Bool :=
  match key.guard with
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime =>
      some (observedTerminalAtBool owned
        (.contextualKeyword .comptimeKw) key.siteCursor)
  | .G07_leadingDotArguments =>
      some (observedExactSliceBool tokens
          key.contextStart key.siteCursor [
            .symbol .dot,
            .category .identifier
          ] &&
        observedTerminalAtBool owned
          (.symbol .leftParen) key.siteCursor)
  | _ => none

/-- The independent raw-pipe bit used by G02's three-way classifier. -/
def matchArmPipeObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  observedTerminalAtBool owned (.symbol .pipe) key.siteCursor

private theorem observedTerminalAtBool_eq_phaseA
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) :
    observedTerminalAtBool owned terminal boundary =
      phaseATerminalAtBool owned terminal boundary :=
  rfl

private theorem observedExactSliceBool_eq_phaseA
    (tokens : List Token) (start finish : Boundary tokens)
    (classes : List TerminalSymbol) :
    observedExactSliceBool tokens start finish classes =
      phaseAExactSliceBool tokens start finish classes :=
  rfl

private instance : LawfulBEq EvidenceIndexKind where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq PriorityGuardId where
  rfl := by intro value; cases value <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

private instance : LawfulBEq (PriorityGuardId ⊕ GrammarRuleId) where
  rfl := by
    intro value
    cases value with
    | inl guard => exact beq_self_eq_true guard
    | inr rule => exact beq_self_eq_true rule
  eq_of_beq := by
    intro left right equal
    cases left with
    | inl leftGuard =>
        cases right with
        | inl rightGuard =>
            congr
            exact LawfulBEq.eq_of_beq equal
        | inr rightRule => contradiction
    | inr leftRule =>
        cases right with
        | inl rightGuard => contradiction
        | inr rightRule =>
            congr
            exact LawfulBEq.eq_of_beq equal

private theorem phaseAEvidenceAddressEqBool_eq_true_iff
    {tokens : List Token}
    (left right : EvidenceIndexAddress tokens) :
    phaseAEvidenceAddressEqBool left right = true ↔ left = right := by
  cases left
  cases right
  simp [phaseAEvidenceAddressEqBool, beq_iff_eq, and_assoc]

private theorem phaseAEvidenceEntryAt?_map_exact
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (phaseA : PhaseAOpen file tokens) :
    ∀ (addresses : List (EvidenceIndexAddress tokens)),
      addresses.Nodup →
      ∀ address, address ∈ addresses →
        phaseAEvidenceEntryAt?
          (addresses.map fun candidate => ({
            address := candidate
            selected := evaluate phaseA candidate
          } : PhaseAEvidenceEntry tokens)) address =
            some (evaluate phaseA address) := by
  intro addresses
  induction addresses with
  | nil => simp
  | cons head tail induction =>
      intro unique address member
      rw [List.nodup_cons] at unique
      rw [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        simp [phaseAEvidenceEntryAt?,
          phaseAEvidenceAddressEqBool_self]
      · have different : head ≠ address := by
          intro equal
          exact unique.1 (equal ▸ member)
        have comparison :
            phaseAEvidenceAddressEqBool head address = false := by
          apply Bool.eq_false_iff.mpr
          intro selected
          exact different
            ((phaseAEvidenceAddressEqBool_eq_true_iff head address).mp
              selected)
        simp [phaseAEvidenceEntryAt?, comparison,
          induction unique.2 address member]

private theorem phaseAEvidenceEntryAt?_canonical_exact
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (phaseA : PhaseAOpen file tokens)
    (address : EvidenceIndexAddress tokens) :
    phaseAEvidenceEntryAt? (canonicalEvidenceEntries evaluate phaseA)
        address = some (evaluate phaseA address) := by
  exact phaseAEvidenceEntryAt?_map_exact evaluate phaseA
    (allEvidenceIndexAddresses tokens)
      (allEvidenceIndexAddresses_nodup tokens) address
      (allEvidenceIndexAddresses_complete address)

private theorem phaseAImmediateSuccessorObservation_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) :
    (match phaseABoundaryAt? tokens (boundary.val + 1) with
      | none => false
      | some after =>
          phaseAImmediatelyAfterTerminalBool owned terminal boundary after) =
        phaseATerminalAtBool owned terminal boundary := by
  by_cases successorIn : boundary.val + 1 < tokens.length + 2
  · rw [show phaseABoundaryAt? tokens (boundary.val + 1) =
        some ⟨boundary.val + 1, successorIn⟩ by
      simp [phaseABoundaryAt?, successorIn]]
    simp [phaseAImmediatelyAfterTerminalBool]
  · rw [show phaseABoundaryAt? tokens (boundary.val + 1) = none by
      simp [phaseABoundaryAt?, successorIn]]
    have terminalOutOfRange : ¬ boundary.val < tokens.length + 1 := by
      omega
    simp [phaseATerminalAtBool, terminalOutOfRange]

private theorem phaseAImmediateSuccessorOption_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens) :
    (match phaseABoundaryAt? tokens (boundary.val + 1) with
      | none => some false
      | some after =>
          some (phaseAImmediatelyAfterTerminalBool
            owned terminal boundary after)) =
        some (phaseATerminalAtBool owned terminal boundary) := by
  have exact :=
    phaseAImmediateSuccessorObservation_exact owned terminal boundary
  cases selected : phaseABoundaryAt? tokens (boundary.val + 1) with
  | none =>
      rw [selected] at exact
      simp only at exact
      rw [← exact]
  | some after =>
      rw [selected] at exact
      simp only at exact
      rw [← exact]

private theorem phaseAImmediateSuccessorAndOption_exact
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol) (boundary : Boundary tokens)
    (leading : Bool) :
    (match phaseABoundaryAt? tokens (boundary.val + 1) with
      | none => some false
      | some after => some (leading &&
          phaseAImmediatelyAfterTerminalBool
            owned terminal boundary after)) =
        some (leading && phaseATerminalAtBool owned terminal boundary) := by
  have exact :=
    phaseAImmediateSuccessorObservation_exact owned terminal boundary
  cases selected : phaseABoundaryAt? tokens (boundary.val + 1) with
  | none =>
      rw [selected] at exact
      simp only at exact
      rw [← exact]
      simp
  | some after =>
      rw [selected] at exact
      simp only at exact
      rw [← exact]

/-- On canonical U01 materialization, the saturation-independent guards read
exactly the public basic observations. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_basic
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (supported :
      key.guard = .G03_parameterComptime ∨
      key.guard = .G04_letComptime ∨
      key.guard = .G05_typeComptime ∨
      key.guard = .G07_leadingDotArguments) :
    ∃ observed,
      phaseBGuardObservationFromIndexes?
          (canonicalEvidenceEntries
            (phaseAObservationIndexEvaluator owned) phaseA) key =
        some (observed, false) ∧
      basicGuardPositiveObservation? owned key = some observed := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  cases guard <;>
    simp_all [phaseBGuardObservationFromIndexes?,
      basicGuardPositiveObservation?, phaseBComptimeAtSitePositive?,
      phaseBG07Positive?, phaseBWithBoundary?, phaseBAllReads?,
      phaseBReadTerminalGuard?, phaseBReadExactSliceGuard?,
      phaseBReadIndex?, phaseAEvidenceEntryAt?_canonical_exact,
      phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
      phaseAExactSliceGuardBool,
      phaseAImmediateSuccessorOption_exact,
      phaseAImmediateSuccessorAndOption_exact,
      observedTerminalAtBool_eq_phaseA,
      observedExactSliceBool_eq_phaseA]

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

/-- Canonical U01 materialization preserves G02's independent pipe bit;
only the header bit remains tied to the raw-saturation observation. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_matchArmPipe
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isMatchArm : key.guard = .G02_matchArmBoundary) :
    ∃ header,
      phaseBGuardObservationFromIndexes?
          (canonicalEvidenceEntries
            (phaseAObservationIndexEvaluator owned) phaseA) key =
        some (header, matchArmPipeObservationBool owned key) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G02_matchArmBoundary at isMatchArm
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG02Observations?,
    phaseBReadDelimiterGuard?, phaseBReadTerminalGuard?,
    phaseBWithBoundary?, phaseBReadIndex?,
    phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
    phaseADelimiterOrRegionGuardBool,
    phaseAImmediateSuccessorOption_exact,
    matchArmPipeObservationBool, observedTerminalAtBool_eq_phaseA]

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

/-- A proof-free greatest-end oracle supplied by saturated Phase A. -/
abbrev GreatestEndObservation (tokens : List Token) :=
  NonterminalSymbol → Boundary tokens → Boundary tokens →
    Boundary tokens → Bool

/-- G09's complete positive observation, parameterized only by the raw
greatest-end oracle whose semantic adequacy belongs to Phase A. -/
def genericContextPositiveObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (greatest : GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  (List.finRange (tokens.length + 2)).any fun arrowCursor =>
    observedTerminalAtBool owned (.symbol .fatArrow) arrowCursor &&
      greatest (.rule .predicateList)
        key.siteCursor arrowCursor arrowCursor

private theorem phaseBAnyReads?_map_some
    {alpha : Type} (values : List alpha) (select : alpha → Bool) :
    phaseBAnyReads? (values.map fun value => some (select value)) =
      some (values.any select) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [phaseBAnyReads?, induction]

/-- Canonical U01 reads implement G09's public parameterized observation with
the concrete raw Phase-A greatest-end oracle. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_G09
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isGeneric : key.guard = .G09_genericContext) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (genericContextPositiveObservationBool owned
        (fun symbol start upperBound finish =>
          rawGreatestEndBool phaseA symbol start upperBound finish) key,
        false) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G09_genericContext at isGeneric
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG09Positive?,
    phaseBReadTerminalGuard?, phaseBReadGreatestRule?,
    phaseBReadIndex?, phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
    phaseBAllReads?, phaseBAnyReads?_map_some,
    genericContextPositiveObservationBool,
    observedTerminalAtBool_eq_phaseA]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Public checked construction of one chart boundary. -/
def observedBoundaryAt?
    (tokens : List Token) (coordinate : Nat) : Option (Boundary tokens) :=
  if inRange : coordinate < tokens.length + 2 then
    some ⟨coordinate, inRange⟩
  else
    none

/-- Proof-free terminal observation with its exact successor boundary. -/
def observedImmediatelyAfterTerminalBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (boundary after : Boundary tokens) : Bool :=
  observedTerminalAtBool owned terminal boundary &&
    decide (after.val = boundary.val + 1)

/-- The same-depth pattern delimiter oracle used by G06. -/
abbrev PatternDelimiterObservation (tokens : List Token) :=
  Boundary tokens → Boundary tokens → Bool

/-- G06's complete positive observation, parameterized by the delimiter and
greatest-end facts whose adequacy is proved at their own phase boundaries. -/
def patternComptimePositiveObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (nextDelimiter : PatternDelimiterObservation tokens)
    (greatest : GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  match observedBoundaryAt? tokens (key.siteCursor.val + 1) with
  | none => false
  | some expressionStart =>
      observedImmediatelyAfterTerminalBool owned
          (.contextualKeyword .comptimeKw)
          key.siteCursor expressionStart &&
        (List.finRange (tokens.length + 2)).any fun limit =>
          nextDelimiter expressionStart limit &&
            greatest (.rule .expression)
              expressionStart limit limit

private theorem observedBoundaryAt?_eq_phaseA
    (tokens : List Token) (coordinate : Nat) :
    observedBoundaryAt? tokens coordinate =
      phaseABoundaryAt? tokens coordinate :=
  rfl

private theorem observedImmediatelyAfterTerminalBool_eq_phaseA
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (terminal : TerminalSymbol)
    (boundary after : Boundary tokens) :
    observedImmediatelyAfterTerminalBool owned terminal boundary after =
      phaseAImmediatelyAfterTerminalBool owned terminal boundary after := by
  simp [observedImmediatelyAfterTerminalBool,
    phaseAImmediatelyAfterTerminalBool,
    observedTerminalAtBool_eq_phaseA]

/-- Canonical U01 reads implement G06's public parameterized observation. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_G06
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isPattern : key.guard = .G06_patternComptime) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (patternComptimePositiveObservationBool owned
        (fun start limit =>
          phaseANextSameDepthDelimiterBool tokens start limit {
            head := .comma
            tail := [.rightParen, .fatArrow]
          })
        (fun symbol start upperBound finish =>
          rawGreatestEndBool phaseA symbol start upperBound finish) key,
        false) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G06_patternComptime at isPattern
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG06Positive?,
    phaseBWithBoundary?,
    phaseBReadTerminalGuard?, phaseBReadDelimiterGuard?,
    phaseBReadGreatestRule?, phaseBReadIndex?,
    phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
    phaseADelimiterOrRegionGuardBool, phaseBAllReads?,
    phaseBAnyReads?_map_some,
    patternComptimePositiveObservationBool,
    observedBoundaryAt?_eq_phaseA,
    observedImmediatelyAfterTerminalBool_eq_phaseA]
  cases selected : phaseABoundaryAt? tokens (siteCursor.val + 1) <;>
    simp

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- A proof-free match-arm header oracle supplied by saturated Phase A. -/
abbrev MatchArmHeaderObservation (tokens : List Token) :=
  Boundary tokens → Boundary tokens → Bool

/-- G02's positive header bit, kept separate from its exact pipe bit. -/
def matchArmHeaderObservationBool
    {tokens : List Token}
    (header : MatchArmHeaderObservation tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  header key.contextStart key.siteCursor

/-- Canonical U01 reads implement G02's public parameterized header together
with the already-exact pipe observation. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_G02
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isMatchArm : key.guard = .G02_matchArmBoundary) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (matchArmHeaderObservationBool
          (fun regionStart cursor =>
            phaseAArmHeaderBool phaseA regionStart cursor) key,
        matchArmPipeObservationBool owned key) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G02_matchArmBoundary at isMatchArm
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG02Observations?,
    phaseBReadDelimiterGuard?, phaseBReadTerminalGuard?,
    phaseBWithBoundary?, phaseBReadIndex?,
    phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
    phaseADelimiterOrRegionGuardBool,
    phaseAImmediateSuccessorOption_exact,
    matchArmHeaderObservationBool, matchArmPipeObservationBool,
    observedTerminalAtBool_eq_phaseA]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- A proof-free nearest-statement-region oracle supplied by Phase A. -/
abbrev StatementRegionObservation (tokens : List Token) :=
  Boundary tokens → Boundary tokens → Bool

/-- G08's complete positive observation, parameterized by the nearest-region
and greatest-end oracles whose semantic adequacy belongs to Phase A. -/
def terminalExpressionPositiveObservationBool
    {tokens : List Token}
    (region : StatementRegionObservation tokens)
    (greatest : GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  (List.finRange (tokens.length + 2)).any fun regionEnd =>
    region key.contextStart regionEnd &&
      greatest (.rule .expression)
        key.siteCursor regionEnd regionEnd

/-- Canonical U01 reads implement G08's public parameterized observation. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_G08
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isTerminalExpression : key.guard = .G08_terminalExpression) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (terminalExpressionPositiveObservationBool
        (fun regionStart regionEnd =>
          phaseANearestStatementRegionBool phaseA regionStart regionEnd)
        (fun symbol start upperBound finish =>
          rawGreatestEndBool phaseA symbol start upperBound finish) key,
        false) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G08_terminalExpression at isTerminalExpression
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG08Positive?,
    phaseBReadDelimiterGuard?, phaseBReadGreatestRule?,
    phaseBReadIndex?, phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseADelimiterOrRegionGuardBool,
    phaseBAllReads?, phaseBAnyReads?_map_some,
    terminalExpressionPositiveObservationBool]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- A proof-free matching-parenthesis oracle supplied by Phase A. -/
abbrev MatchingParenthesisObservation (tokens : List Token) :=
  Boundary tokens → Boundary tokens → Bool

/-- The complete terminal-only part of G01 at fixed structural boundaries. -/
def statementIfTerminalObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (siteCursor openCursor expressionStart closeCursor : Boundary tokens) :
    Bool :=
  match observedBoundaryAt? tokens (closeCursor.val + 1) with
  | none => false
  | some afterClose =>
      observedImmediatelyAfterTerminalBool owned (.hardKeyword .ifKw)
          siteCursor openCursor &&
        observedImmediatelyAfterTerminalBool owned (.symbol .leftParen)
          openCursor expressionStart &&
        observedImmediatelyAfterTerminalBool owned (.symbol .rightParen)
          closeCursor afterClose &&
        observedTerminalAtBool owned (.symbol .leftBrace) afterClose

/-- G01's complete positive observation, parameterized only by the delimiter
and greatest-end oracles whose semantic adequacy belongs to Phase A. -/
def statementIfPositiveObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (matching : MatchingParenthesisObservation tokens)
    (greatest : GreatestEndObservation tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  match observedBoundaryAt? tokens (key.siteCursor.val + 1),
      observedBoundaryAt? tokens (key.siteCursor.val + 2) with
  | some openCursor, some expressionStart =>
      (List.finRange (tokens.length + 2)).any fun closeCursor =>
        statementIfTerminalObservationBool owned key.siteCursor
            openCursor expressionStart closeCursor &&
          (matching openCursor closeCursor &&
            greatest (.rule .expression)
              expressionStart closeCursor closeCursor)
  | _, _ => false

/-- Canonical U01 reads implement G01's public parameterized observation. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_G01
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (key : GuardInstanceKey tokens)
    (isStatementIf : key.guard = .G01_statementIf) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (statementIfPositiveObservationBool owned
        (fun openCursor closeCursor =>
          phaseAMatchingDelimiterBool tokens openCursor closeCursor
            .leftParen .rightParen)
        (fun symbol start upperBound finish =>
          rawGreatestEndBool phaseA symbol start upperBound finish) key,
        false) := by
  rcases key with ⟨guard, contextStart, siteCursor, ordered⟩
  change guard = .G01_statementIf at isStatementIf
  subst guard
  simp [phaseBGuardObservationFromIndexes?, phaseBG01Positive?,
    phaseBWithBoundary?, phaseBReadTerminalGuard?,
    phaseBReadDelimiterGuard?, phaseBReadGreatestRule?,
    phaseBReadIndex?, phaseAEvidenceEntryAt?_canonical_exact,
    phaseAObservationIndexEvaluator, phaseATerminalWindowGuardBool,
    phaseADelimiterOrRegionGuardBool, phaseBAllReads?,
    phaseBAnyReads?_map_some, statementIfPositiveObservationBool,
    statementIfTerminalObservationBool,
    observedBoundaryAt?_eq_phaseA,
    observedImmediatelyAfterTerminalBool_eq_phaseA,
    observedTerminalAtBool_eq_phaseA]
  cases openSelected : phaseABoundaryAt? tokens (siteCursor.val + 1) <;>
    simp
  cases expressionSelected :
      phaseABoundaryAt? tokens (siteCursor.val + 2) <;>
    simp
  congr 1
  funext closeCursor
  cases phaseABoundaryAt? tokens (closeCursor.val + 1) <;> rfl

end Chart

namespace Chart

open Solcore.Workspace

/-- Public result of the executable Phase-A/Phase-B guard worklist. -/
structure GuardWorklistResult (tokens : List Token) where
  memo : GuardMemo tokens

/-- Execute raw saturation, materialize its observations, and finalize every
grammar-owned guard cell. -/
def executeObservedGuardWorklist?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    Option (GuardWorklistResult tokens) := do
  let result ← executeObservedPhaseAB? file tokens owned
  pure { memo := result.payload.memo }

/-- Every guard cell returned by the executable worklist is final. -/
theorem executeObservedGuardWorklist?_allGuardsFinal
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : GuardWorklistResult tokens)
    (selected : executeObservedGuardWorklist? file tokens owned =
      some result) :
    AllGuardsFinal result.memo := by
  unfold executeObservedGuardWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  exact executeObservedPhaseAB?_allFinal file tokens owned internal
    internalEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Public membership view of the proof-free raw saturation. -/
def SaturatedRawItem (tokens : List Token) (item : DottedItem tokens) : Prop :=
  item ∈ rawSaturation tokens

/-- Every grammar seed belongs to raw saturation. -/
theorem saturatedRawItem_seed
    {tokens : List Token} (production : ProductionId)
    (cursor : Boundary tokens) :
    SaturatedRawItem tokens {
      production := production
      dot := ⟨0, Nat.zero_lt_succ _⟩
      origin := cursor
      current := cursor
    } := by
  exact rawSaturation_seed_closed rfl rfl

/-- Raw saturation is closed under one unguarded prediction. -/
theorem saturatedRawItem_predict
    {tokens : List Token} (waiting : DottedItem tokens)
    (predicted : ProductionId)
    (waitingMember : SaturatedRawItem tokens waiting)
    (next : NextSymbol waiting (.nonterminal predicted.lhs)) :
    SaturatedRawItem tokens {
      production := predicted
      dot := ⟨0, Nat.zero_lt_succ _⟩
      origin := waiting.current
      current := waiting.current
    } := by
  exact rawSaturation_predict_closed waitingMember next rfl rfl rfl

/-- Raw saturation is closed under one exact terminal scan. -/
theorem saturatedRawItem_scan
    {file : WorkspaceFile} {tokens : List Token}
    (before after : DottedItem tokens) (cursor : TerminalCursor tokens)
    (terminal : TerminalSymbol) (value : TerminalStreamValue)
    (span : SourceSpan)
    (beforeMember : SaturatedRawItem tokens before)
    (next : NextSymbol before (.terminal terminal))
    (atCurrent : cursor.beforeBoundary = before.current)
    (terminalAt : TerminalAt file tokens cursor value span)
    (matchedEvidence : TerminalMatches terminal value)
    (advance : AdvanceItem before cursor.afterBoundary after) :
    SaturatedRawItem tokens after := by
  apply rawSaturation_scan_closed beforeMember
  apply packedEdge_scanned_valid_iff.mpr
  exact ⟨{
    terminal := terminal
    matched := {
      cursor := cursor
      value := value
      span := span
      «at» := terminalAt
      «matches» := matchedEvidence
    }
    sameCursor := rfl
    next := next
    atCurrent := atCurrent
    advance := advance
  }⟩

/-- Raw saturation is closed under one exact completion. -/
theorem saturatedRawItem_complete
    {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (waitingMember : SaturatedRawItem tokens waiting)
    (finishedMember : SaturatedRawItem tokens finished)
    (next : NextSymbol waiting
      (.nonterminal finished.production.lhs))
    (finishedComplete : CompleteItem finished)
    (sameCursor : waiting.current = finished.origin)
    (advance : AdvanceItem waiting finished.current after) :
    SaturatedRawItem tokens after :=
  rawSaturation_complete_closed waitingMember finishedMember next
    finishedComplete sameCursor advance

/-- Leastness interface for raw saturation.  The decidability argument is
operational only and does not become a semantic dependency. -/
theorem saturatedRawItem_induction
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (property : DottedItem tokens → Prop)
    (propertyDecision : ∀ item, Decidable (property item))
    (seed : ∀ production cursor,
      property ({
        production := production
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := cursor
        current := cursor
      } : DottedItem tokens))
    (predict : ∀ waiting predicted,
      property waiting →
      NextSymbol waiting (.nonterminal predicted.lhs) →
      property ({
        production := predicted
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := waiting.current
        current := waiting.current
      } : DottedItem tokens))
    (scan : ∀ before after cursor terminal value span,
      property before →
      NextSymbol before (.terminal terminal) →
      cursor.beforeBoundary = before.current →
      TerminalAt file tokens cursor value span →
      TerminalMatches terminal value →
      AdvanceItem before cursor.afterBoundary after →
      property after)
    (complete : ∀ waiting finished after,
      property waiting → property finished →
      NextSymbol waiting (.nonterminal finished.production.lhs) →
      CompleteItem finished →
      waiting.current = finished.origin →
      AdvanceItem waiting finished.current after →
      property after)
    {item : DottedItem tokens}
    (member : SaturatedRawItem tokens item) : property item := by
  let acceptedItems := (allDottedItems tokens).filter fun candidate =>
    @decide (property candidate) (propertyDecision candidate)
  have accepted_iff (candidate : DottedItem tokens) :
      candidate ∈ acceptedItems ↔ property candidate := by
    simp [acceptedItems, allDottedItems_complete,
      @decide_eq_true_iff (property candidate) (propertyDecision candidate)]
  have closed : ExecutableRawClosed owned acceptedItems := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro candidate candidateSeed
      apply (accepted_iff candidate).mpr
      rw [rawSeedItems, List.mem_filter] at candidateSeed
      have selected := candidateSeed.2
      simp only [rawSeedBool, Bool.and_eq_true, beq_iff_eq] at selected
      let canonical : DottedItem tokens := {
        production := candidate.production
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := candidate.current
        current := candidate.current
      }
      have canonicalEq : canonical = candidate :=
        dottedItem_eq_of_fields rfl selected.1.symm selected.2.symm rfl
      have canonicalProperty : property canonical := by
        simpa only [canonical] using
          seed candidate.production candidate.current
      exact canonicalEq ▸ canonicalProperty
    · intro waiting waitingMember production result computed
      apply (accepted_iff result).mpr
      have waitingAccepted := (accepted_iff waiting).mp waitingMember
      unfold predictedItem? at computed
      split at computed
      next symbol nextEq =>
        split at computed
        next sameLhs =>
          cases computed
          apply predict waiting production waitingAccepted
          rcases List.getElem?_eq_some_iff.mp nextEq with ⟨bound, _⟩
          exact ⟨bound, by simpa [sameLhs] using nextEq⟩
        next => contradiction
      next => contradiction
    · intro before beforeMember after edge computed
      apply (accepted_iff after).mpr
      have beforeAccepted := (accepted_iff before).mp beforeMember
      obtain ⟨cursor, shape⟩ :=
        scannedEdge?_shape owned before after edge computed
      have valid : PackedEdgeKey.Valid file tokens
          (.scanned before after cursor) := by
        rw [← shape]
        exact edge.property
      rcases valid with ⟨terminal, value, span, next, atCurrent,
        terminalAt, matchedEvidence, advance⟩
      exact scan before after cursor terminal value span beforeAccepted next
        atCurrent terminalAt matchedEvidence advance
    · intro waiting waitingMember finished finishedMember after edge computed
      apply (accepted_iff after).mpr
      have waitingAccepted := (accepted_iff waiting).mp waitingMember
      have finishedAccepted := (accepted_iff finished).mp finishedMember
      obtain ⟨shared, shape⟩ :=
        completedEdge?_shape waiting finished after edge computed
      have valid : PackedEdgeKey.Valid file tokens
          (.completed waiting finished after shared) := by
        rw [← shape]
        exact edge.property
      rcases valid with ⟨symbol, next, finishedComplete, lhs,
        waitingAtShared, finishedAtShared, advance⟩
      have exactNext : NextSymbol waiting
          (.nonterminal finished.production.lhs) := by
        simpa [lhs] using next
      exact complete waiting finished after waitingAccepted finishedAccepted
        exactNext finishedComplete
        (waitingAtShared.trans finishedAtShared.symm) advance
  apply (accepted_iff item).mp
  apply rawSaturation_subset_of_closed
    (closed.rawClosureBool owned acceptedItems) item
  exact member

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Recognition computed over the canonical proof-free raw saturation. -/
def saturatedRawRecognizesBool
    (tokens : List Token) (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) : Bool :=
  (rawSaturation tokens).any fun item =>
    item.dot.val == item.production.rhs.length &&
      item.production.lhs == symbol &&
      item.origin == start && item.current == finish

/-- The saturated recognition Boolean exposes exactly one complete raw item. -/
theorem saturatedRawRecognizesBool_eq_true_iff
    (tokens : List Token) (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) :
    saturatedRawRecognizesBool tokens symbol start finish = true ↔
      ∃ item : DottedItem tokens,
        SaturatedRawItem tokens item ∧
          CompleteItem item ∧
          item.production.lhs = symbol ∧
          item.origin = start ∧
          item.current = finish := by
  unfold saturatedRawRecognizesBool
  rw [List.any_eq_true]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨item, member, ⟨⟨⟨complete, lhs⟩, origin⟩, current⟩⟩
    exact ⟨item, member, complete, lhs, origin, current⟩
  · rintro ⟨item, member, complete, lhs, origin, current⟩
    exact ⟨item, member, ⟨⟨⟨complete, lhs⟩, origin⟩, current⟩⟩

/-- Greatest-end observation computed over canonical raw saturation. -/
def saturatedRawGreatestEndObservation
    (tokens : List Token) : GreatestEndObservation tokens :=
  fun symbol start upperBound finish =>
    saturatedRawRecognizesBool tokens symbol start finish &&
      decide (finish.val ≤ upperBound.val) &&
      (List.finRange (tokens.length + 2)).all fun candidate =>
        if candidate.val ≤ upperBound.val then
          !saturatedRawRecognizesBool tokens symbol start candidate ||
            decide (candidate.val ≤ finish.val)
        else
          true

private theorem list_any_eq_of_mem_iff
    {alpha : Type} (left right : List alpha) (select : alpha → Bool)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.any select = right.any select := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨value, member, selected⟩
    exact ⟨value, (sameMembers value).mp member, selected⟩
  · rintro ⟨value, member, selected⟩
    exact ⟨value, (sameMembers value).mpr member, selected⟩

private theorem rawRecognizesBool_eq_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (symbol : NonterminalSymbol) (start finish : Boundary tokens) :
    rawRecognizesBool phaseA symbol start finish =
      saturatedRawRecognizesBool tokens symbol start finish := by
  unfold rawRecognizesBool saturatedRawRecognizesBool
  apply list_any_eq_of_mem_iff
  simpa only [SaturatedRawItem] using sameMembers

/-- A saturated Phase-A item carrier computes the canonical greatest-end
observation. -/
private theorem rawGreatestEndBool_eq_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) :
    rawGreatestEndBool phaseA symbol start upperBound finish =
      saturatedRawGreatestEndObservation tokens symbol start
        upperBound finish := by
  have recognizesEq : ∀ candidate,
      rawRecognizesBool phaseA symbol start candidate =
        saturatedRawRecognizesBool tokens symbol start candidate :=
    fun candidate => rawRecognizesBool_eq_saturated phaseA sameMembers
      symbol start candidate
  simp only [rawGreatestEndBool, saturatedRawGreatestEndObservation,
    recognizesEq]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- A finalized memo operationally enables one production instance when
every guarded cell has an exact structural anchor and an accepting stored
decision.  This predicate is independent of declarative guard evidence. -/
def MemoEnablesProduction
    {tokens : List Token}
    (memo : GuardMemo tokens)
    (productionInstance : ProductionInstanceKey tokens) : Prop :=
  ∀ guard polarity,
    (guard, polarity) ∈ guardOf productionInstance.production →
      ∃ guardInstance decision,
        GuardAnchor productionInstance (guard, polarity) guardInstance ∧
          memo guardInstance = .final decision ∧
          decision.allows polarity = true

/-- The least contextual relation generated by the actual worklist rules,
with guard acceptance stated only in terms of the stored memo. -/
inductive OperationalContextualReach
    (file : WorkspaceFile)
    (tokens : List Token)
    (memo : GuardMemo tokens) :
    ContextualItemKey tokens → Prop where
  | root :
      OperationalContextualReach file tokens memo {
        raw := {
          production := .root .module
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := Boundary.start tokens
          current := Boundary.start tokens
        }
        context := .plain
      }
  | predict
      (waiting : ContextualItemKey tokens)
      (predicted : ProductionId)
      (reached : OperationalContextualReach file tokens memo waiting)
      (next : NextSymbol waiting.raw
        (.nonterminal predicted.lhs))
      (enabled : MemoEnablesProduction memo {
        production := predicted
        origin := waiting.raw.current
        context := descendContext waiting predicted
      }) :
      OperationalContextualReach file tokens memo {
        raw := {
          production := predicted
          dot := ⟨0, Nat.zero_lt_succ _⟩
          origin := waiting.raw.current
          current := waiting.raw.current
        }
        context := descendContext waiting predicted
      }
  | scan
      (before after : ContextualItemKey tokens)
      (cursor : TerminalCursor tokens)
      (reached : OperationalContextualReach file tokens memo before)
      (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
        (.scanned before after cursor)) :
      OperationalContextualReach file tokens memo after
  | complete
      (waiting finished after : ContextualItemKey tokens)
      (shared : Boundary tokens)
      (waitingReached :
        OperationalContextualReach file tokens memo waiting)
      (finishedReached :
        OperationalContextualReach file tokens memo finished)
      (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
        (.completed waiting finished after shared)) :
      OperationalContextualReach file tokens memo after

/-- Operational reachability of every endpoint of one checked worklist edge. -/
def OperationalContextualEdgeReach
    (file : WorkspaceFile)
    (tokens : List Token)
    (memo : GuardMemo tokens)
    (key : ContextualPackedEdgeKey tokens) : Prop :=
  ContextualPackedEdgeKey.StructurallyValid file tokens key ∧
    match key with
    | .scanned before after _ =>
        OperationalContextualReach file tokens memo before ∧
          OperationalContextualReach file tokens memo after
    | .completed waiting finished after _ =>
        OperationalContextualReach file tokens memo waiting ∧
          OperationalContextualReach file tokens memo finished ∧
          OperationalContextualReach file tokens memo after

/-- Public proof-free observation of a successful checked contextual drain. -/
structure ContextualWorklistResult
    (file : WorkspaceFile) (tokens : List Token) where
  memo : GuardMemo tokens
  items : List (ContextualItemKey tokens)
  edges : List (StructurallyValidContextualPackedEdge file tokens)

/-- The finite checked edge set assigns one erased completion coordinate to
each retained contextual target.  This says nothing about unretained edges. -/
def RetainedCompletionBackpointersConsistent
    {file : WorkspaceFile} {tokens : List Token}
    (edges : List (StructurallyValidContextualPackedEdge file tokens)) : Prop :=
  ∀ left, left ∈ edges → ∀ right, right ∈ edges →
    match left.val, right.val with
    | .completed _ leftFinished leftAfter leftShared,
        .completed _ rightFinished rightAfter rightShared =>
        leftAfter = rightAfter →
          leftShared = rightShared ∧
            leftFinished.raw.production = rightFinished.raw.production
    | _, _ => True

/-- Run the landed observed A/B/C worklist and expose only its semantic memo,
items, and already checked edge keys.  Failure remains explicit. -/
def executeObservedContextualWorklist?
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    Option (ContextualWorklistResult file tokens) := do
  let result ← executeObservedPhaseABCWorklist? file tokens owned
  pure {
    memo := result.payload.phaseC.memo
    items := result.payload.phaseC.contextualItems
    edges := result.payload.phaseC.contextualEdges
  }

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem guardWitnessFor?_isSome_iff
    {tokens : List Token}
    (memo : GuardMemo tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity) :
    (guardWitnessFor? memo productionInstance cell).isSome = true ↔
      ∃ guardInstance decision,
        GuardAnchor productionInstance cell guardInstance ∧
          memo guardInstance = .final decision ∧
          decision.allows cell.2 = true := by
  unfold guardWitnessFor?
  split
  next anchorEq =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨guardInstance, decision, anchor, _stored, _accepted⟩
      have computed := GuardAnchor.decide_eq_some_iff.mpr anchor
      rw [anchorEq] at computed
      contradiction
  next guardInstance anchorEq =>
      cases memoEq : memo guardInstance with
      | undecided =>
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨other, decision, anchor, stored, _accepted⟩
          have computed := GuardAnchor.decide_eq_some_iff.mpr anchor
          rw [anchorEq] at computed
          have same : other = guardInstance := (Option.some.inj computed).symm
          subst other
          rw [memoEq] at stored
          contradiction
      | final decision =>
          cases acceptedEq : cell.2.accepts decision with
          | false =>
              simp only [acceptedEq, ↓reduceDIte, Option.isSome_none,
                Bool.false_eq_true, false_iff]
              rintro ⟨other, otherDecision, anchor, stored, accepted⟩
              have computed := GuardAnchor.decide_eq_some_iff.mpr anchor
              rw [anchorEq] at computed
              have same : other = guardInstance :=
                (Option.some.inj computed).symm
              subst other
              have decisionEq : otherDecision = decision :=
                GuardMemoState.final.inj (stored.symm.trans memoEq)
              subst otherDecision
              exact Bool.false_ne_true (acceptedEq.symm.trans accepted)
          | true =>
              simp only [acceptedEq, ↓reduceDIte, Option.isSome_some]
              constructor
              · intro _
                exact ⟨guardInstance, decision,
                  GuardAnchor.decide_eq_some_iff.mp anchorEq,
                  memoEq, acceptedEq⟩
              · intro _
                trivial

private structure PhaseCReachCarrier
    (file : WorkspaceFile) (tokens : List Token) where
  memo : GuardMemo tokens
  items : List (ContextualItemKey tokens)
  itemQueue : List (ContextualItemKey tokens)
  edges : List (StructurallyValidContextualPackedEdge file tokens)
  edgeQueue : List (StructurallyValidContextualPackedEdge file tokens)

private def PhaseCOpen.reachCarrier
    {file : WorkspaceFile} {tokens : List Token}
    (state : PhaseCOpen file tokens) : PhaseCReachCarrier file tokens := {
  memo := state.memo
  items := state.contextualItems
  itemQueue := state.itemQueue
  edges := state.contextualEdges
  edgeQueue := state.edgeQueue
}

private theorem processGuardCell?_reachCarrier
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result) :
    result.1.payload.reachCarrier = current.payload.reachCarrier := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  have inspectedPayload := chargeAddresses?_payload
    (preInsertWitnessSlots.map fun slot =>
      .guardWitness slot (guardCellAddress productionInstance index))
    current inspected inspectedEq
  have insertedPayload := runMappedPrimitive?_payload inspected
    (.guardWitness .insertWitness
      (guardCellAddress productionInstance index)) _ insertedEq
  rw [insertedPayload, inspectedPayload]
  split <;> rfl

private theorem processGuardCells?_reachCarrier
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ (indices : List
        (Fin (guardOf productionInstance.production).length))
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
        result.1.payload.reachCarrier = current.payload.reachCarrier := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected
      simp only [processGuardCells?, Option.some.injEq] at selected
      cases selected
      rfl
  | cons index rest induction =>
      intro current result selected
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨processed, processedEq, finished, finishedEq, resultEq⟩
      cases resultEq
      exact (induction processed.1 finished finishedEq).trans
        (processGuardCell?_reachCarrier current productionInstance index
          processed processedEq)

private theorem processGuardCell?_accepted_sound
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result)
    (accepted : result.2 = true) :
    ∃ guardInstance decision,
      GuardAnchor productionInstance
          ((guardOf productionInstance.production).get index)
          guardInstance ∧
        current.payload.memo guardInstance = .final decision ∧
        decision.allows
          ((guardOf productionInstance.production).get index).2 = true := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  exact (guardWitnessFor?_isSome_iff current.payload.memo
    productionInstance
    ((guardOf productionInstance.production).get index)).mp accepted

private theorem processGuardCells?_accepted_sound
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ (indices : List
        (Fin (guardOf productionInstance.production).length))
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
      result.2 = true →
      ∀ index, index ∈ indices →
        ∃ guardInstance decision,
          GuardAnchor productionInstance
              ((guardOf productionInstance.production).get index)
              guardInstance ∧
            current.payload.memo guardInstance = .final decision ∧
            decision.allows
              ((guardOf productionInstance.production).get index).2 = true := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected accepted index member
      simp at member
  | cons head rest induction =>
      intro current result selected accepted index member
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨processed, processedEq, finished, finishedEq, resultEq⟩
      cases resultEq
      have both : processed.2 = true ∧ finished.2 = true :=
        Bool.and_eq_true_iff.mp accepted
      rcases List.mem_cons.mp member with same | inRest
      · subst index
        exact processGuardCell?_accepted_sound current productionInstance
          head processed processedEq both.1
      · have sound := induction processed.1 finished finishedEq both.2
          index inRest
        have carrier := processGuardCell?_reachCarrier current
          productionInstance head processed processedEq
        have memoEq := congrArg PhaseCReachCarrier.memo carrier
        change processed.1.payload.memo = current.payload.memo at memoEq
        rw [memoEq] at sound
        exact sound

private theorem activateProduction?_accepted_sound
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : activateProduction? current productionInstance = some result)
    (accepted : result.2 = true) :
    MemoEnablesProduction current.payload.memo productionInstance := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  intro guard polarity member
  obtain ⟨index, indexValue⟩ := List.get_of_mem member
  have indexMember : index ∈
      List.ofFn (fun index :
        Fin (guardOf productionInstance.production).length => index) :=
    List.mem_ofFn.mpr ⟨index, rfl⟩
  have sound := processGuardCells?_accepted_sound productionInstance _
    attempted result processedEq accepted index indexMember
  have attemptedPayload := runMappedPrimitive?_payload current
    (.production productionInstance) id attemptedEq
  change attempted.payload = current.payload at attemptedPayload
  rw [attemptedPayload] at sound
  simpa only [indexValue] using sound

private theorem activateWorklistProduction?_accepted_sound
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result)
    (accepted : result.2 = true) :
    MemoEnablesProduction current.payload.phaseC.memo productionInstance := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  exact activateProduction?_accepted_sound
    { payload := current.payload.phaseC, counter := current.counter }
    productionInstance activated activatedEq accepted

private theorem activateProduction?_reachCarrier
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : activateProduction? current productionInstance =
      some result) :
    result.1.payload.reachCarrier = current.payload.reachCarrier := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  have processed := processGuardCells?_reachCarrier productionInstance _
    attempted result processedEq
  have attemptedPayload := runMappedPrimitive?_payload current
    (.production productionInstance) id attemptedEq
  change attempted.payload = current.payload at attemptedPayload
  exact processed.trans (congrArg PhaseCOpen.reachCarrier attemptedPayload)

private theorem activateWorklistProduction?_reachCarrier
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    result.1.payload.phaseC.reachCarrier =
      current.payload.phaseC.reachCarrier := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  exact activateProduction?_reachCarrier
    { payload := current.payload.phaseC, counter := current.counter }
    productionInstance activated activatedEq

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseCOperationalInvariant
    (file : WorkspaceFile) (tokens : List Token)
    (state : PhaseCWorklist file tokens) : Prop :=
  (∀ item, item ∈ state.phaseC.contextualItems →
    OperationalContextualReach file tokens state.phaseC.memo item) ∧
  (∀ item, item ∈ state.phaseC.itemQueue →
    OperationalContextualReach file tokens state.phaseC.memo item) ∧
  (∀ edge, edge ∈ state.phaseC.contextualEdges →
    OperationalContextualEdgeReach file tokens state.phaseC.memo edge.val) ∧
  (∀ edge, edge ∈ state.phaseC.edgeQueue →
    OperationalContextualEdgeReach file tokens state.phaseC.memo edge.val)

private theorem PhaseCOperationalInvariant.of_reachCarrier_eq
    {file : WorkspaceFile} {tokens : List Token}
    {before after : PhaseCWorklist file tokens}
    (equal : after.phaseC.reachCarrier = before.phaseC.reachCarrier)
    (invariant : PhaseCOperationalInvariant file tokens before) :
    PhaseCOperationalInvariant file tokens after := by
  have memoEq := congrArg PhaseCReachCarrier.memo equal
  have itemsEq := congrArg PhaseCReachCarrier.items equal
  have itemQueueEq := congrArg PhaseCReachCarrier.itemQueue equal
  have edgesEq := congrArg PhaseCReachCarrier.edges equal
  have edgeQueueEq := congrArg PhaseCReachCarrier.edgeQueue equal
  change after.phaseC.memo = before.phaseC.memo at memoEq
  change after.phaseC.contextualItems =
    before.phaseC.contextualItems at itemsEq
  change after.phaseC.itemQueue = before.phaseC.itemQueue at itemQueueEq
  change after.phaseC.contextualEdges =
    before.phaseC.contextualEdges at edgesEq
  change after.phaseC.edgeQueue = before.phaseC.edgeQueue at edgeQueueEq
  simpa only [PhaseCOperationalInvariant, memoEq, itemsEq, itemQueueEq,
    edgesEq, edgeQueueEq] using invariant

private theorem beginPhaseCWorklist?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : beginPhaseCWorklist? current = some result) :
    PhaseCOperationalInvariant file tokens result.payload := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  have payload := runMappedPrimitive?_payload current
    (.linear .L03_itemInsert (contextualLinearKey (contextualRoot tokens))) _
    enteredEq
  rw [payload]
  constructor
  · intro item member
    simp only [List.mem_singleton] at member
    subst item
    exact OperationalContextualReach.root
  · constructor
    · intro item member
      simp only [List.mem_singleton] at member
      subst item
      exact OperationalContextualReach.root
    · simp

private theorem activateWorklistProduction?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCOperationalInvariant file tokens result.1.payload :=
  invariant.of_reachCarrier_eq
    (activateWorklistProduction?_reachCarrier current productionInstance
      result selected)

private theorem insertContextualItem?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (reached : OperationalContextualReach file tokens
      current.payload.phaseC.memo item)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCOperationalInvariant file tokens result.payload := by
  unfold insertContextualItem? at selected
  split at selected
  · cases selected
    exact invariant
  · rw [runMappedPrimitive?_payload current _ _ selected]
    rcases invariant with ⟨items, queue, edges, edgeQueue⟩
    constructor
    · intro candidate member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with old | equal
      · exact items candidate old
      · subst candidate
        exact reached
    · constructor
      · intro candidate member
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with old | equal
        · exact queue candidate old
        · subst candidate
          exact reached
      · exact ⟨edges, edgeQueue⟩

private theorem insertContextualScannedEdge?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (reached : OperationalContextualEdgeReach file tokens
      current.payload.phaseC.memo
      (.scanned edge.before edge.after edge.cursor))
    (selected : insertContextualScannedEdge? current edge = some result) :
    PhaseCOperationalInvariant file tokens result.payload := by
  unfold insertContextualScannedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    exact invariant
  · rw [runMappedPrimitive?_payload current _ _ selected]
    rcases invariant with ⟨items, queue, edges, edgeQueue⟩
    refine ⟨items, queue, ?_, ?_⟩
    · intro candidate member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with old | equal
      · exact edges candidate old
      · subst candidate
        exact reached
    · intro candidate member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with old | equal
      · exact edgeQueue candidate old
      · subst candidate
        exact reached

private theorem insertContextualCompletedEdge?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (reached : OperationalContextualEdgeReach file tokens
      current.payload.phaseC.memo
      (.completed edge.waiting edge.finished edge.after edge.shared))
    (selected : insertContextualCompletedEdge? current edge = some result) :
    PhaseCOperationalInvariant file tokens result.payload := by
  unfold insertContextualCompletedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    exact invariant
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨pair, insertedEq, chargedEq⟩
    rw [runMappedPrimitive?_payload current _ _ chargedEq]
    unfold CompletionBackpointerLedger.insertCompleted? at insertedEq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at insertedEq
    rcases insertedEq with ⟨ledger, ledgerEq, pairEq⟩
    cases pairEq
    rcases invariant with ⟨items, queue, edges, edgeQueue⟩
    refine ⟨items, queue, ?_, ?_⟩
    · intro candidate member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with old | equal
      · exact edges candidate old
      · subst candidate
        exact reached
    · intro candidate member
      rw [List.mem_append, List.mem_singleton] at member
      rcases member with old | equal
      · exact edgeQueue candidate old
      · subst candidate
        exact reached

private theorem dequeueContextualItem?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (selected : dequeueContextualItem? current = some result) :
    OperationalContextualReach file tokens
        current.payload.phaseC.memo result.1 ∧
      PhaseCOperationalInvariant file tokens result.2.payload := by
  unfold dequeueContextualItem? at selected
  cases queueEq : current.payload.phaseC.itemQueue with
  | nil => simp [queueEq] at selected
  | cons item rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := runMappedPrimitive?_payload current
        (.linear .L01_itemDequeue (contextualLinearKey item)) _ nextEq
      constructor
      · exact invariant.2.1 item (by simp [queueEq])
      · rw [payload]
        refine ⟨invariant.1, ?_, invariant.2.2.1, ?_⟩
        · intro candidate member
          exact invariant.2.1 candidate (by simp [queueEq, member])
        · exact invariant.2.2.2

private theorem dequeueContextualEdge?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (selected : dequeueContextualEdge? current = some result) :
    PhaseCOperationalInvariant file tokens result.2.payload := by
  unfold dequeueContextualEdge? at selected
  cases queueEq : current.payload.phaseC.edgeQueue with
  | nil => simp [queueEq] at selected
  | cons edge rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := runMappedPrimitive?_payload current _ _ nextEq
      rw [payload]
      refine ⟨invariant.1, invariant.2.1, invariant.2.2.1, ?_⟩
      intro candidate member
      exact invariant.2.2.2 candidate (by simp [queueEq, member])

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem contextualPredictedItem?_operational
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (waiting item : ContextualItemKey tokens)
    (predicted : ProductionId)
    (productionInstance : ProductionInstanceKey tokens)
    (waitingReached : OperationalContextualReach file tokens
      memo waiting)
    (enabled : MemoEnablesProduction memo productionInstance)
    (selected : contextualPredictedItem? waiting predicted =
      some (item, productionInstance)) :
    OperationalContextualReach file tokens memo item := by
  unfold contextualPredictedItem? at selected
  split at selected
  next symbol nextEq =>
    split at selected
    next sameLhs =>
      cases selected
      apply OperationalContextualReach.predict waiting predicted
        waitingReached
      · rcases List.getElem?_eq_some_iff.mp nextEq with
          ⟨bound, lookup⟩
        exact ⟨bound, by simpa [sameLhs] using nextEq⟩
      · exact enabled
    next different => contradiction
  next => contradiction

private theorem insertContextualItem?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (selected : insertContextualItem? current source item = some result) :
    result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold insertContextualItem? at selected
  split at selected
  · cases selected
    rfl
  · rw [runMappedPrimitive?_payload current _ _ selected]

private theorem attemptContextualPrediction?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (waitingReached : OperationalContextualReach file tokens
      current.payload.phaseC.memo waiting)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    PhaseCOperationalInvariant file tokens result.payload ∧
      result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold attemptContextualPrediction? at selected
  cases predictedEq : contextualPredictedItem? waiting predicted with
  | none =>
      simp only [predictedEq, Option.some.injEq] at selected
      cases selected
      exact ⟨invariant, rfl⟩
  | some pair =>
      rcases pair with ⟨item, productionInstance⟩
      simp only [predictedEq] at selected
      cases attemptedEq : runMappedPrimitive? current
          (.prediction .R01_predictionAttempt
            (contextualPredictionKey waiting predicted)) id with
      | none => simp [attemptedEq] at selected
      | some attempted =>
          have attemptedPayload := runMappedPrimitive?_payload current _ id
            attemptedEq
          change attempted.payload = current.payload at attemptedPayload
          have attemptedInvariant :
              PhaseCOperationalInvariant file tokens attempted.payload := by
            rw [attemptedPayload]
            exact invariant
          have waitingAttempted : OperationalContextualReach file tokens
              attempted.payload.phaseC.memo waiting := by
            rw [attemptedPayload]
            exact waitingReached
          by_cases used : (UnitAddress.production productionInstance) ∈
              attempted.counter.usedRev
          · simp [attemptedEq, used] at selected
            cases selected
            refine ⟨attemptedInvariant, ?_⟩
            rw [attemptedPayload]
          · cases activatedEq :
                activateWorklistProduction? attempted productionInstance with
            | none => simp [attemptedEq, used, activatedEq] at selected
            | some activated =>
                have activatedInvariant :=
                  activateWorklistProduction?_operationalInvariant attempted
                    productionInstance activated attemptedInvariant activatedEq
                cases acceptedEq : activated.2
                · simp [attemptedEq, used, activatedEq, acceptedEq]
                    at selected
                  cases selected
                  refine ⟨activatedInvariant, ?_⟩
                  have carrier := activateWorklistProduction?_reachCarrier
                    attempted productionInstance activated activatedEq
                  have memoEq := congrArg PhaseCReachCarrier.memo carrier
                  change activated.1.payload.phaseC.memo =
                    attempted.payload.phaseC.memo at memoEq
                  exact memoEq.trans (by rw [attemptedPayload])
                · simp [attemptedEq, used, activatedEq, acceptedEq]
                    at selected
                  have enabled :=
                    activateWorklistProduction?_accepted_sound attempted
                      productionInstance activated activatedEq acceptedEq
                  have itemReached := contextualPredictedItem?_operational
                    waiting item predicted productionInstance waitingAttempted
                      enabled predictedEq
                  have carrier := activateWorklistProduction?_reachCarrier
                    attempted productionInstance activated activatedEq
                  have memoEq := congrArg PhaseCReachCarrier.memo carrier
                  change activated.1.payload.phaseC.memo =
                    attempted.payload.phaseC.memo at memoEq
                  have itemReachedActivated :
                      OperationalContextualReach file tokens
                        activated.1.payload.phaseC.memo item := by
                    rw [memoEq]
                    exact itemReached
                  refine ⟨insertContextualItem?_operationalInvariant
                    activated.1 result .prediction item activatedInvariant
                    itemReachedActivated selected, ?_⟩
                  have insertedMemo := insertContextualItem?_memo
                    activated.1 result .prediction item selected
                  exact insertedMemo.trans (memoEq.trans (by
                    rw [attemptedPayload]))

private theorem attemptContextualPredictions?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    ∀ (productions : List ProductionId)
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCOperationalInvariant file tokens current.payload →
      OperationalContextualReach file tokens
        current.payload.phaseC.memo waiting →
      attemptContextualPredictions? waiting productions current = some result →
      PhaseCOperationalInvariant file tokens result.payload ∧
        result.payload.phaseC.memo = current.payload.phaseC.memo := by
  intro productions
  induction productions with
  | nil =>
      intro current result invariant _ selected
      cases selected
      exact ⟨invariant, rfl⟩
  | cons predicted rest induction =>
      intro current result invariant waitingReached selected
      rw [attemptContextualPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, restEq⟩
      have nextSound :=
        attemptContextualPrediction?_operationalInvariant current next
          waiting predicted invariant waitingReached nextEq
      have restSound := induction next result nextSound.1
        (by rw [nextSound.2]; exact waitingReached) restEq
      exact ⟨restSound.1, restSound.2.trans nextSound.2⟩

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

private theorem contextualScannedEdge?_operational
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (beforeReached : OperationalContextualReach file tokens memo before)
    (selected : contextualScannedEdge? owned before = some (after, edge)) :
    OperationalContextualReach file tokens memo after ∧
      OperationalContextualEdgeReach file tokens memo
        (.scanned edge.before edge.after edge.cursor) := by
  unfold contextualScannedEdge? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  simp only at selected
  split at selected <;> try contradiction
  next matched matchEq =>
    have pairEq := Option.some.inj selected
    have beforeEq : before = edge.before := by
      simpa only using congrArg (fun pair => pair.2.before) pairEq
    have generatedAfterEq : after = edge.after := by
      have first := congrArg (fun pair => pair.1) pairEq
      have second := congrArg (fun pair => pair.2.after) pairEq
      exact first.symm.trans second
    have beforeEdgeReached : OperationalContextualReach file tokens memo
        edge.before := by
      rw [← beforeEq]
      exact beforeReached
    have afterEdgeReached := OperationalContextualReach.scan edge.before
      edge.after edge.cursor beforeEdgeReached edge.structural
    have afterReached : OperationalContextualReach file tokens memo after := by
      rw [generatedAfterEq]
      exact afterEdgeReached
    exact ⟨afterReached, edge.structural, beforeEdgeReached,
      afterEdgeReached⟩

private theorem insertContextualScannedEdge?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (selected : insertContextualScannedEdge? current edge = some result) :
    result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold insertContextualScannedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    rfl
  · rw [runMappedPrimitive?_payload current _ _ selected]

private theorem attemptContextualScan?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (beforeReached : OperationalContextualReach file tokens
      current.payload.phaseC.memo before)
    (selected : attemptContextualScan? owned current before = some result) :
    PhaseCOperationalInvariant file tokens result.payload ∧
      result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold attemptContextualScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedPayload := runMappedPrimitive?_payload current _ id
      attemptedEq
    change attempted.payload = current.payload at attemptedPayload
    have attemptedInvariant :
        PhaseCOperationalInvariant file tokens attempted.payload := by
      rw [attemptedPayload]
      exact invariant
    have beforeAttempted : OperationalContextualReach file tokens
        attempted.payload.phaseC.memo before := by
      rw [attemptedPayload]
      exact beforeReached
    cases scanEq : contextualScannedEdge? owned before with
    | none =>
        simp only [scanEq, Option.some.injEq] at remainder
        cases remainder
        refine ⟨attemptedInvariant, ?_⟩
        rw [attemptedPayload]
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scanEq, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have edgeReached := contextualScannedEdge?_operational owned
          before after edge beforeAttempted scanEq
        have itemInvariant := insertContextualItem?_operationalInvariant
          attempted withItem .scan after attemptedInvariant edgeReached.1 itemEq
        have itemMemo := insertContextualItem?_memo attempted withItem .scan
          after itemEq
        have edgeReachedWithItem : OperationalContextualEdgeReach file tokens
            withItem.payload.phaseC.memo
            (.scanned edge.before edge.after edge.cursor) := by
          rw [itemMemo]
          exact edgeReached.2
        refine ⟨insertContextualScannedEdge?_operationalInvariant
          withItem result edge itemInvariant edgeReachedWithItem edgeEq, ?_⟩
        exact (insertContextualScannedEdge?_memo withItem result edge edgeEq).trans
          (itemMemo.trans (by rw [attemptedPayload]))
  next notApplicable =>
    cases selected
    exact ⟨invariant, rfl⟩

private theorem contextualCompletedEdge?_operational
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    (waiting finished after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (waitingReached : OperationalContextualReach file tokens memo waiting)
    (finishedReached : OperationalContextualReach file tokens memo finished)
    (selected : contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge)) :
    OperationalContextualReach file tokens memo after ∧
      OperationalContextualEdgeReach file tokens memo
        (.completed edge.waiting edge.finished edge.after edge.shared) := by
  unfold contextualCompletedEdge? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  next sameContext =>
    have pairEq := Option.some.inj selected
    have waitingEq : waiting = edge.waiting := by
      simpa only using congrArg (fun pair => pair.2.waiting) pairEq
    have finishedEq : finished = edge.finished := by
      simpa only using congrArg (fun pair => pair.2.finished) pairEq
    have generatedAfterEq : after = edge.after := by
      have first := congrArg (fun pair => pair.1) pairEq
      have second := congrArg (fun pair => pair.2.after) pairEq
      exact first.symm.trans second
    have waitingEdgeReached : OperationalContextualReach file tokens memo
        edge.waiting := by
      rw [← waitingEq]
      exact waitingReached
    have finishedEdgeReached : OperationalContextualReach file tokens memo
        edge.finished := by
      rw [← finishedEq]
      exact finishedReached
    have afterEdgeReached := OperationalContextualReach.complete edge.waiting
      edge.finished edge.after edge.shared waitingEdgeReached
        finishedEdgeReached edge.structural
    have afterReached : OperationalContextualReach file tokens memo after := by
      rw [generatedAfterEq]
      exact afterEdgeReached
    exact ⟨afterReached, edge.structural, waitingEdgeReached,
      finishedEdgeReached, afterEdgeReached⟩

private theorem insertContextualCompletedEdge?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : insertContextualCompletedEdge? current edge = some result) :
    result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold insertContextualCompletedEdge? at selected
  simp only at selected
  split at selected
  · cases selected
    rfl
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨pair, insertedEq, chargedEq⟩
    rw [runMappedPrimitive?_payload current _ _ chargedEq]

private theorem attemptContextualCompletion?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished : ContextualItemKey tokens)
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (waitingReached : OperationalContextualReach file tokens
      current.payload.phaseC.memo waiting)
    (finishedReached : OperationalContextualReach file tokens
      current.payload.phaseC.memo finished)
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    PhaseCOperationalInvariant file tokens result.payload ∧
      result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold attemptContextualCompletion? at selected
  cases completionEq : contextualCompletedEdge?
      (file := file) waiting finished with
  | none =>
      simp only [completionEq, Option.some.injEq] at selected
      cases selected
      exact ⟨invariant, rfl⟩
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completionEq] at selected
      split at selected
      next attemptedBefore =>
        cases selected
        exact ⟨invariant, rfl⟩
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with
          ⟨attempted, attemptedEq, withItem, itemEq, edgeEq⟩
        have attemptedPayload := runMappedPrimitive?_payload current _ id
          attemptedEq
        change attempted.payload = current.payload at attemptedPayload
        have attemptedInvariant :
            PhaseCOperationalInvariant file tokens attempted.payload := by
          rw [attemptedPayload]
          exact invariant
        have waitingAttempted : OperationalContextualReach file tokens
            attempted.payload.phaseC.memo waiting := by
          rw [attemptedPayload]
          exact waitingReached
        have finishedAttempted : OperationalContextualReach file tokens
            attempted.payload.phaseC.memo finished := by
          rw [attemptedPayload]
          exact finishedReached
        have edgeReached := contextualCompletedEdge?_operational waiting
          finished after edge waitingAttempted finishedAttempted completionEq
        have itemInvariant := insertContextualItem?_operationalInvariant
          attempted withItem .completion after attemptedInvariant
            edgeReached.1 itemEq
        have itemMemo := insertContextualItem?_memo attempted withItem
          .completion after itemEq
        have edgeReachedWithItem : OperationalContextualEdgeReach file tokens
            withItem.payload.phaseC.memo
            (.completed edge.waiting edge.finished edge.after edge.shared) := by
          rw [itemMemo]
          exact edgeReached.2
        refine ⟨insertContextualCompletedEdge?_operationalInvariant
          withItem result edge itemInvariant edgeReachedWithItem edgeEq, ?_⟩
        exact (insertContextualCompletedEdge?_memo withItem result edge edgeEq).trans
          (itemMemo.trans (by rw [attemptedPayload]))

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

private theorem attemptContextualCompletionsWith?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    ∀ (others : List (ContextualItemKey tokens))
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCOperationalInvariant file tokens current.payload →
      OperationalContextualReach file tokens
        current.payload.phaseC.memo pivot →
      (∀ other, other ∈ others →
        OperationalContextualReach file tokens
          current.payload.phaseC.memo other) →
      attemptContextualCompletionsWith? pivot others current = some result →
      PhaseCOperationalInvariant file tokens result.payload ∧
        result.payload.phaseC.memo = current.payload.phaseC.memo := by
  intro others
  induction others with
  | nil =>
      intro current result invariant _ _ selected
      cases selected
      exact ⟨invariant, rfl⟩
  | cons other rest induction =>
      intro current result invariant pivotReached othersReached selected
      rw [attemptContextualCompletionsWith?] at selected
      cases forwardEq : attemptContextualCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have otherReached := othersReached other (by simp)
          have forwardSound :=
            attemptContextualCompletion?_operationalInvariant current forward
              pivot other invariant pivotReached otherReached forwardEq
          split at selected
          next same =>
            have restSound := induction forward result forwardSound.1
              (by rw [forwardSound.2]; exact pivotReached)
              (fun item member => by
                rw [forwardSound.2]
                exact othersReached item (by simp [member])) selected
            exact ⟨restSound.1, restSound.2.trans forwardSound.2⟩
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq : attemptContextualCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                have reverseSound :=
                  attemptContextualCompletion?_operationalInvariant forward
                    reverse other pivot forwardSound.1
                    (by rw [forwardSound.2]; exact otherReached)
                    (by rw [forwardSound.2]; exact pivotReached) reverseEq
                have restSound := induction reverse result reverseSound.1
                  (by rw [reverseSound.2, forwardSound.2]; exact pivotReached)
                  (fun item member => by
                    rw [reverseSound.2, forwardSound.2]
                    exact othersReached item (by simp [member])) selected
                exact ⟨restSound.1,
                  restSound.2.trans (reverseSound.2.trans forwardSound.2)⟩

private theorem dequeueContextualItem?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (selected : dequeueContextualItem? current = some result) :
    result.2.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold dequeueContextualItem? at selected
  cases queueEq : current.payload.phaseC.itemQueue with
  | nil => simp [queueEq] at selected
  | cons item rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      rw [runMappedPrimitive?_payload current _ _ nextEq]

private theorem dequeueContextualEdge?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (selected : dequeueContextualEdge? current = some result) :
    result.2.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold dequeueContextualEdge? at selected
  cases queueEq : current.payload.phaseC.edgeQueue with
  | nil => simp [queueEq] at selected
  | cons edge rest =>
      simp only [queueEq, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      rw [runMappedPrimitive?_payload current _ _ nextEq]

private theorem processContextualItem?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (invariant : PhaseCOperationalInvariant file tokens current.payload)
    (itemReached : OperationalContextualReach file tokens
      current.payload.phaseC.memo item)
    (selected : processContextualItem? owned item current = some result) :
    PhaseCOperationalInvariant file tokens result.payload ∧
      result.payload.phaseC.memo = current.payload.phaseC.memo := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predicted, predictedEq, scanned, scannedEq, completedEq⟩
  have predictedSound :=
    attemptContextualPredictions?_operationalInvariant item allProductionIds
      current predicted invariant itemReached predictedEq
  have itemPredicted : OperationalContextualReach file tokens
      predicted.payload.phaseC.memo item := by
    rw [predictedSound.2]
    exact itemReached
  have scannedSound := attemptContextualScan?_operationalInvariant owned
    predicted scanned item predictedSound.1 itemPredicted scannedEq
  have itemScanned : OperationalContextualReach file tokens
      scanned.payload.phaseC.memo item := by
    rw [scannedSound.2, predictedSound.2]
    exact itemReached
  have completedSound :=
    attemptContextualCompletionsWith?_operationalInvariant item
      scanned.payload.phaseC.contextualItems scanned result scannedSound.1
      itemScanned scannedSound.1.1 completedEq
  exact ⟨completedSound.1,
    completedSound.2.trans (scannedSound.2.trans predictedSound.2)⟩

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

private theorem runPhaseCQueues?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel (current result :
      CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCOperationalInvariant file tokens current.payload →
      runPhaseCQueues? owned fuel current = some result →
      PhaseCOperationalInvariant file tokens result.payload ∧
        result.payload.phaseC.memo = current.payload.phaseC.memo := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runPhaseCQueues?] at selected
      split at selected
      · cases selected
        exact ⟨invariant, rfl⟩
      · contradiction
  | succ previous induction =>
      intro current result invariant selected
      rw [runPhaseCQueues?] at selected
      cases itemsEq : current.payload.phaseC.itemQueue with
      | nil =>
          cases edgesEq : current.payload.phaseC.edgeQueue with
          | nil =>
              simp only [itemsEq, edgesEq] at selected
              cases selected
              exact ⟨invariant, rfl⟩
          | cons edge rest =>
              simp only [itemsEq, edgesEq] at selected
              cases dequeuedEq : dequeueContextualEdge? current with
              | none => simp [dequeuedEq] at selected
              | some dequeued =>
                  rw [dequeuedEq] at selected
                  have dequeuedInvariant :=
                    dequeueContextualEdge?_operationalInvariant current
                      dequeued invariant dequeuedEq
                  have restSound := induction dequeued.2 result
                    dequeuedInvariant selected
                  exact ⟨restSound.1, restSound.2.trans
                    (dequeueContextualEdge?_memo current dequeued dequeuedEq)⟩
      | cons item rest =>
          simp only [itemsEq] at selected
          cases dequeuedEq : dequeueContextualItem? current with
          | none => simp [dequeuedEq] at selected
          | some dequeued =>
              rw [dequeuedEq] at selected
              rcases dequeued with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processedEq :
                  processContextualItem? owned pivot afterDequeue with
              | none => simp [processedEq] at selected
              | some processed =>
                  rw [processedEq] at selected
                  have dequeuedSound :=
                    dequeueContextualItem?_operationalInvariant current
                      (pivot, afterDequeue) invariant dequeuedEq
                  have dequeuedMemo := dequeueContextualItem?_memo current
                    (pivot, afterDequeue) dequeuedEq
                  have pivotReached : OperationalContextualReach file tokens
                      afterDequeue.payload.phaseC.memo pivot := by
                    rw [dequeuedMemo]
                    exact dequeuedSound.1
                  have processedSound :=
                    processContextualItem?_operationalInvariant owned pivot
                      afterDequeue processed dequeuedSound.2 pivotReached
                        processedEq
                  have restSound := induction processed result
                    processedSound.1 selected
                  exact ⟨restSound.1, restSound.2.trans
                    (processedSound.2.trans dequeuedMemo)⟩

private theorem beginPhaseCWorklist?_memo
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : beginPhaseCWorklist? current = some result) :
    result.payload.phaseC.memo = current.payload.memo := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  rw [runMappedPrimitive?_payload current _ _ enteredEq]

private theorem executePhaseCWorklist?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executePhaseCWorklist? owned current = some result) :
    PhaseCOperationalInvariant file tokens result.payload ∧
      result.payload.phaseC.memo = current.payload.memo := by
  unfold executePhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, runEq⟩
  have runSound := runPhaseCQueues?_operationalInvariant owned
    (chartGBound (tokens.length + 1)) entered result
      (beginPhaseCWorklist?_operationalInvariant current entered enteredEq)
      runEq
  exact ⟨runSound.1,
    runSound.2.trans (beginPhaseCWorklist?_memo current entered enteredEq)⟩

private theorem executeObservedPhaseABCWorklist?_operationalInvariant
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    PhaseCOperationalInvariant file tokens result.payload := by
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, _phaseBEq, phaseCEq⟩
  exact (executePhaseCWorklist?_operationalInvariant owned phaseB result
    phaseCEq).1

private theorem executeObservedPhaseABCWorklist?_allFinal
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    AllGuardsFinal result.payload.phaseC.memo := by
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, phaseBEq, phaseCEq⟩
  have final := executeObservedPhaseAB?_allFinal file tokens owned phaseB
    phaseBEq
  have memoEq := (executePhaseCWorklist?_operationalInvariant owned phaseB
    result phaseCEq).2
  rw [memoEq]
  exact final

/-- Every item and checked edge exposed by a successful observed contextual
worklist execution is operationally reachable under its returned memo. -/
theorem executeObservedContextualWorklist?_operational_sound
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : ContextualWorklistResult file tokens)
    (selected : executeObservedContextualWorklist? file tokens owned =
      some result) :
    (∀ item, item ∈ result.items →
      OperationalContextualReach file tokens result.memo item) ∧
    (∀ edge, edge ∈ result.edges →
      OperationalContextualEdgeReach file tokens result.memo edge.val) := by
  unfold executeObservedContextualWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  have invariant :=
    executeObservedPhaseABCWorklist?_operationalInvariant file tokens owned
      internal internalEq
  exact ⟨invariant.1, invariant.2.2.1⟩

/-- A successful observed contextual worklist always exposes a fully sealed
guard memo. -/
theorem executeObservedContextualWorklist?_allGuardsFinal
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : ContextualWorklistResult file tokens)
    (selected : executeObservedContextualWorklist? file tokens owned =
      some result) :
    AllGuardsFinal result.memo := by
  unfold executeObservedContextualWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  exact executeObservedPhaseABCWorklist?_allFinal file tokens owned internal
    internalEq

private theorem PhaseCBackpointerInvariant.retainedConsistent
    {file : WorkspaceFile} {tokens : List Token}
    {state : PhaseCWorklist file tokens}
    (invariant : PhaseCBackpointerInvariant file tokens state) :
    RetainedCompletionBackpointersConsistent
      state.phaseC.contextualEdges := by
  intro left leftMember right rightMember
  unfold PhaseCBackpointerInvariant at invariant
  have leftCovered := invariant left leftMember
  have rightCovered := invariant right rightMember
  cases leftKey : left.val <;> cases rightKey : right.val
  all_goals simp only [leftKey, rightKey] at leftCovered rightCovered ⊢
  intro afterEq
  unfold CompletionBackpointerLedger.CoversCompleted at leftCovered rightCovered
  rw [afterEq] at leftCovered
  have coordinates := Option.some.inj (leftCovered.symm.trans rightCovered)
  exact ⟨congrArg Prod.fst coordinates,
    congrArg Prod.snd coordinates⟩

/-- The executable ledger is single-valued on every completed edge retained
by a successful observed contextual worklist. -/
theorem executeObservedContextualWorklist?_retainedBackpointersConsistent
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : ContextualWorklistResult file tokens)
    (selected : executeObservedContextualWorklist? file tokens owned =
      some result) :
    RetainedCompletionBackpointersConsistent result.edges := by
  unfold executeObservedContextualWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  exact (executeObservedPhaseABCWorklist?_backpointerInvariant
    file tokens owned internal internalEq).retainedConsistent

end Chart


namespace Chart

open Grammar
open Solcore.Workspace

/-- The extensional closure that a drained Phase-C worklist must establish.
It deliberately says nothing about fuel or address freshness: those are the
operational obligations needed to prove this interface for the executor. -/
structure OperationalContextualClosure
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (items : List (ContextualItemKey tokens))
    (edges : List (StructurallyValidContextualPackedEdge file tokens)) :
    Prop where
  root_mem :
    ({
      raw := {
        production := .root .module
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := Boundary.start tokens
        current := Boundary.start tokens
      }
      context := .plain
    } : ContextualItemKey tokens) ∈ items
  predict_mem :
    ∀ (waiting : ContextualItemKey tokens) (predicted : ProductionId),
      waiting ∈ items →
      ∀ (_next : NextSymbol waiting.raw (.nonterminal predicted.lhs)),
        MemoEnablesProduction memo {
          production := predicted
          origin := waiting.raw.current
          context := descendContext waiting predicted
        } →
        ({
          raw := {
            production := predicted
            dot := ⟨0, Nat.zero_lt_succ _⟩
            origin := waiting.raw.current
            current := waiting.raw.current
          }
          context := descendContext waiting predicted
        } : ContextualItemKey tokens) ∈ items
  scan_closed :
    ∀ (before after : ContextualItemKey tokens)
        (cursor : TerminalCursor tokens),
      before ∈ items →
      ContextualPackedEdgeKey.StructurallyValid file tokens
        (.scanned before after cursor) →
      after ∈ items ∧
        ∃ retained, retained ∈ edges ∧
          retained.val = .scanned before after cursor
  complete_closed :
    ∀ (waiting finished after : ContextualItemKey tokens)
        (shared : Boundary tokens),
      waiting ∈ items → finished ∈ items →
      ContextualPackedEdgeKey.StructurallyValid file tokens
        (.completed waiting finished after shared) →
      after ∈ items ∧
        ∃ retained, retained ∈ edges ∧
          retained.val = .completed waiting finished after shared

/-- Extensional closure contains the least operational item relation. -/
theorem OperationalContextualClosure.reach_complete
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {items : List (ContextualItemKey tokens)}
    {edges : List (StructurallyValidContextualPackedEdge file tokens)}
    (closed : OperationalContextualClosure file tokens memo items edges)
    {item : ContextualItemKey tokens}
    (reached : OperationalContextualReach file tokens memo item) :
    item ∈ items := by
  induction reached with
  | root => exact closed.root_mem
  | predict waiting predicted _ next enabled waitingInduction =>
      exact closed.predict_mem waiting predicted waitingInduction next enabled
  | scan before after cursor _ structural beforeInduction =>
      exact (closed.scan_closed before after cursor beforeInduction
        structural).1
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      exact (closed.complete_closed waiting finished after shared
        waitingInduction finishedInduction structural).1

/-- Extensional closure retains every operationally reachable checked edge. -/
theorem OperationalContextualClosure.edge_complete
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {items : List (ContextualItemKey tokens)}
    {edges : List (StructurallyValidContextualPackedEdge file tokens)}
    (closed : OperationalContextualClosure file tokens memo items edges)
    {key : ContextualPackedEdgeKey tokens}
    (reached : OperationalContextualEdgeReach file tokens memo key) :
    ∃ retained, retained ∈ edges ∧ retained.val = key := by
  rcases reached with ⟨structural, endpoints⟩
  cases key with
  | scanned before after cursor =>
      exact (closed.scan_closed before after cursor
        (closed.reach_complete endpoints.1) structural).2
  | completed waiting finished after shared =>
      exact (closed.complete_closed waiting finished after shared
        (closed.reach_complete endpoints.1)
        (closed.reach_complete endpoints.2.1) structural).2

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Every successful Phase-A worklist computes the canonical saturated
greatest-end observation. -/
private theorem executePhaseA?_rawGreatestEndBool_eq_saturated
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseAOpen file tokens))
    (selected : executePhaseA? file tokens owned = some result)
    (symbol : NonterminalSymbol)
    (start upperBound finish : Boundary tokens) :
    rawGreatestEndBool result.payload symbol start upperBound finish =
      saturatedRawGreatestEndObservation tokens symbol start
        upperBound finish := by
  apply rawGreatestEndBool_eq_saturated result.payload
  intro item
  simpa only [SaturatedRawItem] using
    executePhaseA?_membership_eq file tokens owned result selected item

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseBOperationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (state : PhaseBIndexed file tokens) : Prop :=
  state.indexes = entries ∧
    ∀ key, key ∈ state.phaseB.finalizedRev →
      ∃ decision,
        phaseBGuardDecisionFromIndexes? entries key = some decision ∧
          state.phaseB.cells key = some (.final decision)

private theorem enterIndexedPhaseB?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBIndexed file tokens))
    (selected : enterIndexedPhaseB? current = some result) :
    PhaseBOperationalInvariant current.payload.entries result.payload := by
  unfold enterIndexedPhaseB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  constructor
  · rfl
  · intro key member
    have initialized := enterPhaseB?_initializes {
      payload := current.payload.phaseA
      counter := current.counter
    } entered enteredEq
    rw [initialized.2] at member
    contradiction

private theorem finalizeNextIndexedGuard?_operationalShape
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseBIndexed file tokens))
    (selected : finalizeNextIndexedGuard? current = some result) :
    ∃ key decision,
      result.payload.indexes = current.payload.indexes ∧
      phaseBGuardDecisionFromIndexes? current.payload.indexes key =
        some decision ∧
      result.payload.phaseB.finalizedRev =
        key :: current.payload.phaseB.finalizedRev ∧
      ∀ candidate, result.payload.phaseB.cells candidate =
        if candidate = key then some (.final decision)
        else current.payload.phaseB.cells candidate := by
  unfold finalizeNextIndexedGuard? at selected
  cases remaining : current.payload.phaseB.remaining with
  | nil => simp [remaining] at selected
  | cons key rest =>
      simp only [remaining] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨afterInitialize, initialized,
        afterLookups, charged, decision, decided, finalSelected⟩
      have initializePayload := phaseB_runMappedPrimitive?_payload current
        (.guardFinalize .initializeUndecided key)
        (fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            state.phaseB with
            cells := fun candidate =>
              if candidate = key then some .undecided
              else state.phaseB.cells candidate
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)) initialized
      have lookupPayload := phaseB_chargeAddresses?_payload afterInitialize
        (preFinalGuardSlots.map fun slot => .guardFinalize slot key)
        afterLookups charged
      have finalPayload := phaseB_runMappedPrimitive?_payload afterLookups
        (.guardFinalize .writeFinalDecision key)
        (fun (state : PhaseBIndexed file tokens) => ({
          phaseB := {
            phaseA := state.phaseB.phaseA
            cells := fun candidate =>
              if candidate = key then some (.final decision)
              else state.phaseB.cells candidate
            remaining := rest
            finalizedRev := key :: state.phaseB.finalizedRev
          }
          indexes := state.indexes
        } : PhaseBIndexed file tokens)) finalSelected
      refine ⟨key, decision, ?_, ?_, ?_, ?_⟩
      · rw [finalPayload, lookupPayload, initializePayload]
      · rw [lookupPayload, initializePayload] at decided
        exact decided
      · rw [finalPayload, lookupPayload, initializePayload]
      · intro candidate
        rw [finalPayload, lookupPayload, initializePayload]
        by_cases same : candidate = key
        · simp [same]
        · simp [same]

private theorem finalizeNextIndexedGuard?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens))
    (current result : CountedState tokens (PhaseBIndexed file tokens))
    (invariant : PhaseBOperationalInvariant entries current.payload)
    (selected : finalizeNextIndexedGuard? current = some result) :
    PhaseBOperationalInvariant entries result.payload := by
  obtain ⟨key, decision, indexes, decided, finalized, cells⟩ :=
    finalizeNextIndexedGuard?_operationalShape current result selected
  have decidedAtEntries :
      phaseBGuardDecisionFromIndexes? entries key = some decision := by
    rw [← invariant.1]
    exact decided
  constructor
  · exact indexes.trans invariant.1
  · intro candidate member
    rw [finalized, List.mem_cons] at member
    rcases member with same | old
    · subst candidate
      exact ⟨decision, decidedAtEntries, by simp [cells]⟩
    · obtain ⟨oldDecision, oldSelected, oldCell⟩ :=
        invariant.2 candidate old
      by_cases same : candidate = key
      · subst candidate
        have decisionEq : oldDecision = decision := by
          exact Option.some.inj (oldSelected.symm.trans decidedAtEntries)
        subst oldDecision
        exact ⟨decision, decidedAtEntries, by simp [cells]⟩
      · exact ⟨oldDecision, oldSelected, by simp [cells, same, oldCell]⟩

private theorem runIndexedPhaseB?_operationalInvariant
    {file : WorkspaceFile} {tokens : List Token}
    (entries : List (PhaseAEvidenceEntry tokens)) :
    ∀ fuel
      (current result : CountedState tokens (PhaseBIndexed file tokens)),
      PhaseBOperationalInvariant entries current.payload →
      runIndexedPhaseB? fuel current = some result →
      PhaseBOperationalInvariant entries result.payload := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      split at selected
      · cases selected
        exact invariant
      · contradiction
  | succ fuel induction =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      cases remaining : current.payload.phaseB.remaining with
      | nil =>
          simp only [remaining] at selected
          cases selected
          exact invariant
      | cons key rest =>
          simp only [remaining] at selected
          cases finalized : finalizeNextIndexedGuard? current with
          | none => simp [finalized] at selected
          | some next =>
              rw [finalized] at selected
              exact induction next result
                (finalizeNextIndexedGuard?_operationalInvariant entries
                  current next invariant finalized) selected

private theorem sealIndexedPhaseB?_memo_eq_cell
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (selected : sealIndexedPhaseB? current = some result)
    (key : GuardInstanceKey tokens) :
    result.payload.memo key =
      match current.payload.phaseB.cells key with
      | some value => value
      | none => .undecided := by
  unfold sealIndexedPhaseB? sealPhaseB? at selected
  cases remaining : current.payload.phaseB.remaining with
  | cons head tail => simp [remaining] at selected
  | nil =>
      simp only [remaining] at selected
      have payload := phaseB_runMappedPrimitive?_payload {
        payload := current.payload.phaseB
        counter := current.counter
      } (.phase .sealBEnterC) (fun state => ({
        phaseA := state.phaseA
        memo := fun key =>
          match state.cells key with
          | some value => value
          | none => .undecided
        finalizedRev := state.finalizedRev
      } : PhaseBSealed file tokens)) selected
      rw [payload]

/-- Every successfully executed indexed Phase-B cell contains exactly the
decision computed from its immutable materialized Phase-A table. -/
private theorem executeIndexedPhaseB?_memo_from_indexes
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (selected : executeIndexedPhaseB? current = some result)
    (key : GuardInstanceKey tokens) :
    ∃ decision,
      phaseBGuardDecisionFromIndexes? current.payload.entries key =
          some decision ∧
        result.payload.memo key = .final decision := by
  unfold executeIndexedPhaseB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq,
    finalized, runEq, sealedEq⟩
  have enteredOperational :=
    enterIndexedPhaseB?_operationalInvariant current entered enteredEq
  have finalOperational := runIndexedPhaseB?_operationalInvariant
    current.payload.entries (allGuardInstanceKeys tokens).length
    entered finalized enteredOperational runEq
  have enteredCoverage :=
    enterIndexedPhaseB?_invariant current entered enteredEq
  have finalCoverage := runIndexedPhaseB?_invariant
    (allGuardInstanceKeys tokens).length entered finalized
    enteredCoverage runEq
  have remainingEmpty := runIndexedPhaseB?_remaining_empty
    (allGuardInstanceKeys tokens).length entered finalized runEq
  have keyFinalized : key ∈ finalized.payload.phaseB.finalizedRev := by
    rcases finalCoverage.1 key with pending | done
    · rw [remainingEmpty] at pending
      contradiction
    · exact done
  obtain ⟨decision, decided, cell⟩ :=
    finalOperational.2 key keyFinalized
  refine ⟨decision, decided, ?_⟩
  rw [sealIndexedPhaseB?_memo_eq_cell finalized result sealedEq key,
    cell]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- The concrete matching-parenthesis bit computed by U01. -/
abbrev rawMatchingParenthesisObservation
    (tokens : List Token) : MatchingParenthesisObservation tokens :=
  fun openCursor closeCursor =>
    phaseAMatchingDelimiterBool tokens openCursor closeCursor
      .leftParen .rightParen

/-- The concrete first same-depth pattern delimiter bit computed by U01. -/
abbrev rawPatternDelimiterObservation
    (tokens : List Token) : PatternDelimiterObservation tokens :=
  fun start limit =>
    phaseANextSameDepthDelimiterBool tokens start limit {
      head := .comma
      tail := [.rightParen, .fatArrow]
    }

/-- The concrete match-arm header oracle over canonical raw saturation. -/
def saturatedMatchArmHeaderObservation
    (tokens : List Token) : MatchArmHeaderObservation tokens :=
  fun regionStart cursor =>
    decide (regionStart.val ≤ cursor.val) &&
      phaseASameDelimiterDepthBool tokens regionStart cursor &&
      phaseASymbolAtBool cursor .pipe &&
      match phaseABoundaryAt? tokens (cursor.val + 1) with
      | none => false
      | some patternStart =>
          phaseAImmediatelyAfterSymbolBool .pipe cursor patternStart &&
            (List.finRange (tokens.length + 2)).any fun arrowCursor =>
              phaseANextSameDepthDelimiterBool tokens patternStart
                  arrowCursor ⟨.fatArrow, []⟩ &&
                saturatedRawGreatestEndObservation tokens
                  (.aux Grammar.matchArmPatternListSite.site)
                  patternStart arrowCursor arrowCursor

private def saturatedNextArmOrCloseBool
    (tokens : List Token)
    (regionStart closeCursor regionEnd : Boundary tokens) : Bool :=
  decide (regionStart.val ≤ regionEnd.val) &&
    decide (regionEnd.val ≤ closeCursor.val) &&
    phaseASameDelimiterDepthBool tokens regionStart regionEnd &&
    (decide (regionEnd = closeCursor) ||
      saturatedMatchArmHeaderObservation tokens regionStart regionEnd) &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if regionStart.val ≤ earlier.val &&
          earlier.val < regionEnd.val &&
          phaseASameDelimiterDepthBool tokens regionStart earlier then
        !(decide (earlier = closeCursor) ||
          saturatedMatchArmHeaderObservation tokens regionStart earlier)
      else
        true

/-- The concrete nearest statement-region oracle over canonical raw
saturation. -/
def saturatedStatementRegionObservation
    (tokens : List Token) : StatementRegionObservation tokens :=
  fun regionStart regionEnd =>
    let bracedBody :=
      (List.finRange (tokens.length + 2)).any fun openCursor =>
        phaseAImmediatelyAfterSymbolBool .leftBrace openCursor regionStart &&
          phaseAMatchingDelimiterBool tokens openCursor regionEnd
            .leftBrace .rightBrace
    let armBody :=
      (List.finRange (tokens.length + 2)).any fun arrowCursor =>
        phaseAImmediatelyAfterSymbolBool .fatArrow arrowCursor regionStart &&
          (List.finRange (tokens.length + 2)).any fun openCursor =>
            (List.finRange (tokens.length + 2)).any fun closeCursor =>
              phaseAInnermostContainingBraceFrameBool tokens arrowCursor
                  openCursor closeCursor &&
                saturatedNextArmOrCloseBool tokens regionStart
                  closeCursor regionEnd
    bracedBody || armBody

private theorem phaseAArmHeaderBool_eq_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (regionStart cursor : Boundary tokens) :
    phaseAArmHeaderBool phaseA regionStart cursor =
      saturatedMatchArmHeaderObservation tokens regionStart cursor := by
  simp only [phaseAArmHeaderBool, saturatedMatchArmHeaderObservation,
    rawGreatestEndBool_eq_saturated phaseA sameMembers]

private theorem phaseANextArmOrCloseBool_eq_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (regionStart closeCursor regionEnd : Boundary tokens) :
    phaseANextArmOrCloseBool phaseA regionStart closeCursor regionEnd =
      saturatedNextArmOrCloseBool tokens regionStart closeCursor
        regionEnd := by
  simp only [phaseANextArmOrCloseBool, saturatedNextArmOrCloseBool,
    phaseAArmHeaderBool_eq_saturated phaseA sameMembers]

private theorem phaseANearestStatementRegionBool_eq_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (regionStart regionEnd : Boundary tokens) :
    phaseANearestStatementRegionBool phaseA regionStart regionEnd =
      saturatedStatementRegionObservation tokens regionStart regionEnd := by
  simp only [phaseANearestStatementRegionBool,
    saturatedStatementRegionObservation,
    phaseANextArmOrCloseBool_eq_saturated phaseA sameMembers]

/-- The complete positive bit computed from canonical U01 raw observations. -/
def saturatedGuardPositiveObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  match key.guard with
  | .G01_statementIf =>
      statementIfPositiveObservationBool owned
        (rawMatchingParenthesisObservation tokens)
        (saturatedRawGreatestEndObservation tokens) key
  | .G02_matchArmBoundary =>
      matchArmHeaderObservationBool
        (saturatedMatchArmHeaderObservation tokens) key
  | .G03_parameterComptime | .G04_letComptime |
      .G05_typeComptime | .G07_leadingDotArguments =>
      (basicGuardPositiveObservation? owned key).getD false
  | .G06_patternComptime =>
      patternComptimePositiveObservationBool owned
        (rawPatternDelimiterObservation tokens)
        (saturatedRawGreatestEndObservation tokens) key
  | .G08_terminalExpression =>
      terminalExpressionPositiveObservationBool
        (saturatedStatementRegionObservation tokens)
        (saturatedRawGreatestEndObservation tokens) key
  | .G09_genericContext =>
      genericContextPositiveObservationBool owned
        (saturatedRawGreatestEndObservation tokens) key

private def saturatedGuardPipeObservationBool
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (key : GuardInstanceKey tokens) : Bool :=
  match key.guard with
  | .G02_matchArmBoundary => matchArmPipeObservationBool owned key
  | _ => false

/-- Canonical U01 materialization reads exactly the canonical saturated raw
observer, guard by guard. -/
private theorem phaseBGuardObservationFromIndexes?_canonical_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (key : GuardInstanceKey tokens) :
    phaseBGuardObservationFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (saturatedGuardPositiveObservationBool owned key,
        saturatedGuardPipeObservationBool owned key) := by
  cases guardEq : key.guard with
  | G01_statementIf =>
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq,
        rawMatchingParenthesisObservation,
        rawGreatestEndBool_eq_saturated phaseA sameMembers] using
        phaseBGuardObservationFromIndexes?_canonical_G01
          owned phaseA key guardEq
  | G02_matchArmBoundary =>
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq,
        phaseAArmHeaderBool_eq_saturated phaseA sameMembers] using
        phaseBGuardObservationFromIndexes?_canonical_G02
          owned phaseA key guardEq
  | G03_parameterComptime =>
      obtain ⟨observed, selected, basic⟩ :=
        phaseBGuardObservationFromIndexes?_canonical_basic owned phaseA key
          (Or.inl guardEq)
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq, basic] using selected
  | G04_letComptime =>
      obtain ⟨observed, selected, basic⟩ :=
        phaseBGuardObservationFromIndexes?_canonical_basic owned phaseA key
          (Or.inr (Or.inl guardEq))
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq, basic] using selected
  | G05_typeComptime =>
      obtain ⟨observed, selected, basic⟩ :=
        phaseBGuardObservationFromIndexes?_canonical_basic owned phaseA key
          (Or.inr (Or.inr (Or.inl guardEq)))
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq, basic] using selected
  | G06_patternComptime =>
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq,
        rawPatternDelimiterObservation,
        rawGreatestEndBool_eq_saturated phaseA sameMembers] using
        phaseBGuardObservationFromIndexes?_canonical_G06
          owned phaseA key guardEq
  | G07_leadingDotArguments =>
      obtain ⟨observed, selected, basic⟩ :=
        phaseBGuardObservationFromIndexes?_canonical_basic owned phaseA key
          (Or.inr (Or.inr (Or.inr guardEq)))
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq, basic] using selected
  | G08_terminalExpression =>
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq,
        phaseANearestStatementRegionBool_eq_saturated phaseA sameMembers,
        rawGreatestEndBool_eq_saturated phaseA sameMembers] using
        phaseBGuardObservationFromIndexes?_canonical_G08
          owned phaseA key guardEq
  | G09_genericContext =>
      simpa [saturatedGuardPositiveObservationBool,
        saturatedGuardPipeObservationBool, guardEq,
        rawGreatestEndBool_eq_saturated phaseA sameMembers] using
        phaseBGuardObservationFromIndexes?_canonical_G09
          owned phaseA key guardEq

/-- The canonical U01 decision is the public classifier applied to the
canonical saturated raw observations. -/
private theorem phaseBGuardDecisionFromIndexes?_canonical_saturated
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (phaseA : PhaseAOpen file tokens)
    (sameMembers : ∀ item,
      item ∈ phaseA.rawItems ↔ SaturatedRawItem tokens item)
    (key : GuardInstanceKey tokens) :
    phaseBGuardDecisionFromIndexes?
        (canonicalEvidenceEntries
          (phaseAObservationIndexEvaluator owned) phaseA) key =
      some (classifyGuardObservation key.guard
        (saturatedGuardPositiveObservationBool owned key)
        (matchArmPipeObservationBool owned key)) := by
  rw [phaseBGuardDecisionFromIndexes?_eq_classifier,
    phaseBGuardObservationFromIndexes?_canonical_saturated
      owned phaseA sameMembers key]
  cases guardEq : key.guard <;>
    simp [saturatedGuardPipeObservationBool, guardEq,
      classifyGuardObservation]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem indexSaturatedPhaseAWith?_entries_eq_canonical
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : indexSaturatedPhaseAWith? evaluate current = some result) :
    result.payload.entries =
      canonicalEvidenceEntries evaluate current.payload := by
  unfold indexSaturatedPhaseAWith? at selected
  split at selected
  next itemsDone =>
    split at selected
    next edgesDone =>
      split at selected
      next saturated =>
        exact materializeAllPhaseAIndexes?_entries_eq_canonical
          evaluate current result selected
      next notSaturated => contradiction
    next edgesRemain => contradiction
  next itemsRemain => contradiction

private theorem indexSaturatedPhaseACanonicalWith?_entries_eq_canonical
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (selected : indexSaturatedPhaseACanonicalWith? evaluate current =
      some result) :
    ∃ sameMembers :
        canonicalRawItems tokens current.payload.rawItems =
          canonicalRawItems tokens (rawSaturation tokens),
      result.payload.entries = canonicalEvidenceEntries evaluate
        (normalizePhaseARawItems current sameMembers).payload := by
  unfold indexSaturatedPhaseACanonicalWith? at selected
  split at selected
  next sameMembers =>
    exact ⟨sameMembers,
      indexSaturatedPhaseAWith?_entries_eq_canonical evaluate
        (normalizePhaseARawItems current sameMembers) result selected⟩
  next differentMembers => contradiction

/-- The fully-final memo computed from canonical raw U01 observations. -/
def saturatedGuardMemo
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) : GuardMemo tokens :=
  fun key => .final (classifyGuardObservation key.guard
    (saturatedGuardPositiveObservationBool owned key)
    (matchArmPipeObservationBool owned key))

/-- Every successful executable guard worklist returns exactly the canonical
raw-saturation guard memo. -/
theorem executeObservedGuardWorklist?_memo_eq_saturated
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : GuardWorklistResult tokens)
    (selected : executeObservedGuardWorklist? file tokens owned =
      some result) :
    result.memo = saturatedGuardMemo owned := by
  unfold executeObservedGuardWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  unfold executeObservedPhaseAB? at internalEq
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at internalEq
  rcases internalEq with ⟨phaseA, phaseAEq,
    indexed, indexedEq, phaseBEq⟩
  obtain ⟨sameMembers, entriesEq⟩ :=
    indexSaturatedPhaseACanonicalWith?_entries_eq_canonical
      (phaseAObservationIndexEvaluator owned) phaseA indexed indexedEq
  have normalizedMembers : ∀ item,
      item ∈ (normalizePhaseARawItems phaseA sameMembers).payload.rawItems ↔
        SaturatedRawItem tokens item := by
    intro item
    rfl
  funext key
  obtain ⟨decision, decisionEq, memoEq⟩ :=
    executeIndexedPhaseB?_memo_from_indexes indexed internal phaseBEq key
  rw [entriesEq] at decisionEq
  have canonicalEq :=
    phaseBGuardDecisionFromIndexes?_canonical_saturated owned
      (normalizePhaseARawItems phaseA sameMembers).payload
      normalizedMembers key
  have decided : decision = classifyGuardObservation key.guard
      (saturatedGuardPositiveObservationBool owned key)
      (matchArmPipeObservationBool owned key) := by
    exact Option.some.inj (decisionEq.symm.trans canonicalEq)
  change internal.payload.memo key = saturatedGuardMemo owned key
  rw [memoEq, decided]
  rfl

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem contextualItem_eq_of_fields
    {tokens : List Token} {left right : ContextualItemKey tokens}
    (raw : left.raw = right.raw)
    (context : left.context = right.context) : left = right := by
  cases left
  cases right
  simp only at raw context
  cases raw
  cases context
  rfl

/-- A declarative next-symbol premise computes the exact contextual
prediction cell consumed by the worklist. -/
private theorem contextualPredictedItem?_complete
    {tokens : List Token}
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (next : NextSymbol waiting.raw (.nonterminal predicted.lhs)) :
    contextualPredictedItem? waiting predicted = some (({
      raw := {
        production := predicted
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := waiting.raw.current
        current := waiting.raw.current
      }
      context := descendContext waiting predicted
    } : ContextualItemKey tokens), {
      production := predicted
      origin := waiting.raw.current
      context := descendContext waiting predicted
    }) := by
  unfold contextualPredictedItem?
  rw [next.2]
  simp

/-- Every structurally valid contextual scan is reconstructed by the exact
checked scan builder, including its requested endpoint and cursor. -/
private theorem contextualScannedEdge?_complete
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (cursor : TerminalCursor tokens)
    (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
      (.scanned before after cursor)) :
    ∃ edge, contextualScannedEdge? owned before = some (after, edge) ∧
      edge.before = before ∧ edge.after = after ∧ edge.cursor = cursor := by
  obtain ⟨witness⟩ := packedEdge_scanned_valid_iff.mp structural.1
  rcases witness with
    ⟨terminal, matched, sameCursor, next, atCurrent, advance⟩
  change before.raw.dot.val < before.raw.production.rhs.length ∧
    before.raw.production.rhs[before.raw.dot.val]? =
      some (.terminal terminal) at next
  have cursorVal : cursor.val = before.raw.current.val :=
    congrArg Fin.val atCurrent
  have currentInRange : before.raw.current.val < tokens.length + 1 := by
    rw [← cursorVal]
    exact cursor.isLt
  let computedCursor : TerminalCursor tokens :=
    ⟨before.raw.current.val, currentInRange⟩
  have cursorEq : computedCursor = cursor := Fin.ext cursorVal.symm
  have nextGet :
      before.raw.production.rhs[before.raw.dot.val] = .terminal terminal := by
    exact Option.some.inj
      ((List.getElem?_eq_getElem next.1).symm.trans next.2)
  have terminalAt : TerminalAt file tokens computedCursor
      matched.value matched.span := by
    rw [cursorEq, ← sameCursor]
    exact matched.at
  obtain ⟨computedMatched, matchedEq⟩ :=
    MatchedTerminal.atCursor?_complete owned terminal computedCursor
      terminalAt matched.matches
  let expectedRaw : DottedItem tokens := {
    production := before.raw.production
    dot := ⟨before.raw.dot.val + 1, by omega⟩
    origin := before.raw.origin
    current := computedCursor.afterBoundary
  }
  have requestedAdvance : AdvanceItem before.raw
      computedCursor.afterBoundary after.raw := by
    rw [cursorEq, ← sameCursor]
    exact advance
  have expectedRawEq : expectedRaw = after.raw :=
    dottedItem_eq_of_fields
      (by simpa [expectedRaw] using requestedAdvance.1.symm)
      (by simpa [expectedRaw] using requestedAdvance.2.1.symm)
      (by simpa [expectedRaw] using requestedAdvance.2.2.1.symm)
      (by simpa [expectedRaw] using requestedAdvance.2.2.2.symm)
  let expected : ContextualItemKey tokens := {
    raw := expectedRaw
    context := before.context
  }
  have expectedEq : expected = after :=
    contextualItem_eq_of_fields expectedRawEq structural.2
  rw [← expectedEq]
  unfold contextualScannedEdge?
  rw [dif_pos next.1]
  split <;> simp_all [expected, expectedRaw, computedCursor]
  all_goals
    subst_vars
    rw [matchedEq]
    simp

/-- Every structurally valid contextual completion is reconstructed by the
exact checked completion builder, including its erased shared coordinate. -/
private theorem contextualCompletedEdge?_complete
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (shared : Boundary tokens)
    (structural : ContextualPackedEdgeKey.StructurallyValid file tokens
      (.completed waiting finished after shared)) :
    ∃ edge, contextualCompletedEdge? (file := file) waiting finished =
        some (after, edge) ∧
      edge.waiting = waiting ∧ edge.finished = finished ∧
        edge.after = after ∧ edge.shared = shared := by
  obtain ⟨witness⟩ := packedEdge_completed_valid_iff.mp structural.1
  rcases witness with
    ⟨next, complete, waitingAtShared, finishedAtShared, advance⟩
  change waiting.raw.dot.val < waiting.raw.production.rhs.length ∧
    waiting.raw.production.rhs[waiting.raw.dot.val]? =
      some (.nonterminal finished.raw.production.lhs) at next
  change finished.raw.dot.val = finished.raw.production.rhs.length at complete
  have nextGet : waiting.raw.production.rhs[waiting.raw.dot.val] =
      .nonterminal finished.raw.production.lhs := by
    exact Option.some.inj
      ((List.getElem?_eq_getElem next.1).symm.trans next.2)
  have sameCursor : waiting.raw.current = finished.raw.origin :=
    waitingAtShared.trans finishedAtShared.symm
  let expectedRaw : DottedItem tokens := {
    production := waiting.raw.production
    dot := ⟨waiting.raw.dot.val + 1, by omega⟩
    origin := waiting.raw.origin
    current := finished.raw.current
  }
  have expectedRawEq : expectedRaw = after.raw :=
    dottedItem_eq_of_fields
      (by simpa [expectedRaw] using advance.1.symm)
      (by simpa [expectedRaw] using advance.2.1.symm)
      (by simpa [expectedRaw] using advance.2.2.1.symm)
      (by simpa [expectedRaw] using advance.2.2.2.symm)
  let expected : ContextualItemKey tokens := {
    raw := expectedRaw
    context := waiting.context
  }
  have expectedEq : expected = after :=
    contextualItem_eq_of_fields expectedRawEq structural.2.2.symm
  rw [← expectedEq]
  unfold contextualCompletedEdge?
  rw [dif_pos next.1]
  split <;> simp_all [expected, expectedRaw]
  exact ⟨_, ⟨structural.2.1, rfl⟩, rfl, rfl, rfl, rfl⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem processGuardCell?_accepted_complete
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result)
    (enabled : ∃ guardInstance decision,
      GuardAnchor productionInstance
          ((guardOf productionInstance.production).get index)
          guardInstance ∧
        current.payload.memo guardInstance = .final decision ∧
        decision.allows
          ((guardOf productionInstance.production).get index).2 = true) :
    result.2 = true := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  exact (guardWitnessFor?_isSome_iff current.payload.memo
    productionInstance
      ((guardOf productionInstance.production).get index)).mpr enabled

private theorem processGuardCells?_accepted_complete
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ (indices : List
        (Fin (guardOf productionInstance.production).length))
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
      (∀ index, index ∈ indices →
        ∃ guardInstance decision,
          GuardAnchor productionInstance
              ((guardOf productionInstance.production).get index)
              guardInstance ∧
            current.payload.memo guardInstance = .final decision ∧
            decision.allows
              ((guardOf productionInstance.production).get index).2 = true) →
      result.2 = true := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected _enabled
      cases selected
      rfl
  | cons head rest induction =>
      intro current result selected enabled
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨processed, processedEq, finished, finishedEq, resultEq⟩
      cases resultEq
      have headAccepted := processGuardCell?_accepted_complete current
        productionInstance head processed processedEq
          (enabled head (by simp))
      have carrier := processGuardCell?_reachCarrier current
        productionInstance head processed processedEq
      have memoEq := congrArg PhaseCReachCarrier.memo carrier
      change processed.1.payload.memo = current.payload.memo at memoEq
      have restEnabled : ∀ index, index ∈ rest →
          ∃ guardInstance decision,
            GuardAnchor productionInstance
                ((guardOf productionInstance.production).get index)
                guardInstance ∧
              processed.1.payload.memo guardInstance = .final decision ∧
              decision.allows
                ((guardOf productionInstance.production).get index).2 =
                  true := by
        intro index member
        rw [memoEq]
        exact enabled index (by simp [member])
      have restAccepted := induction processed.1 finished finishedEq
        restEnabled
      exact Bool.and_eq_true_iff.mpr ⟨headAccepted, restAccepted⟩

private theorem activateProduction?_accepted_complete
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : activateProduction? current productionInstance = some result)
    (enabled : MemoEnablesProduction current.payload.memo
      productionInstance) :
    result.2 = true := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  apply processGuardCells?_accepted_complete productionInstance
    (List.ofFn fun index :
      Fin (guardOf productionInstance.production).length => index)
    attempted result processedEq
  intro index _member
  have attemptedPayload := runMappedPrimitive?_payload current
    (.production productionInstance) id attemptedEq
  change attempted.payload = current.payload at attemptedPayload
  rw [attemptedPayload]
  rcases cellEq : (guardOf productionInstance.production).get index with
    ⟨guard, polarity⟩
  exact enabled guard polarity (by
    rw [← cellEq]
    exact List.get_mem _ index)

private theorem activateWorklistProduction?_accepted_complete
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result)
    (enabled : MemoEnablesProduction current.payload.phaseC.memo
      productionInstance) :
    result.2 = true := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  exact activateProduction?_accepted_complete {
    payload := current.payload.phaseC
    counter := current.counter
  } productionInstance activated activatedEq enabled

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem phaseCItemMemberBool_true_iff
    {tokens : List Token} (items : List (ContextualItemKey tokens))
    (item : ContextualItemKey tokens) :
    phaseCItemMemberBool items item = true ↔ item ∈ items := by
  simp [phaseCItemMemberBool, List.any_eq_true]

private theorem phaseCEdgeMemberBool_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (edges : List (StructurallyValidContextualPackedEdge file tokens))
    (edge : StructurallyValidContextualPackedEdge file tokens) :
    phaseCEdgeMemberBool edges edge = true ↔
      ∃ candidate, candidate ∈ edges ∧ candidate.val = edge.val := by
  simp [phaseCEdgeMemberBool, List.any_eq_true]

/-- Content grows monotonically between item-processing steps.  Newly
discovered items remain queued until a later dequeue. -/
private structure PhaseCContentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseCWorklist file tokens)) : Prop where
  memo : after.payload.phaseC.memo = before.payload.phaseC.memo
  items : before.payload.phaseC.contextualItems ⊆
    after.payload.phaseC.contextualItems
  itemQueue : before.payload.phaseC.itemQueue ⊆
    after.payload.phaseC.itemQueue
  edges : before.payload.phaseC.contextualEdges ⊆
    after.payload.phaseC.contextualEdges
  newItemsQueued : ∀ item,
    item ∈ after.payload.phaseC.contextualItems →
      item ∈ before.payload.phaseC.contextualItems ∨
        item ∈ after.payload.phaseC.itemQueue

private theorem PhaseCContentGrowth.refl
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens)) :
    PhaseCContentGrowth current current := {
  memo := rfl
  items := fun _ => id
  itemQueue := fun _ => id
  edges := fun _ => id
  newItemsQueued := fun _ member => Or.inl member
}

private theorem PhaseCContentGrowth.trans
    {file : WorkspaceFile} {tokens : List Token}
    {first second third : CountedState tokens (PhaseCWorklist file tokens)}
    (left : PhaseCContentGrowth first second)
    (right : PhaseCContentGrowth second third) :
    PhaseCContentGrowth first third := by
  refine {
    memo := right.memo.trans left.memo
    items := fun item member => right.items (left.items member)
    itemQueue := fun item member => right.itemQueue (left.itemQueue member)
    edges := fun edge member => right.edges (left.edges member)
    newItemsQueued := ?_
  }
  intro item member
  rcases right.newItemsQueued item member with middle | queued
  · rcases left.newItemsQueued item middle with old | queued
    · exact Or.inl old
    · exact Or.inr (right.itemQueue queued)
  · exact Or.inr queued

private theorem PhaseCContentGrowth.of_reachCarrier_eq
    {file : WorkspaceFile} {tokens : List Token}
    (before after : CountedState tokens (PhaseCWorklist file tokens))
    (equal : after.payload.phaseC.reachCarrier =
      before.payload.phaseC.reachCarrier) :
    PhaseCContentGrowth before after := by
  have memo := congrArg PhaseCReachCarrier.memo equal
  have items := congrArg PhaseCReachCarrier.items equal
  have itemQueue := congrArg PhaseCReachCarrier.itemQueue equal
  have edges := congrArg PhaseCReachCarrier.edges equal
  change after.payload.phaseC.memo = before.payload.phaseC.memo at memo
  change after.payload.phaseC.contextualItems =
    before.payload.phaseC.contextualItems at items
  change after.payload.phaseC.itemQueue =
    before.payload.phaseC.itemQueue at itemQueue
  change after.payload.phaseC.contextualEdges =
    before.payload.phaseC.contextualEdges at edges
  refine {
    memo := memo
    items := ?_
    itemQueue := ?_
    edges := ?_
    newItemsQueued := ?_
  }
  · intro item member
    rw [items]
    exact member
  · intro item member
    rw [itemQueue]
    exact member
  · intro edge member
    rw [edges]
    exact member
  · intro item member
    left
    rw [← items]
    exact member

private theorem insertContextualItem?_coverage
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCContentGrowth current result ∧
      item ∈ result.payload.phaseC.contextualItems := by
  unfold insertContextualItem? at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current,
      (phaseCItemMemberBool_true_iff _ _).mp present⟩
  next absent =>
    have payload := runMappedPrimitive?_payload current _ _ selected
    constructor
    · refine {
        memo := by rw [payload]
        items := fun candidate member => by rw [payload]; simp [member]
        itemQueue := fun candidate member => by rw [payload]; simp [member]
        edges := fun candidate member => by rw [payload]; exact member
        newItemsQueued := ?_
      }
      intro candidate member
      rw [payload] at member ⊢
      simp only [List.mem_append, List.mem_singleton] at member ⊢
      exact member.elim Or.inl (fun equal => Or.inr (Or.inr equal))
    · rw [payload]
      simp

private theorem insertContextualScannedEdge?_coverage
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (selected : insertContextualScannedEdge? current edge = some result) :
    PhaseCContentGrowth current result ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .scanned edge.before edge.after edge.cursor := by
  unfold insertContextualScannedEdge? at selected
  simp only at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current,
      (phaseCEdgeMemberBool_true_iff _ _).mp present⟩
  next absent =>
    have payload := runMappedPrimitive?_payload current _ _ selected
    constructor
    · exact {
        memo := by rw [payload]
        items := fun _ member => by rw [payload]; exact member
        itemQueue := fun _ member => by rw [payload]; exact member
        edges := fun candidate member => by rw [payload]; simp [member]
        newItemsQueued := fun _ member => by
          left
          rw [payload] at member
          exact member
      }
    · rw [payload]
      exact ⟨CompletionBackpointerLedger.packScanned edge,
        by simp [CompletionBackpointerLedger.packScanned]⟩

private theorem insertContextualCompletedEdge?_coverage
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : insertContextualCompletedEdge? current edge = some result) :
    PhaseCContentGrowth current result ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .completed edge.waiting edge.finished edge.after
          edge.shared := by
  unfold insertContextualCompletedEdge? at selected
  simp only at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current,
      (phaseCEdgeMemberBool_true_iff _ _).mp present⟩
  next absent =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨pair, insertedEq, steppedEq⟩
    rcases pair with ⟨nextLedger, nextEdges⟩
    unfold CompletionBackpointerLedger.insertCompleted? at insertedEq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at insertedEq
    rcases insertedEq with ⟨ledger, _ledgerEq, pairEq⟩
    cases pairEq
    have payload := runMappedPrimitive?_payload current _ _ steppedEq
    constructor
    · exact {
        memo := by rw [payload]
        items := fun _ member => by rw [payload]; exact member
        itemQueue := fun _ member => by rw [payload]; exact member
        edges := fun candidate member => by rw [payload]; simp [member]
        newItemsQueued := fun _ member => by
          left
          rw [payload] at member
          exact member
      }
    · rw [payload]
      exact ⟨CompletionBackpointerLedger.packCompleted edge,
        by simp [CompletionBackpointerLedger.packCompleted]⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem observedPhaseABPrerequisites_total
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    ObservedPhaseABPrerequisites file tokens owned := by
  obtain ⟨phaseA, executed, sameMembers⟩ :=
    executePhaseA?_total_membership_eq file tokens owned
  exact ⟨phaseA, executed,
    (canonicalRawItems_eq_iff phaseA.payload.rawItems
      (rawSaturation tokens)).mpr sameMembers⟩

private theorem executeObservedPhaseAB?_total
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    ∃ result, executeObservedPhaseAB? file tokens owned = some result :=
  (executeObservedPhaseAB?_total_iff_prerequisites file tokens owned).mpr
    (observedPhaseABPrerequisites_total file tokens owned)

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- The executable Phase-A/Phase-B guard worklist succeeds for every owned
token stream. -/
theorem executeObservedGuardWorklist?_total
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    ∃ result, executeObservedGuardWorklist? file tokens owned = some result := by
  obtain ⟨internal, internalEq⟩ :=
    executeObservedPhaseAB?_total file tokens owned
  refine ⟨{ memo := internal.payload.memo }, ?_⟩
  unfold executeObservedGuardWorklist?
  rw [internalEq]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rfl

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem beginPhaseCWorklist?_total_iff_root_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens)) :
    (∃ result, beginPhaseCWorklist? current = some result) ↔
      (.linear .L03_itemInsert
        (contextualLinearKey (contextualRoot tokens)) : UnitAddress tokens) ∉
          current.counter.usedRev := by
  constructor
  · rintro ⟨result, selected⟩
    unfold beginPhaseCWorklist? at selected
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨entered, enteredEq, resultEq⟩
    unfold enterPhaseC? runMappedPrimitive? at enteredEq
    dsimp only at enteredEq
    split at enteredEq
    next fresh => exact fresh
    next used => contradiction
  · intro fresh
    unfold beginPhaseCWorklist? enterPhaseC?
    simp [runMappedPrimitive?, fresh]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseCWorklistPrerequisites
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens)) : Prop :=
  (.linear .L03_itemInsert
    (contextualLinearKey (contextualRoot tokens)) : UnitAddress tokens) ∉
      current.counter.usedRev ∧
  ∀ entered, beginPhaseCWorklist? current = some entered →
    ∃ result, runPhaseCQueues? owned (chartGBound (tokens.length + 1))
      entered = some result

set_option maxRecDepth 2048 in
private theorem executePhaseCWorklist?_total_iff_prerequisites
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens)) :
    (∃ result, executePhaseCWorklist? owned current = some result) ↔
      PhaseCWorklistPrerequisites owned current := by
  constructor
  · rintro ⟨result, selected⟩
    unfold executePhaseCWorklist? at selected
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨entered, enteredEq, runEq⟩
    refine ⟨(beginPhaseCWorklist?_total_iff_root_fresh current).mp
      ⟨entered, enteredEq⟩, ?_⟩
    intro candidate candidateEq
    rw [enteredEq] at candidateEq
    cases candidateEq
    exact ⟨result, runEq⟩
  · rintro ⟨rootFresh, drainable⟩
    obtain ⟨entered, enteredEq⟩ :=
      (beginPhaseCWorklist?_total_iff_root_fresh current).mpr rootFresh
    obtain ⟨result, runEq⟩ := drainable entered enteredEq
    exact ⟨result, by
      unfold executePhaseCWorklist?
      rw [enteredEq]
      exact runEq⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def ObservedPhaseCPrerequisites
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) : Prop :=
  ∀ phaseB, executeObservedPhaseAB? file tokens owned = some phaseB →
    PhaseCWorklistPrerequisites owned phaseB

private theorem executeObservedPhaseABCWorklist?_total_iff_prerequisites
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens) :
    (∃ result, executeObservedPhaseABCWorklist? file tokens owned =
      some result) ↔ ObservedPhaseCPrerequisites file tokens owned := by
  constructor
  · rintro ⟨result, selected⟩ phaseB phaseBEq
    unfold executeObservedPhaseABCWorklist? at selected
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨actualPhaseB, actualPhaseBEq, phaseCEq⟩
    rw [phaseBEq] at actualPhaseBEq
    cases actualPhaseBEq
    exact (executePhaseCWorklist?_total_iff_prerequisites owned phaseB).mp
      ⟨result, phaseCEq⟩
  · intro prerequisites
    obtain ⟨phaseB, phaseBEq⟩ := executeObservedPhaseAB?_total
      file tokens owned
    obtain ⟨result, phaseCEq⟩ :=
      (executePhaseCWorklist?_total_iff_prerequisites owned phaseB).mpr
        (prerequisites phaseB phaseBEq)
    exact ⟨result, by
      unfold executeObservedPhaseABCWorklist?
      rw [phaseBEq]
      exact phaseCEq⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem phaseC_runMappedPrimitive?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (address : UnitAddress tokens)
    (selected : runMappedPrimitive? current address id = some result) :
    PhaseCContentGrowth current result := by
  have payload := runMappedPrimitive?_payload current address id selected
  change result.payload = current.payload at payload
  exact PhaseCContentGrowth.of_reachCarrier_eq current result
    (by rw [payload])

private theorem activateWorklistProduction?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCContentGrowth current result.1 :=
  PhaseCContentGrowth.of_reachCarrier_eq current result.1
    (activateWorklistProduction?_reachCarrier current productionInstance
      result selected)

private theorem attemptContextualPrediction?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    PhaseCContentGrowth current result := by
  unfold attemptContextualPrediction? at selected
  cases predictedEq : contextualPredictedItem? waiting predicted with
  | none =>
      simp only [predictedEq] at selected
      cases selected
      exact .refl current
  | some pair =>
      rcases pair with ⟨item, productionInstance⟩
      simp only [predictedEq] at selected
      cases attemptedEq : runMappedPrimitive? current
          (.prediction .R01_predictionAttempt
            (contextualPredictionKey waiting predicted)) id with
      | none => simp [attemptedEq] at selected
      | some attempted =>
          have attemptedGrowth := phaseC_runMappedPrimitive?_contentGrowth
            current attempted _ attemptedEq
          by_cases used : (UnitAddress.production productionInstance) ∈
              attempted.counter.usedRev
          · simp [attemptedEq, used] at selected
            cases selected
            exact attemptedGrowth
          · cases activatedEq :
                activateWorklistProduction? attempted productionInstance with
            | none => simp [attemptedEq, used, activatedEq] at selected
            | some activated =>
                have activatedGrowth :=
                  activateWorklistProduction?_contentGrowth attempted
                    productionInstance activated activatedEq
                cases acceptedEq : activated.2
                · simp [attemptedEq, used, activatedEq, acceptedEq]
                    at selected
                  cases selected
                  exact attemptedGrowth.trans activatedGrowth
                · simp [attemptedEq, used, activatedEq, acceptedEq]
                    at selected
                  exact attemptedGrowth.trans (activatedGrowth.trans
                    (insertContextualItem?_coverage activated.1 result
                      .prediction item selected).1)

private theorem attemptContextualPredictions?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    ∀ productions
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      attemptContextualPredictions? waiting productions current =
        some result →
      PhaseCContentGrowth current result := by
  intro productions
  induction productions with
  | nil =>
      intro current result selected
      cases selected
      exact .refl current
  | cons predicted rest induction =>
      intro current result selected
      rw [attemptContextualPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      exact (attemptContextualPrediction?_contentGrowth current next waiting
        predicted nextEq).trans (induction next result continued)

private theorem attemptContextualScan?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens)
    (selected : attemptContextualScan? owned current before = some result) :
    PhaseCContentGrowth current result := by
  unfold attemptContextualScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have attemptedGrowth := phaseC_runMappedPrimitive?_contentGrowth
      current attempted _ attemptedEq
    cases scanEq : contextualScannedEdge? owned before with
    | none =>
        simp only [scanEq] at remainder
        cases remainder
        exact attemptedGrowth
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scanEq, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        exact attemptedGrowth.trans
          ((insertContextualItem?_coverage attempted withItem .scan after
            itemEq).1.trans
          (insertContextualScannedEdge?_coverage withItem result edge
            edgeEq).1)
  next notApplicable =>
    cases selected
    exact .refl current

private theorem attemptContextualCompletion?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished : ContextualItemKey tokens)
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    PhaseCContentGrowth current result := by
  unfold attemptContextualCompletion? at selected
  cases completionEq : contextualCompletedEdge?
      (file := file) waiting finished with
  | none =>
      simp only [completionEq] at selected
      cases selected
      exact .refl current
  | some pair =>
      rcases pair with ⟨after, edge⟩
      simp only [completionEq] at selected
      split at selected
      next used =>
        cases selected
        exact .refl current
      next fresh =>
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
        rcases selected with
          ⟨attempted, attemptedEq, withItem, itemEq, edgeEq⟩
        exact (phaseC_runMappedPrimitive?_contentGrowth current attempted _
          attemptedEq).trans
          ((insertContextualItem?_coverage attempted withItem .completion
            after itemEq).1.trans
          (insertContextualCompletedEdge?_coverage withItem result edge
            edgeEq).1)

private theorem attemptContextualCompletionsWith?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    ∀ others
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      attemptContextualCompletionsWith? pivot others current = some result →
      PhaseCContentGrowth current result := by
  intro others
  induction others with
  | nil =>
      intro current result selected
      cases selected
      exact .refl current
  | cons other rest induction =>
      intro current result selected
      rw [attemptContextualCompletionsWith?] at selected
      cases forwardEq : attemptContextualCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardGrowth := attemptContextualCompletion?_contentGrowth
            current forward pivot other forwardEq
          split at selected
          next same =>
            exact forwardGrowth.trans (induction forward result selected)
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq :
                attemptContextualCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact forwardGrowth.trans
                  ((attemptContextualCompletion?_contentGrowth forward reverse
                    other pivot reverseEq).trans
                  (induction reverse result selected))

private theorem processContextualItem?_contentGrowth
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : processContextualItem? owned item current = some result) :
    PhaseCContentGrowth current result := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predicted, predictedEq, scanned, scannedEq, completedEq⟩
  exact (attemptContextualPredictions?_contentGrowth item allProductionIds
    current predicted predictedEq).trans
    ((attemptContextualScan?_contentGrowth owned predicted scanned item
      scannedEq).trans
    (attemptContextualCompletionsWith?_contentGrowth item
      scanned.payload.phaseC.contextualItems scanned result completedEq))

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Public proof-free delimiter closer used at the Chart/Properties boundary. -/
inductive ObservedDelimiterCloser where
  | rightParen
  | rightBracket
  | rightBrace
  deriving Repr, BEq, DecidableEq

abbrev ObservedDelimiterStack := List ObservedDelimiterCloser

def observedDelimiterStep? :
    ObservedDelimiterStack → TokenKind → Option ObservedDelimiterStack
  | before, .symbol .leftParen => some (.rightParen :: before)
  | before, .symbol .leftBracket => some (.rightBracket :: before)
  | before, .symbol .leftBrace => some (.rightBrace :: before)
  | .rightParen :: rest, .symbol .rightParen => some rest
  | .rightBracket :: rest, .symbol .rightBracket => some rest
  | .rightBrace :: rest, .symbol .rightBrace => some rest
  | _, .symbol .rightParen => none
  | _, .symbol .rightBracket => none
  | _, .symbol .rightBrace => none
  | before, _ => some before

def observedDelimiterRunFrom?
    (tokens : List Token) : Nat → Nat → ObservedDelimiterStack →
      Option ObservedDelimiterStack
  | 0, _, before => some before
  | fuel + 1, cursor, before =>
      if inRange : cursor < tokens.length then
        match observedDelimiterStep? before tokens[cursor].payload with
        | some after =>
            observedDelimiterRunFrom? tokens fuel (cursor + 1) after
        | none => none
      else
        none

def observedDelimiterRun?
    (tokens : List Token) (before : ObservedDelimiterStack)
    (start finish : Boundary tokens) : Option ObservedDelimiterStack :=
  if _ordered : start.val ≤ finish.val then
    observedDelimiterRunFrom? tokens (finish.val - start.val)
      start.val before
  else
    none

def observedProtectedDelimiterStep?
    (before : ObservedDelimiterStack) (token : TokenKind) :
    Option ObservedDelimiterStack :=
  match before with
  | [] => none
  | _ :: _ =>
      match observedDelimiterStep? before token with
      | some after@(_ :: _) => some after
      | _ => none

def observedProtectedDelimiterRunFrom?
    (tokens : List Token) : Nat → Nat → ObservedDelimiterStack →
      Option ObservedDelimiterStack
  | 0, _, [] => none
  | 0, _, before@(_ :: _) => some before
  | fuel + 1, cursor, before =>
      if inRange : cursor < tokens.length then
        match observedProtectedDelimiterStep?
            before tokens[cursor].payload with
        | some after =>
            observedProtectedDelimiterRunFrom? tokens fuel
              (cursor + 1) after
        | none => none
      else
        none

def observedProtectedDelimiterRun?
    (tokens : List Token) (before : ObservedDelimiterStack)
    (start finish : Boundary tokens) : Option ObservedDelimiterStack :=
  if _ordered : start.val ≤ finish.val then
    observedProtectedDelimiterRunFrom? tokens
      (finish.val - start.val) start.val before
  else
    none

private def PhaseADelimiterCloser.observed :
    PhaseADelimiterCloser → ObservedDelimiterCloser
  | .rightParen => .rightParen
  | .rightBracket => .rightBracket
  | .rightBrace => .rightBrace

private theorem phaseADelimiterStep?_observed
    (before : PhaseADelimiterStack) (token : TokenKind) :
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseADelimiterStep? before token) =
      observedDelimiterStep?
        (before.map PhaseADelimiterCloser.observed) token := by
  cases token <;> try rfl
  case symbol symbol =>
    cases symbol <;> try rfl
    all_goals
      cases before with
      | nil => rfl
      | cons head tail =>
          cases head <;> rfl

private theorem phaseADelimiterRunFrom?_observed
    (tokens : List Token) : ∀ fuel cursor before,
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseADelimiterRunFrom? tokens fuel cursor before) =
      observedDelimiterRunFrom? tokens fuel cursor
        (before.map PhaseADelimiterCloser.observed) := by
  intro fuel
  induction fuel with
  | zero => intro cursor before; simp [phaseADelimiterRunFrom?,
      observedDelimiterRunFrom?]
  | succ fuel induction =>
      intro cursor before
      rw [phaseADelimiterRunFrom?, observedDelimiterRunFrom?]
      split
      next inRange =>
        have step := phaseADelimiterStep?_observed before
          tokens[cursor].payload
        cases selected : phaseADelimiterStep? before tokens[cursor].payload
        <;> rw [selected] at step
        · have observedNone : observedDelimiterStep?
              (List.map PhaseADelimiterCloser.observed before)
              tokens[cursor].payload = none := by simpa using step.symm
          rw [observedNone]
          rfl
        · rename_i after
          have observedSome : observedDelimiterStep?
              (List.map PhaseADelimiterCloser.observed before)
              tokens[cursor].payload =
                some (after.map PhaseADelimiterCloser.observed) := by
            simpa using step.symm
          rw [observedSome]
          exact induction (cursor + 1) after
      next outOfRange => rfl

private theorem phaseADelimiterRun?_observed
    (tokens : List Token) (before : PhaseADelimiterStack)
    (start finish : Boundary tokens) :
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseADelimiterRun? tokens before start finish) =
      observedDelimiterRun? tokens
        (before.map PhaseADelimiterCloser.observed) start finish := by
  unfold phaseADelimiterRun? observedDelimiterRun?
  split
  · exact phaseADelimiterRunFrom?_observed tokens _ _ before
  · rfl

private theorem phaseAProtectedDelimiterStep?_observed
    (before : PhaseADelimiterStack) (token : TokenKind) :
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseAProtectedDelimiterStep? before token) =
      observedProtectedDelimiterStep?
        (before.map PhaseADelimiterCloser.observed) token := by
  cases before with
  | nil => rfl
  | cons head tail =>
      have step := phaseADelimiterStep?_observed (head :: tail) token
      cases selected : phaseADelimiterStep? (head :: tail) token
      <;> rw [selected] at step
      · have observedNone : observedDelimiterStep?
            ((head :: tail).map PhaseADelimiterCloser.observed) token =
              none := by simpa using step.symm
        simp only [List.map_cons] at observedNone
        simp only [phaseAProtectedDelimiterStep?, selected, Option.map_none,
          observedProtectedDelimiterStep?, List.map_cons]
        rw [observedNone]
      · rename_i after
        have observedSome : observedDelimiterStep?
            ((head :: tail).map PhaseADelimiterCloser.observed) token =
              some (after.map PhaseADelimiterCloser.observed) := by
          simpa using step.symm
        simp only [List.map_cons] at observedSome
        cases after with
        | nil =>
            simp only [phaseAProtectedDelimiterStep?, selected,
              observedProtectedDelimiterStep?, List.map_cons,
              Option.map_none]
            rw [observedSome]
            rfl
        | cons afterHead afterTail =>
            simp only [phaseAProtectedDelimiterStep?, selected,
              observedProtectedDelimiterStep?, List.map_cons,
              Option.map_some]
            rw [observedSome]
            rfl

private theorem phaseAProtectedDelimiterRunFrom?_observed
    (tokens : List Token) : ∀ fuel cursor before,
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseAProtectedDelimiterRunFrom? tokens fuel cursor before) =
      observedProtectedDelimiterRunFrom? tokens fuel cursor
        (before.map PhaseADelimiterCloser.observed) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor before
      cases before <;> simp [phaseAProtectedDelimiterRunFrom?,
        observedProtectedDelimiterRunFrom?]
  | succ fuel induction =>
      intro cursor before
      rw [phaseAProtectedDelimiterRunFrom?,
        observedProtectedDelimiterRunFrom?]
      split
      next inRange =>
        have step := phaseAProtectedDelimiterStep?_observed before
          tokens[cursor].payload
        cases selected : phaseAProtectedDelimiterStep?
            before tokens[cursor].payload
        <;> rw [selected] at step
        · have observedNone : observedProtectedDelimiterStep?
              (before.map PhaseADelimiterCloser.observed)
              tokens[cursor].payload = none := by simpa using step.symm
          rw [observedNone]
          rfl
        · rename_i after
          have observedSome : observedProtectedDelimiterStep?
              (before.map PhaseADelimiterCloser.observed)
              tokens[cursor].payload =
                some (after.map PhaseADelimiterCloser.observed) := by
            simpa using step.symm
          rw [observedSome]
          exact induction (cursor + 1) after
      next outOfRange => rfl

private theorem phaseAProtectedDelimiterRun?_observed
    (tokens : List Token) (before : PhaseADelimiterStack)
    (start finish : Boundary tokens) :
    Option.map (List.map PhaseADelimiterCloser.observed)
        (phaseAProtectedDelimiterRun? tokens before start finish) =
      observedProtectedDelimiterRun? tokens
        (before.map PhaseADelimiterCloser.observed) start finish := by
  unfold phaseAProtectedDelimiterRun? observedProtectedDelimiterRun?
  split
  · exact phaseAProtectedDelimiterRunFrom?_observed tokens _ _ before
  · rfl

private theorem phaseADelimiterCloser_map_eq_rightParen_iff
    (values : PhaseADelimiterStack) :
    values.map PhaseADelimiterCloser.observed =
        [.rightParen] ↔
      values = [.rightParen] := by
  cases values with
  | nil => simp
  | cons head tail =>
      cases head <;> cases tail <;>
        simp [PhaseADelimiterCloser.observed]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

/-- Raw retained-symbol observation independent of file ownership. -/
def observedRawSymbolAtBool
    {tokens : List Token} (cursor : Boundary tokens)
    (symbol : Symbol) : Bool :=
  if inRange : cursor.val < tokens.length then
    decide (tokens[cursor.val].payload = .symbol symbol)
  else
    false

/-- Membership in one fixed nonempty symbol family. -/
def observedSymbolAllowedBool
    (symbol : Symbol) (allowed : NonemptyList Symbol) : Bool :=
  decide (symbol = allowed.head) ||
    allowed.tail.any fun candidate => decide (symbol = candidate)

/-- Raw allowed-symbol observation independent of file ownership. -/
def observedAllowedSymbolAtBool
    {tokens : List Token} (cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) : Bool :=
  if inRange : cursor.val < tokens.length then
    match tokens[cursor.val].payload with
    | .symbol symbol => observedSymbolAllowedBool symbol allowed
    | _ => false
  else
    false

private theorem observedRawSymbolAtBool_eq_phaseA
    {tokens : List Token} (cursor : Boundary tokens) (symbol : Symbol) :
    observedRawSymbolAtBool cursor symbol =
      phaseASymbolAtBool cursor symbol := rfl

private theorem observedAllowedSymbolAtBool_eq_phaseA
    {tokens : List Token} (cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) :
    observedAllowedSymbolAtBool cursor allowed =
      phaseAAllowedSymbolAtBool cursor allowed := by
  unfold observedAllowedSymbolAtBool phaseAAllowedSymbolAtBool
    observedSymbolAllowedBool phaseASymbolAllowedBool
  rfl

/-- Equal-depth bit computed through the public delimiter executor. -/
def observedSameDelimiterDepthBool
    (tokens : List Token) (start finish : Boundary tokens) : Bool :=
  decide (observedDelimiterRun? tokens [] start finish = some [])

/-- Matching-parenthesis bit computed through the public delimiter executor. -/
def observedMatchingParenthesisBool
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) : Bool :=
  observedRawSymbolAtBool openCursor .leftParen &&
    observedRawSymbolAtBool closeCursor .rightParen &&
    match observedBoundaryAt? tokens (openCursor.val + 1) with
    | none => false
    | some interiorStart =>
        decide (observedProtectedDelimiterRun? tokens [.rightParen]
          interiorStart closeCursor = some [.rightParen])

/-- G06 delimiter bit computed through the public delimiter executor. -/
def observedPatternDelimiterBool
    (tokens : List Token) (start cursor : Boundary tokens) : Bool :=
  observedSameDelimiterDepthBool tokens start cursor &&
    observedAllowedSymbolAtBool cursor {
      head := .comma
      tail := [.rightParen, .fatArrow]
    } &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if start.val ≤ earlier.val && earlier.val < cursor.val &&
          observedSameDelimiterDepthBool tokens start earlier then
        !observedAllowedSymbolAtBool earlier {
          head := .comma
          tail := [.rightParen, .fatArrow]
        }
      else
        true

theorem rawMatchingParenthesisObservation_eq_observed
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    rawMatchingParenthesisObservation tokens openCursor closeCursor =
      observedMatchingParenthesisBool tokens openCursor closeCursor := by
  unfold rawMatchingParenthesisObservation phaseAMatchingDelimiterBool
    phaseADelimiterPair? observedMatchingParenthesisBool
  simp only [decide_true, Bool.true_and,
    observedRawSymbolAtBool_eq_phaseA, observedBoundaryAt?_eq_phaseA]
  cases boundary : phaseABoundaryAt? tokens (openCursor.val + 1)
  · rfl
  · rename_i interiorStart
    change (phaseASymbolAtBool openCursor .leftParen &&
        phaseASymbolAtBool closeCursor .rightParen &&
        decide (phaseAProtectedDelimiterRun? tokens [.rightParen]
          interiorStart closeCursor = some [.rightParen])) =
      (phaseASymbolAtBool openCursor .leftParen &&
        phaseASymbolAtBool closeCursor .rightParen &&
        decide (observedProtectedDelimiterRun? tokens [.rightParen]
          interiorStart closeCursor = some [.rightParen]))
    have run := phaseAProtectedDelimiterRun?_observed tokens
      [.rightParen] interiorStart closeCursor
    simp only [PhaseADelimiterCloser.observed, List.map_cons,
      List.map_nil] at run
    rw [← run]
    cases phaseAProtectedDelimiterRun? tokens [.rightParen]
      interiorStart closeCursor with
    | none => simp
    | some values =>
        simp only [Option.map_some, Option.some.injEq,
          phaseADelimiterCloser_map_eq_rightParen_iff]

theorem rawPatternDelimiterObservation_eq_observed
    (tokens : List Token) (start cursor : Boundary tokens) :
    rawPatternDelimiterObservation tokens start cursor =
      observedPatternDelimiterBool tokens start cursor := by
  have sameDepth : ∀ finish,
      phaseASameDelimiterDepthBool tokens start finish =
        observedSameDelimiterDepthBool tokens start finish := by
    intro finish
    unfold phaseASameDelimiterDepthBool observedSameDelimiterDepthBool
    have run := phaseADelimiterRun?_observed tokens [] start finish
    simp only [List.map_nil] at run
    rw [← run]
    cases phaseADelimiterRun? tokens [] start finish <;> simp
  simp only [rawPatternDelimiterObservation,
    phaseANextSameDepthDelimiterBool, observedPatternDelimiterBool,
    observedAllowedSymbolAtBool_eq_phaseA, sameDepth]

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def phaseCInitialAddress {tokens : List Token} :
    UnitAddress tokens → Prop
  | .production _ => True
  | .guardWitness _ _ => True
  | .linear _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | .prediction _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | .cubic _ key =>
      match key.source with
      | .contextual _ => True
      | .rawEvidence => False
  | _ => False

private def PhaseCInitialFresh {tokens : List Token}
    (counter : Counter tokens) : Prop :=
  ∀ address, phaseCInitialAddress address →
    address ∉ counter.usedRev

private theorem PhaseAReservedFresh.phaseCInitialFresh
    {tokens : List Token} {counter : Counter tokens}
    (invariant : PhaseAReservedFresh counter) :
    PhaseCInitialFresh counter := by
  intro address reserved
  apply invariant address
  cases address with
  | production => simp [phaseAReservedAddress]
  | cubic kind key =>
      cases kind <;>
        simp_all [phaseAReservedAddress, phaseCInitialAddress]
  | phase => simp_all [phaseCInitialAddress]
  | guardFinalize => simp_all [phaseCInitialAddress]
  | guardWitness =>
      simp_all [phaseAReservedAddress, phaseCInitialAddress]
  | linear =>
      simp_all [phaseAReservedAddress, phaseCInitialAddress]
  | prediction =>
      simp_all [phaseAReservedAddress, phaseCInitialAddress]

private theorem runMappedPrimitive?_phaseCInitialFresh
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (invariant : PhaseCInitialFresh current.counter)
    (available : ¬ phaseCInitialAddress address)
    (result : CountedState tokens after)
    (selected : runMappedPrimitive? current address transition =
      some result) :
    PhaseCInitialFresh result.counter := by
  unfold runMappedPrimitive? at selected
  split at selected
  next fresh =>
    cases selected
    intro candidate reserved member
    simp only [Counter.charge, List.mem_cons] at member
    rcases member with equal | old
    · exact available (equal ▸ reserved)
    · exact invariant candidate reserved old
  next collision => contradiction

private theorem chargeAddresses?_phaseCInitialFresh
    {tokens : List Token} {state : Type} :
    ∀ addresses (current result : CountedState tokens state),
      (∀ address, address ∈ addresses →
        ¬ phaseCInitialAddress address) →
      PhaseCInitialFresh current.counter →
      chargeAddresses? current addresses = some result →
      PhaseCInitialFresh result.counter := by
  intro addresses
  induction addresses with
  | nil =>
      intro current result _available invariant selected
      cases selected
      exact invariant
  | cons address rest induction =>
      intro current result available invariant selected
      rw [chargeAddresses?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      exact induction next result
        (fun candidate member => available candidate (by simp [member]))
        (runMappedPrimitive?_phaseCInitialFresh current address id invariant
          (available address (by simp)) next nextEq) continued

private theorem materializePhaseAIndexes?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens) :
    ∀ addresses
      (current result : CountedState tokens (PhaseAIndexed file tokens)),
      PhaseCInitialFresh current.counter →
      materializePhaseAIndexes? evaluate addresses current = some result →
      PhaseCInitialFresh result.counter := by
  intro addresses
  induction addresses with
  | nil =>
      intro current result invariant selected
      cases selected
      exact invariant
  | cons address rest induction =>
      intro current result invariant selected
      rw [materializePhaseAIndexes?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      exact induction next result
        (runMappedPrimitive?_phaseCInitialFresh current
          (UnitAddress.evidenceIndex address) _ invariant
          (by simp [phaseCInitialAddress, UnitAddress.evidenceIndex,
            evidenceIndexUnitAddress, evidenceIndexKey]) next nextEq)
        continued

private theorem indexSaturatedPhaseACanonicalWith?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (evaluate : PhaseAIndexEvaluator file tokens)
    (current : CountedState tokens (PhaseAOpen file tokens))
    (result : CountedState tokens (PhaseAIndexed file tokens))
    (invariant : PhaseCInitialFresh current.counter)
    (selected : indexSaturatedPhaseACanonicalWith? evaluate current =
      some result) :
    PhaseCInitialFresh result.counter := by
  unfold indexSaturatedPhaseACanonicalWith? at selected
  split at selected
  next sameMembers =>
    unfold indexSaturatedPhaseAWith? at selected
    split at selected
    next itemsDone =>
      split at selected
      next edgesDone =>
        split at selected
        next saturated =>
          exact materializePhaseAIndexes?_phaseCInitialFresh evaluate _
            (beginPhaseAIndexing
              (normalizePhaseARawItems current sameMembers)) result
            (by simpa [beginPhaseAIndexing, normalizePhaseARawItems] using
              invariant) selected
        next notSaturated => contradiction
      next edgesRemain => contradiction
    next itemsRemain => contradiction
  next different => contradiction

private theorem enterIndexedPhaseB?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBIndexed file tokens))
    (invariant : PhaseCInitialFresh current.counter)
    (selected : enterIndexedPhaseB? current = some result) :
    PhaseCInitialFresh result.counter := by
  unfold enterIndexedPhaseB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseB? at enteredEq
  split at enteredEq
  next itemsDone =>
    split at enteredEq
    next edgesDone =>
      split at enteredEq
      next saturated =>
        exact runMappedPrimitive?_phaseCInitialFresh {
          payload := current.payload.phaseA
          counter := current.counter
        } (.phase .sealAEnterB) _ invariant
          (by simp [phaseCInitialAddress]) entered enteredEq
      next notSaturated => contradiction
    next edgesRemain => contradiction
  next itemsRemain => contradiction

private theorem finalizeNextIndexedGuard?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseBIndexed file tokens))
    (invariant : PhaseCInitialFresh current.counter)
    (selected : finalizeNextIndexedGuard? current = some result) :
    PhaseCInitialFresh result.counter := by
  unfold finalizeNextIndexedGuard? at selected
  cases remaining : current.payload.phaseB.remaining with
  | nil => simp [remaining] at selected
  | cons key rest =>
      simp only [remaining, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨initialized, initializedEq,
        lookedUp, lookedUpEq, decision, _decisionEq, finalEq⟩
      have initializedFresh := runMappedPrimitive?_phaseCInitialFresh
        current (.guardFinalize .initializeUndecided key) _ invariant
          (by simp [phaseCInitialAddress]) initialized initializedEq
      have lookedUpFresh := chargeAddresses?_phaseCInitialFresh
        (preFinalGuardSlots.map fun slot =>
          UnitAddress.guardFinalize slot key) initialized lookedUp
        (by simp [phaseCInitialAddress]) initializedFresh lookedUpEq
      exact runMappedPrimitive?_phaseCInitialFresh lookedUp
        (.guardFinalize .writeFinalDecision key) _ lookedUpFresh
          (by simp [phaseCInitialAddress]) result finalEq

private theorem runIndexedPhaseB?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token} :
    ∀ fuel
      (current result : CountedState tokens (PhaseBIndexed file tokens)),
      PhaseCInitialFresh current.counter →
      runIndexedPhaseB? fuel current = some result →
      PhaseCInitialFresh result.counter := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      split at selected
      · cases selected
        exact invariant
      · contradiction
  | succ fuel induction =>
      intro current result invariant selected
      rw [runIndexedPhaseB?] at selected
      cases remaining : current.payload.phaseB.remaining with
      | nil =>
          simp only [remaining] at selected
          cases selected
          exact invariant
      | cons key rest =>
          simp only [remaining] at selected
          cases finalized : finalizeNextIndexedGuard? current with
          | none => simp [finalized] at selected
          | some next =>
              rw [finalized] at selected
              exact induction next result
                (finalizeNextIndexedGuard?_phaseCInitialFresh current next
                  invariant finalized) selected

private theorem sealIndexedPhaseB?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (invariant : PhaseCInitialFresh current.counter)
    (selected : sealIndexedPhaseB? current = some result) :
    PhaseCInitialFresh result.counter := by
  unfold sealIndexedPhaseB? sealPhaseB? at selected
  cases remaining : current.payload.phaseB.remaining with
  | cons key rest => simp [remaining] at selected
  | nil =>
      simp only [remaining] at selected
      exact runMappedPrimitive?_phaseCInitialFresh {
        payload := current.payload.phaseB
        counter := current.counter
      } (.phase .sealBEnterC) _ invariant
        (by simp [phaseCInitialAddress]) result selected

private theorem executeIndexedPhaseB?_phaseCInitialFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseAIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (invariant : PhaseCInitialFresh current.counter)
    (selected : executeIndexedPhaseB? current = some result) :
    PhaseCInitialFresh result.counter := by
  unfold executeIndexedPhaseB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq,
    finalized, finalizedEq, sealedEq⟩
  exact sealIndexedPhaseB?_phaseCInitialFresh finalized result
    (runIndexedPhaseB?_phaseCInitialFresh _ entered finalized
      (enterIndexedPhaseB?_phaseCInitialFresh current entered invariant
        enteredEq) finalizedEq) sealedEq

private theorem executeObservedPhaseAB?_phaseCInitialFresh
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseBSealed file tokens))
    (selected : executeObservedPhaseAB? file tokens owned = some result) :
    PhaseCInitialFresh result.counter := by
  unfold executeObservedPhaseAB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseA, phaseAEq,
    indexed, indexedEq, phaseBEq⟩
  exact executeIndexedPhaseB?_phaseCInitialFresh indexed result
    (indexSaturatedPhaseACanonicalWith?_phaseCInitialFresh
      (phaseAObservationIndexEvaluator owned) phaseA indexed
      (executePhaseA?_reservedFresh file tokens owned phaseA phaseAEq
        |>.phaseCInitialFresh) indexedEq) phaseBEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def contextualPredictedItemOfInstance {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ContextualItemKey tokens := {
  raw := {
    production := productionInstance.production
    dot := ⟨0, Nat.zero_lt_succ _⟩
    origin := productionInstance.origin
    current := productionInstance.origin
  }
  context := productionInstance.context
}

private theorem contextualPredictedItem?_item_eq_instance
    {tokens : List Token}
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (item : ContextualItemKey tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (selected : contextualPredictedItem? waiting predicted =
      some (item, productionInstance)) :
    item = contextualPredictedItemOfInstance productionInstance := by
  unfold contextualPredictedItem? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  next sameLhs =>
    have equal := Option.some.inj selected
    cases equal
    rfl

private theorem contextualCompletedEdge?_finished_shape
    {file : WorkspaceFile} {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge)) :
    finished.raw.origin = waiting.raw.current ∧
      finished.context =
        descendContext waiting finished.raw.production := by
  unfold contextualCompletedEdge? at selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  next sameCursor =>
    split at selected <;> try contradiction
    next sameContext => exact ⟨sameCursor.symm, sameContext⟩

private theorem contextualCompletedEdge?_eq_of_contextualCompletionKey_eq
    {file : WorkspaceFile} {tokens : List Token}
    (leftWaiting leftFinished leftAfter : ContextualItemKey tokens)
    (leftEdge : StructurallyValidContextualCompletedEdge file tokens)
    (rightWaiting rightFinished rightAfter : ContextualItemKey tokens)
    (rightEdge : StructurallyValidContextualCompletedEdge file tokens)
    (leftSelected : contextualCompletedEdge? (file := file)
      leftWaiting leftFinished = some (leftAfter, leftEdge))
    (rightSelected : contextualCompletedEdge? (file := file)
      rightWaiting rightFinished = some (rightAfter, rightEdge))
    (keys : contextualCompletionKey leftWaiting leftFinished =
      contextualCompletionKey rightWaiting rightFinished) :
    leftAfter = rightAfter ∧ leftEdge = rightEdge := by
  have waitingRaw : leftWaiting.raw = rightWaiting.raw :=
    dottedItem_eq_of_fields
      (congrArg (fun key => key.waiting.production) keys)
      (congrArg (fun key => key.waiting.dot.val) keys)
      (congrArg (fun key => key.origin) keys)
      (congrArg (fun key => key.shared) keys)
  have waitingContext : leftWaiting.context = rightWaiting.context := by
    have source := congrArg ChartCubicKey.source keys
    simpa only [contextualCompletionKey,
      ChartSourceTag.contextual.injEq] using source
  have waitingEq : leftWaiting = rightWaiting :=
    contextualItem_eq_of_fields waitingRaw waitingContext
  have leftShape := contextualCompletedEdge?_finished_shape leftWaiting
    leftFinished leftAfter leftEdge leftSelected
  have rightShape := contextualCompletedEdge?_finished_shape rightWaiting
    rightFinished rightAfter rightEdge rightSelected
  have finishedOrigin : leftFinished.raw.origin =
      rightFinished.raw.origin := by
    rw [leftShape.1, rightShape.1, waitingEq]
  have finishedRaw : leftFinished.raw = rightFinished.raw :=
    dottedItem_eq_of_fields
      (congrArg (fun key => key.finished.production) keys)
      (congrArg (fun key => key.finished.dot.val) keys)
      finishedOrigin
      (congrArg (fun key => key.current) keys)
  have finishedContext : leftFinished.context = rightFinished.context := by
    rw [leftShape.2, rightShape.2, waitingEq,
      congrArg DottedItem.production finishedRaw]
  have finishedEq : leftFinished = rightFinished :=
    contextualItem_eq_of_fields finishedRaw finishedContext
  subst rightWaiting
  subst rightFinished
  rw [leftSelected] at rightSelected
  exact Prod.mk.inj (Option.some.inj rightSelected)

private theorem attemptContextualPrediction?_materialization_boundary
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (item : ContextualItemKey tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (computed : contextualPredictedItem? waiting predicted =
      some (item, productionInstance))
    (enabled : MemoEnablesProduction current.payload.phaseC.memo
      productionInstance)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    (UnitAddress.production productionInstance ∈ current.counter.usedRev) ∨
      item ∈ result.payload.phaseC.contextualItems := by
  unfold attemptContextualPrediction? at selected
  rw [computed] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, remainder⟩
  have attemptedPayload := runMappedPrimitive?_payload current _ id attemptedEq
  change attempted.payload = current.payload at attemptedPayload
  split at remainder
  next used =>
    have old : UnitAddress.production productionInstance ∈
        current.counter.usedRev := by
      rw [runMappedPrimitive?_usedRev current _ id attempted attemptedEq,
        List.mem_cons] at used
      rcases used with collision | old
      · cases collision
      · exact old
    cases remainder
    exact Or.inl old
  next fresh =>
    simp only [Option.bind_eq_some_iff] at remainder
    rcases remainder with ⟨activated, activatedEq, acceptedEq⟩
    have accepted := activateWorklistProduction?_accepted_complete attempted
      productionInstance activated activatedEq (by
        rw [attemptedPayload]
        exact enabled)
    cases value : activated.2
    · simp [value] at accepted
    · simp only [value] at acceptedEq
      right
      exact (insertContextualItem?_coverage activated.1 result .prediction
        item acceptedEq).2

private theorem attemptContextualCompletion?_materialization_boundary
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (computed : contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge))
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    ((.cubic .U03_completionAttempt
        (contextualCompletionKey waiting finished) : UnitAddress tokens) ∈
      current.counter.usedRev) ∨
    (after ∈ result.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .completed edge.waiting edge.finished edge.after
          edge.shared) := by
  unfold attemptContextualCompletion? at selected
  rw [computed] at selected
  simp only at selected
  split at selected
  next used =>
    cases selected
    exact Or.inl used
  next fresh =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with
      ⟨attempted, attemptedEq, withItem, itemEq, edgeEq⟩
    have itemCoverage := insertContextualItem?_coverage attempted withItem
      .completion after itemEq
    have edgeCoverage := insertContextualCompletedEdge?_coverage withItem
      result edge edgeEq
    exact Or.inr ⟨edgeCoverage.1.items itemCoverage.2, edgeCoverage.2⟩

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseCProductionAddressesSubset {tokens : List Token}
    (before after : Counter tokens) : Prop :=
  ∀ productionInstance,
    UnitAddress.production productionInstance ∈ after.usedRev →
      UnitAddress.production productionInstance ∈ before.usedRev

private def PhaseCCompletionAddressesSubset {tokens : List Token}
    (before after : Counter tokens) : Prop :=
  ∀ waiting finished,
    (.cubic .U03_completionAttempt
      (contextualCompletionKey waiting finished) : UnitAddress tokens) ∈
        after.usedRev →
      (.cubic .U03_completionAttempt
        (contextualCompletionKey waiting finished) : UnitAddress tokens) ∈
          before.usedRev

private def PhaseCProductionAddressesExtendedBy {tokens : List Token}
    (before after : Counter tokens)
    (productionInstance : ProductionInstanceKey tokens) : Prop :=
  ∀ candidate,
    UnitAddress.production candidate ∈ after.usedRev →
      UnitAddress.production candidate ∈ before.usedRev ∨
        candidate = productionInstance

private theorem PhaseCProductionAddressesSubset.refl
    {tokens : List Token} (counter : Counter tokens) :
    PhaseCProductionAddressesSubset counter counter :=
  fun _ => id

private theorem PhaseCProductionAddressesSubset.trans
    {tokens : List Token} {first second third : Counter tokens}
    (left : PhaseCProductionAddressesSubset first second)
    (right : PhaseCProductionAddressesSubset second third) :
    PhaseCProductionAddressesSubset first third :=
  fun candidate member => left candidate (right candidate member)

private theorem PhaseCCompletionAddressesSubset.refl
    {tokens : List Token} (counter : Counter tokens) :
    PhaseCCompletionAddressesSubset counter counter :=
  fun _ _ => id

private theorem PhaseCCompletionAddressesSubset.trans
    {tokens : List Token} {first second third : Counter tokens}
    (left : PhaseCCompletionAddressesSubset first second)
    (right : PhaseCCompletionAddressesSubset second third) :
    PhaseCCompletionAddressesSubset first third :=
  fun waiting finished member =>
    left waiting finished (right waiting finished member)

private theorem runMappedPrimitive?_phaseCLedgerSubsets
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (result : CountedState tokens after)
    (notProduction : ∀ productionInstance,
      address ≠ UnitAddress.production productionInstance)
    (notCompletion : ∀ waiting finished,
      address ≠ (.cubic .U03_completionAttempt
        (contextualCompletionKey waiting finished) : UnitAddress tokens))
    (selected : runMappedPrimitive? current address transition =
      some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  have used := runMappedPrimitive?_usedRev current address transition result
    selected
  constructor
  · intro productionInstance member
    rw [used, List.mem_cons] at member
    exact member.elim (fun equal => (notProduction productionInstance
      equal.symm).elim) id
  · intro waiting finished member
    rw [used, List.mem_cons] at member
    exact member.elim (fun equal =>
      (notCompletion waiting finished equal.symm).elim) id

private theorem chargeAddresses?_phaseCLedgerSubsets
    {tokens : List Token} {state : Type} :
    ∀ addresses (current result : CountedState tokens state),
      (∀ address, address ∈ addresses →
        (∀ productionInstance,
          address ≠ UnitAddress.production productionInstance) ∧
        ∀ waiting finished,
          address ≠ (.cubic .U03_completionAttempt
            (contextualCompletionKey waiting finished) :
              UnitAddress tokens)) →
      chargeAddresses? current addresses = some result →
      PhaseCProductionAddressesSubset current.counter result.counter ∧
        PhaseCCompletionAddressesSubset current.counter result.counter := by
  intro addresses
  induction addresses with
  | nil =>
      intro current result _available selected
      cases selected
      exact ⟨.refl current.counter, .refl current.counter⟩
  | cons address rest induction =>
      intro current result available selected
      rw [chargeAddresses?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      have first := runMappedPrimitive?_phaseCLedgerSubsets current address id
        next (available address (by simp)).1
        (available address (by simp)).2 nextEq
      have later := induction next result
        (fun candidate member => available candidate (by simp [member]))
        continued
      exact ⟨first.1.trans later.1, first.2.trans later.2⟩

private theorem processGuardCell?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result) :
    PhaseCProductionAddressesSubset current.counter result.1.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.1.counter := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  have inspectedSubsets := chargeAddresses?_phaseCLedgerSubsets
    (preInsertWitnessSlots.map fun slot =>
      UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index)) current inspected
      (by simp) inspectedEq
  have insertedSubsets := runMappedPrimitive?_phaseCLedgerSubsets inspected
    (.guardWitness .insertWitness
      (guardCellAddress productionInstance index)) _ inserted
      (by simp) (by simp) insertedEq
  exact ⟨inspectedSubsets.1.trans insertedSubsets.1,
    inspectedSubsets.2.trans insertedSubsets.2⟩

private theorem processGuardCells?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ indices (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
      PhaseCProductionAddressesSubset current.counter result.1.counter ∧
        PhaseCCompletionAddressesSubset current.counter result.1.counter := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected
      cases selected
      exact ⟨.refl current.counter, .refl current.counter⟩
  | cons index rest induction =>
      intro current result selected
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨next, nextEq, finished, finishedEq, resultEq⟩
      cases resultEq
      have first := processGuardCell?_phaseCLedgerSubsets current
        productionInstance index next nextEq
      have later := induction next.1 finished finishedEq
      exact ⟨first.1.trans later.1, first.2.trans later.2⟩

private theorem activateProduction?_phaseCLedgerAddressFlow
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : activateProduction? current productionInstance =
      some result) :
    PhaseCProductionAddressesExtendedBy current.counter result.1.counter
        productionInstance ∧
      PhaseCCompletionAddressesSubset current.counter result.1.counter := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  have processed := processGuardCells?_phaseCLedgerSubsets
    productionInstance _ attempted result processedEq
  have used := runMappedPrimitive?_usedRev current
    (.production productionInstance) id attempted attemptedEq
  constructor
  · intro candidate member
    have attemptedMember := processed.1 candidate member
    rw [used, List.mem_cons] at attemptedMember
    rcases attemptedMember with equal | old
    · exact Or.inr (UnitAddress.production.inj equal)
    · exact Or.inl old
  · intro waiting finished member
    have attemptedMember := processed.2 waiting finished member
    rw [used, List.mem_cons] at attemptedMember
    rcases attemptedMember with equal | old
    · cases equal
    · exact old

private theorem activateWorklistProduction?_phaseCLedgerAddressFlow
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCProductionAddressesExtendedBy current.counter result.1.counter
        productionInstance ∧
      PhaseCCompletionAddressesSubset current.counter result.1.counter := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  exact activateProduction?_phaseCLedgerAddressFlow {
    payload := current.payload.phaseC
    counter := current.counter
  } productionInstance activated activatedEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseCCompletionAddressesExtendedBy
    {tokens : List Token} (before after : Counter tokens)
    (waiting finished : ContextualItemKey tokens) : Prop :=
  ∀ candidateWaiting candidateFinished,
    (.cubic .U03_completionAttempt
      (contextualCompletionKey candidateWaiting candidateFinished) :
        UnitAddress tokens) ∈ after.usedRev →
    (.cubic .U03_completionAttempt
      (contextualCompletionKey candidateWaiting candidateFinished) :
        UnitAddress tokens) ∈ before.usedRev ∨
      contextualCompletionKey candidateWaiting candidateFinished =
        contextualCompletionKey waiting finished

private theorem insertContextualItem?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  unfold insertContextualItem? at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current.counter, .refl current.counter⟩
  next absent =>
    exact runMappedPrimitive?_phaseCLedgerSubsets current _ _ result
      (by simp) (by simp) selected

private theorem insertContextualScannedEdge?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (selected : insertContextualScannedEdge? current edge = some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  unfold insertContextualScannedEdge? at selected
  simp only at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current.counter, .refl current.counter⟩
  next absent =>
    exact runMappedPrimitive?_phaseCLedgerSubsets current _ _ result
      (by simp) (by simp) selected

private theorem insertContextualCompletedEdge?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (selected : insertContextualCompletedEdge? current edge = some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  unfold insertContextualCompletedEdge? at selected
  simp only at selected
  split at selected
  next present =>
    cases selected
    exact ⟨.refl current.counter, .refl current.counter⟩
  next absent =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨pair, _insertedEq, chargedEq⟩
    exact runMappedPrimitive?_phaseCLedgerSubsets current _ _ result
      (by simp) (by simp) chargedEq

private theorem attemptContextualPrediction?_phaseCLedgerAddressFlow
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (item : ContextualItemKey tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (computed : contextualPredictedItem? waiting predicted =
      some (item, productionInstance))
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    PhaseCProductionAddressesExtendedBy current.counter result.counter
        productionInstance ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  unfold attemptContextualPrediction? at selected
  rw [computed] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, remainder⟩
  have first := runMappedPrimitive?_phaseCLedgerSubsets current _ id attempted
    (by simp) (by simp) attemptedEq
  split at remainder
  next used =>
    cases remainder
    exact ⟨fun candidate member => Or.inl (first.1 candidate member), first.2⟩
  next fresh =>
    simp only [Option.bind_eq_some_iff] at remainder
    rcases remainder with ⟨activated, activatedEq, acceptedEq⟩
    have activation := activateWorklistProduction?_phaseCLedgerAddressFlow
      attempted productionInstance activated activatedEq
    cases value : activated.2
    · simp only [value] at acceptedEq
      cases acceptedEq
      constructor
      · intro candidate member
        rcases activation.1 candidate member with old | equal
        · exact Or.inl (first.1 candidate old)
        · exact Or.inr equal
      · exact first.2.trans activation.2
    · simp only [value] at acceptedEq
      have insertion := insertContextualItem?_phaseCLedgerSubsets activated.1
        result .prediction item acceptedEq
      constructor
      · intro candidate member
        rcases activation.1 candidate (insertion.1 candidate member) with
          old | equal
        · exact Or.inl (first.1 candidate old)
        · exact Or.inr equal
      · exact first.2.trans (activation.2.trans insertion.2)

private theorem attemptContextualScan?_phaseCLedgerSubsets
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens)
    (selected : attemptContextualScan? owned current before = some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesSubset current.counter result.counter := by
  unfold attemptContextualScan? at selected
  split at selected
  next applicable =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with ⟨attempted, attemptedEq, remainder⟩
    have first := runMappedPrimitive?_phaseCLedgerSubsets current _ id attempted
      (by simp) (by simp) attemptedEq
    cases scanEq : contextualScannedEdge? owned before with
    | none =>
        simp only [scanEq] at remainder
        cases remainder
        exact first
    | some pair =>
        rcases pair with ⟨after, edge⟩
        simp only [scanEq, Option.bind_eq_some_iff] at remainder
        rcases remainder with ⟨withItem, itemEq, edgeEq⟩
        have itemFlow := insertContextualItem?_phaseCLedgerSubsets attempted
          withItem .scan after itemEq
        have edgeFlow := insertContextualScannedEdge?_phaseCLedgerSubsets
          withItem result edge edgeEq
        exact ⟨first.1.trans (itemFlow.1.trans edgeFlow.1),
          first.2.trans (itemFlow.2.trans edgeFlow.2)⟩
  next notApplicable =>
    cases selected
    exact ⟨.refl current.counter, .refl current.counter⟩

private theorem attemptContextualCompletion?_phaseCLedgerAddressFlow
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (computed : contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge))
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    PhaseCProductionAddressesSubset current.counter result.counter ∧
      PhaseCCompletionAddressesExtendedBy current.counter result.counter
        waiting finished := by
  unfold attemptContextualCompletion? at selected
  rw [computed] at selected
  simp only at selected
  split at selected
  next used =>
    cases selected
    exact ⟨.refl current.counter,
      fun _ _ member => Or.inl member⟩
  next fresh =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
    rcases selected with
      ⟨attempted, attemptedEq, withItem, itemEq, edgeEq⟩
    have itemFlow := insertContextualItem?_phaseCLedgerSubsets attempted
      withItem .completion after itemEq
    have edgeFlow := insertContextualCompletedEdge?_phaseCLedgerSubsets
      withItem result edge edgeEq
    have usedRev := runMappedPrimitive?_usedRev current _ id attempted
      attemptedEq
    constructor
    · intro candidate member
      have attemptedMember := itemFlow.1 candidate (edgeFlow.1 candidate member)
      rw [usedRev, List.mem_cons] at attemptedMember
      rcases attemptedMember with collision | old
      · cases collision
      · exact old
    · intro candidateWaiting candidateFinished member
      have attemptedMember := itemFlow.2 candidateWaiting candidateFinished
        (edgeFlow.2 candidateWaiting candidateFinished member)
      rw [usedRev, List.mem_cons] at attemptedMember
      rcases attemptedMember with equal | old
      · exact Or.inr (by
          simpa only [UnitAddress.cubic.injEq, true_and] using equal)
      · exact Or.inl old

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private structure PhaseCAttemptLedgerMaterialized
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens)) : Prop where
  prediction : ∀ productionInstance,
    MemoEnablesProduction current.payload.phaseC.memo productionInstance →
    UnitAddress.production productionInstance ∈ current.counter.usedRev →
    contextualPredictedItemOfInstance productionInstance ∈
      current.payload.phaseC.contextualItems
  completion : ∀ waiting finished after
      (edge : StructurallyValidContextualCompletedEdge file tokens),
    contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge) →
    (.cubic .U03_completionAttempt
      (contextualCompletionKey waiting finished) : UnitAddress tokens) ∈
        current.counter.usedRev →
    after ∈ current.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ current.payload.phaseC.contextualEdges ∧
        retained.val = .completed edge.waiting edge.finished edge.after
          edge.shared

private theorem PhaseCAttemptLedgerMaterialized.mono
    {file : WorkspaceFile} {tokens : List Token}
    {before after : CountedState tokens (PhaseCWorklist file tokens)}
    (ledger : PhaseCAttemptLedgerMaterialized before)
    (content : PhaseCContentGrowth before after)
    (productionAddresses : PhaseCProductionAddressesSubset
      before.counter after.counter)
    (completionAddresses : PhaseCCompletionAddressesSubset
      before.counter after.counter) :
    PhaseCAttemptLedgerMaterialized after := by
  constructor
  · intro productionInstance enabled used
    have enabledBefore : MemoEnablesProduction
        before.payload.phaseC.memo productionInstance := by
      rw [← content.memo]
      exact enabled
    exact content.items (ledger.prediction productionInstance enabledBefore
      (productionAddresses productionInstance used))
  · intro waiting finished result edge computed used
    obtain ⟨itemMember, retained, edgeMember, same⟩ :=
      ledger.completion waiting finished result edge computed
        (completionAddresses waiting finished used)
    exact ⟨content.items itemMember, retained,
      content.edges edgeMember, same⟩

private theorem attemptContextualPrediction?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    PhaseCAttemptLedgerMaterialized result := by
  cases computed : contextualPredictedItem? waiting predicted with
  | none =>
      unfold attemptContextualPrediction? at selected
      simp only [computed] at selected
      cases selected
      exact ledger
  | some pair =>
      rcases pair with ⟨item, productionInstance⟩
      have content := attemptContextualPrediction?_contentGrowth current result
        waiting predicted selected
      have addressFlow :=
        attemptContextualPrediction?_phaseCLedgerAddressFlow current result
          waiting predicted item productionInstance computed selected
      constructor
      · intro candidate enabled used
        have enabledBefore : MemoEnablesProduction
            current.payload.phaseC.memo candidate := by
          rw [← content.memo]
          exact enabled
        rcases addressFlow.1 candidate used with old | equal
        · exact content.items
            (ledger.prediction candidate enabledBefore old)
        · subst candidate
          rcases attemptContextualPrediction?_materialization_boundary
              current result waiting predicted item productionInstance
              computed enabledBefore selected with old | materialized
          · exact content.items
              (ledger.prediction productionInstance enabledBefore old)
          · rw [← contextualPredictedItem?_item_eq_instance waiting predicted
              item productionInstance computed]
            exact materialized
      · intro candidateWaiting candidateFinished after edge candidateComputed
          used
        obtain ⟨itemMember, retained, edgeMember, same⟩ :=
          ledger.completion candidateWaiting candidateFinished after edge
            candidateComputed (addressFlow.2 candidateWaiting
              candidateFinished used)
        exact ⟨content.items itemMember, retained,
          content.edges edgeMember, same⟩

private theorem attemptContextualScan?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before : ContextualItemKey tokens)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : attemptContextualScan? owned current before = some result) :
    PhaseCAttemptLedgerMaterialized result := by
  have content := attemptContextualScan?_contentGrowth owned current result
    before selected
  have addresses := attemptContextualScan?_phaseCLedgerSubsets owned current
    result before selected
  exact ledger.mono content addresses.1 addresses.2

private theorem attemptContextualCompletion?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished : ContextualItemKey tokens)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    PhaseCAttemptLedgerMaterialized result := by
  cases computed : contextualCompletedEdge?
      (file := file) waiting finished with
  | none =>
      unfold attemptContextualCompletion? at selected
      simp only [computed] at selected
      cases selected
      exact ledger
  | some pair =>
      rcases pair with ⟨actualAfter, actualEdge⟩
      have content := attemptContextualCompletion?_contentGrowth current result
        waiting finished selected
      have addressFlow :=
        attemptContextualCompletion?_phaseCLedgerAddressFlow current result
          waiting finished actualAfter actualEdge computed selected
      constructor
      · intro productionInstance enabled used
        have enabledBefore : MemoEnablesProduction
            current.payload.phaseC.memo productionInstance := by
          rw [← content.memo]
          exact enabled
        exact content.items (ledger.prediction productionInstance
          enabledBefore (addressFlow.1 productionInstance used))
      · intro candidateWaiting candidateFinished after edge candidateComputed
          used
        rcases addressFlow.2 candidateWaiting candidateFinished used with
          old | sameKey
        · obtain ⟨itemMember, retained, edgeMember, same⟩ :=
            ledger.completion candidateWaiting candidateFinished after edge
              candidateComputed old
          exact ⟨content.items itemMember, retained,
            content.edges edgeMember, same⟩
        · have sameResult :=
            contextualCompletedEdge?_eq_of_contextualCompletionKey_eq
              candidateWaiting candidateFinished after edge
              waiting finished actualAfter actualEdge candidateComputed
                computed sameKey
          have actualMaterialized :
              actualAfter ∈ result.payload.phaseC.contextualItems ∧
                ∃ retained,
                  retained ∈ result.payload.phaseC.contextualEdges ∧
                  retained.val = .completed actualEdge.waiting
                    actualEdge.finished actualEdge.after actualEdge.shared := by
            rcases attemptContextualCompletion?_materialization_boundary
                current result waiting finished actualAfter actualEdge computed
                selected with old | materialized
            · obtain ⟨itemMember, retained, edgeMember, same⟩ :=
                ledger.completion waiting finished actualAfter actualEdge
                  computed old
              exact ⟨content.items itemMember, retained,
                content.edges edgeMember, same⟩
            · exact materialized
          rw [sameResult.1, sameResult.2]
          exact actualMaterialized

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem attemptContextualPredictions?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    ∀ productions
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      attemptContextualPredictions? waiting productions current =
        some result →
      PhaseCAttemptLedgerMaterialized result := by
  intro productions
  induction productions with
  | nil =>
      intro current result ledger selected
      cases selected
      exact ledger
  | cons predicted rest induction =>
      intro current result ledger selected
      rw [attemptContextualPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      exact induction next result
        (attemptContextualPrediction?_attemptLedger current next waiting
          predicted ledger nextEq) continued

private theorem attemptContextualCompletionsWith?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    ∀ others
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      attemptContextualCompletionsWith? pivot others current = some result →
      PhaseCAttemptLedgerMaterialized result := by
  intro others
  induction others with
  | nil =>
      intro current result ledger selected
      cases selected
      exact ledger
  | cons other rest induction =>
      intro current result ledger selected
      rw [attemptContextualCompletionsWith?] at selected
      cases forwardEq : attemptContextualCompletion? current pivot other with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          have forwardLedger := attemptContextualCompletion?_attemptLedger
            current forward pivot other ledger forwardEq
          split at selected
          next same =>
            exact induction forward result forwardLedger selected
          next different =>
            simp only [Option.bind_eq_bind, Option.bind_some] at selected
            cases reverseEq :
                attemptContextualCompletion? forward other pivot with
            | none => simp [reverseEq] at selected
            | some reverse =>
                rw [reverseEq] at selected
                exact induction reverse result
                  (attemptContextualCompletion?_attemptLedger forward reverse
                    other pivot forwardLedger reverseEq) selected

private theorem processContextualItem?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : processContextualItem? owned item current = some result) :
    PhaseCAttemptLedgerMaterialized result := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predicted, predictedEq, scanned, scannedEq, completedEq⟩
  exact attemptContextualCompletionsWith?_attemptLedger item
    scanned.payload.phaseC.contextualItems scanned result
    (attemptContextualScan?_attemptLedger owned predicted scanned item
      (attemptContextualPredictions?_attemptLedger item allProductionIds
        current predicted ledger predictedEq) scannedEq) completedEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem PhaseCAttemptLedgerMaterialized.monoCore
    {file : WorkspaceFile} {tokens : List Token}
    {before after : CountedState tokens (PhaseCWorklist file tokens)}
    (ledger : PhaseCAttemptLedgerMaterialized before)
    (memo : after.payload.phaseC.memo = before.payload.phaseC.memo)
    (items : before.payload.phaseC.contextualItems ⊆
      after.payload.phaseC.contextualItems)
    (edges : before.payload.phaseC.contextualEdges ⊆
      after.payload.phaseC.contextualEdges)
    (productionAddresses : PhaseCProductionAddressesSubset
      before.counter after.counter)
    (completionAddresses : PhaseCCompletionAddressesSubset
      before.counter after.counter) :
    PhaseCAttemptLedgerMaterialized after := by
  constructor
  · intro productionInstance enabled used
    have enabledBefore : MemoEnablesProduction
        before.payload.phaseC.memo productionInstance := by
      rw [← memo]
      exact enabled
    exact items (ledger.prediction productionInstance enabledBefore
      (productionAddresses productionInstance used))
  · intro waiting finished result edge computed used
    obtain ⟨itemMember, retained, edgeMember, same⟩ :=
      ledger.completion waiting finished result edge computed
        (completionAddresses waiting finished used)
    exact ⟨items itemMember, retained, edges edgeMember, same⟩

private theorem dequeueContextualItem?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : dequeueContextualItem? current = some result) :
    PhaseCAttemptLedgerMaterialized result.2 := by
  unfold dequeueContextualItem? at selected
  cases queue : current.payload.phaseC.itemQueue with
  | nil => simp [queue] at selected
  | cons item rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := runMappedPrimitive?_payload current _ _ nextEq
      have addresses := runMappedPrimitive?_phaseCLedgerSubsets current _ _
        next (by simp) (by simp) nextEq
      exact ledger.monoCore
        (by rw [payload])
        (fun candidate member => by rw [payload]; exact member)
        (fun candidate member => by rw [payload]; exact member)
        addresses.1 addresses.2

private theorem dequeueContextualEdge?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : dequeueContextualEdge? current = some result) :
    PhaseCAttemptLedgerMaterialized result.2 := by
  unfold dequeueContextualEdge? at selected
  cases queue : current.payload.phaseC.edgeQueue with
  | nil => simp [queue] at selected
  | cons edge rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := runMappedPrimitive?_payload current _ _ nextEq
      have addresses := runMappedPrimitive?_phaseCLedgerSubsets current _ _
        next (by cases edge.val <;> simp)
        (by cases edge.val <;> simp) nextEq
      exact ledger.monoCore
        (by rw [payload])
        (fun candidate member => by rw [payload]; exact member)
        (fun candidate member => by rw [payload]; exact member)
        addresses.1 addresses.2

private theorem beginPhaseCWorklist?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (fresh : PhaseCInitialFresh current.counter)
    (selected : beginPhaseCWorklist? current = some result) :
    PhaseCAttemptLedgerMaterialized result := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  have usedRev := runMappedPrimitive?_usedRev current _ _ entered enteredEq
  constructor
  · intro productionInstance _enabled used
    exfalso
    rw [usedRev, List.mem_cons] at used
    rcases used with collision | old
    · cases collision
    · exact fresh (.production productionInstance)
        (by simp [phaseCInitialAddress]) old
  · intro waiting finished after edge _computed used
    exfalso
    rw [usedRev, List.mem_cons] at used
    rcases used with collision | old
    · cases collision
    · exact fresh (.cubic .U03_completionAttempt
          (contextualCompletionKey waiting finished))
        (by simp [phaseCInitialAddress, contextualCompletionKey]) old

private theorem runPhaseCQueues?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      runPhaseCQueues? owned fuel current = some result →
      PhaseCAttemptLedgerMaterialized result := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result ledger selected
      rw [runPhaseCQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact ledger
  | succ fuel induction =>
      intro current result ledger selected
      rw [runPhaseCQueues?] at selected
      cases items : current.payload.phaseC.itemQueue with
      | nil =>
          cases edges : current.payload.phaseC.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact ledger
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueContextualEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueContextualEdge?_attemptLedger current pair ledger
                      dequeued) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueContextualItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processed :
                  processContextualItem? owned pivot afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  exact induction next result
                    (processContextualItem?_attemptLedger owned pivot
                      afterDequeue next
                      (dequeueContextualItem?_attemptLedger current
                        (pivot, afterDequeue) ledger dequeued) processed)
                    selected

private theorem executePhaseCWorklist?_attemptLedger
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (fresh : PhaseCInitialFresh current.counter)
    (selected : executePhaseCWorklist? owned current = some result) :
    PhaseCAttemptLedgerMaterialized result := by
  unfold executePhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, runEq⟩
  exact runPhaseCQueues?_attemptLedger owned _ entered result
    (beginPhaseCWorklist?_attemptLedger current entered fresh enteredEq) runEq

private theorem executeObservedPhaseABCWorklist?_attemptLedger
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    PhaseCAttemptLedgerMaterialized result := by
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, phaseBEq, phaseCEq⟩
  exact executePhaseCWorklist?_attemptLedger owned phaseB result
    (executeObservedPhaseAB?_phaseCInitialFresh file tokens owned phaseB
      phaseBEq) phaseCEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem executeObservedPhaseAB?_phaseC_entry_total
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (phaseB : CountedState tokens (PhaseBSealed file tokens))
    (selected : executeObservedPhaseAB? file tokens owned = some phaseB) :
    ∃ entered, beginPhaseCWorklist? phaseB = some entered := by
  apply (beginPhaseCWorklist?_total_iff_root_fresh phaseB).mpr
  exact executeObservedPhaseAB?_phaseCInitialFresh file tokens owned phaseB
    selected (.linear .L03_itemInsert
      (contextualLinearKey (contextualRoot tokens)))
      (by simp [phaseCInitialAddress, contextualLinearKey])

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem guardCellAddress_injective
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    Function.Injective (guardCellAddress productionInstance) := by
  intro left right equal
  apply Fin.ext
  simpa [guardCellAddress] using congrArg
    (fun address : GuardAddress tokens => address.1.1.2.val) equal

private theorem preInsertWitnessSlots_nodup :
    preInsertWitnessSlots.Nodup := by
  decide

private theorem preInsertWitnessAddresses_nodup
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length) :
    (preInsertWitnessSlots.map fun slot =>
      UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact preInsertWitnessSlots_nodup.imp fun different equal =>
    different (UnitAddress.guardWitness.inj equal).1

private theorem processGuardCell?_total_usedRev
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (fresh : ∀ slot, UnitAddress.guardWitness slot
      (guardCellAddress productionInstance index) ∉
        current.counter.usedRev) :
    ∃ result,
      processGuardCell? current productionInstance index = some result ∧
      result.1.counter.usedRev =
        UnitAddress.guardWitness .insertWitness
            (guardCellAddress productionInstance index) ::
          (preInsertWitnessSlots.map fun slot =>
            UnitAddress.guardWitness slot
              (guardCellAddress productionInstance index)).reverse ++
            current.counter.usedRev := by
  let address := guardCellAddress productionInstance index
  let lookupAddresses := preInsertWitnessSlots.map fun slot =>
    UnitAddress.guardWitness slot address
  have lookupFresh : ∀ candidate, candidate ∈ lookupAddresses →
      candidate ∉ current.counter.usedRev := by
    intro candidate member
    simp only [lookupAddresses, List.mem_map] at member
    rcases member with ⟨slot, _slotMember, rfl⟩
    exact fresh slot
  obtain ⟨inspected, inspectedEq, inspectedUsed⟩ :=
    chargeAddresses?_total_usedRev lookupAddresses current
      (by simpa [lookupAddresses, address] using
        preInsertWitnessAddresses_nodup productionInstance index)
      lookupFresh
  have insertFresh : UnitAddress.guardWitness .insertWitness address ∉
      inspected.counter.usedRev := by
    intro used
    rw [inspectedUsed, List.mem_append, List.mem_reverse] at used
    rcases used with lookup | old
    · simp only [lookupAddresses, List.mem_map] at lookup
      rcases lookup with ⟨slot, slotMember, equal⟩
      have sameSlot := (UnitAddress.guardWitness.inj equal).1
      subst slot
      simp [preInsertWitnessSlots] at slotMember
    · exact fresh .insertWitness old
  let witness := guardWitnessFor? current.payload.memo productionInstance
    ((guardOf productionInstance.production).get index)
  let transition := fun (state : PhaseCOpen file tokens) =>
    match witness with
    | none => state
    | some key => { state with guardWitnesses := key :: state.guardWitnesses }
  let inserted : CountedState tokens (PhaseCOpen file tokens) := {
    payload := transition inspected.payload
    counter := inspected.counter.charge
      (.guardWitness .insertWitness address) insertFresh
  }
  have insertedEq : runMappedPrimitive? inspected
      (.guardWitness .insertWitness address) transition = some inserted := by
    simp [runMappedPrimitive?, insertFresh, inserted]
  refine ⟨(inserted, witness.isSome), ?_, ?_⟩
  · unfold processGuardCell?
    change (chargeAddresses? current lookupAddresses).bind _ = _
    rw [inspectedEq]
    change (runMappedPrimitive? inspected
      (.guardWitness .insertWitness address) transition).bind _ = _
    rw [insertedEq]
    rfl
  · rw [runMappedPrimitive?_usedRev inspected
      (.guardWitness .insertWitness address) transition inserted insertedEq,
      inspectedUsed]
    rfl

private theorem processGuardCells?_total_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ (indices : List
        (Fin (guardOf productionInstance.production).length))
      (current : CountedState tokens (PhaseCOpen file tokens)),
      indices.Nodup →
      (∀ index, index ∈ indices → ∀ slot,
        UnitAddress.guardWitness slot
          (guardCellAddress productionInstance index) ∉
            current.counter.usedRev) →
      ∃ result,
        processGuardCells? productionInstance indices current =
          some result := by
  intro indices
  induction indices with
  | nil =>
      intro current _unique _fresh
      exact ⟨(current, true), rfl⟩
  | cons index rest induction =>
      intro current unique fresh
      rw [List.nodup_cons] at unique
      obtain ⟨next, nextEq, nextUsed⟩ :=
        processGuardCell?_total_usedRev current productionInstance index
          (fresh index (by simp))
      have restFresh : ∀ other, other ∈ rest → ∀ slot,
          UnitAddress.guardWitness slot
            (guardCellAddress productionInstance other) ∉
              next.1.counter.usedRev := by
        intro other member slot used
        rw [nextUsed] at used
        rcases List.mem_cons.mp used with inserted | used
        · have sameAddress :=
            (UnitAddress.guardWitness.inj inserted).2
          have sameIndex :=
            guardCellAddress_injective productionInstance sameAddress
          exact unique.1 (sameIndex ▸ member)
        rcases List.mem_append.mp used with lookup | old
        · rw [List.mem_reverse] at lookup
          simp only [List.mem_map] at lookup
          rcases lookup with ⟨headSlot, _slotMember, equal⟩
          have sameAddress :=
            (UnitAddress.guardWitness.inj equal).2
          have sameIndex :=
            guardCellAddress_injective productionInstance sameAddress
          exact unique.1 (sameIndex ▸ member)
        · exact fresh other (by simp [member]) slot old
      obtain ⟨result, resultEq⟩ :=
        induction next.1 unique.2 restFresh
      refine ⟨(result.1, next.2 && result.2), ?_⟩
      change (processGuardCell? current productionInstance index).bind _ = _
      rw [nextEq]
      change (processGuardCells? productionInstance rest next.1).bind _ = _
      rw [resultEq]
      rfl

private theorem guardCellIndices_nodup
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    (List.ofFn fun index :
      Fin (guardOf productionInstance.production).length => index).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro left right _leftBound _rightBound before equal
  simp only [List.getElem_ofFn] at equal
  have sameValue : left = right := congrArg Fin.val equal
  omega

private theorem activateProduction?_total_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (productionFresh : UnitAddress.production productionInstance ∉
      current.counter.usedRev)
    (witnessFresh : ∀ index slot,
      UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index) ∉
          current.counter.usedRev) :
    ∃ result, activateProduction? current productionInstance =
      some result := by
  let attempted : CountedState tokens (PhaseCOpen file tokens) := {
    payload := current.payload
    counter := current.counter.charge
      (.production productionInstance) productionFresh
  }
  have attemptedEq : runMappedPrimitive? current
      (.production productionInstance) id = some attempted := by
    simp [runMappedPrimitive?, productionFresh, attempted]
  let indices := List.ofFn fun index :
    Fin (guardOf productionInstance.production).length => index
  have pending : ∀ index, index ∈ indices → ∀ slot,
      UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index) ∉
          attempted.counter.usedRev := by
    intro index _member slot used
    rw [runMappedPrimitive?_usedRev current
      (.production productionInstance) id attempted attemptedEq,
      List.mem_cons] at used
    rcases used with equal | old
    · cases equal
    · exact witnessFresh index slot old
  obtain ⟨result, resultEq⟩ :=
    processGuardCells?_total_fresh productionInstance indices attempted
      (by simpa [indices] using
        guardCellIndices_nodup productionInstance)
      pending
  refine ⟨result, ?_⟩
  unfold activateProduction?
  change (runMappedPrimitive? current
    (.production productionInstance) id).bind _ = _
  rw [attemptedEq]
  exact resultEq

private theorem activateWorklistProduction?_total_fresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (productionFresh : UnitAddress.production productionInstance ∉
      current.counter.usedRev)
    (witnessFresh : ∀ index slot,
      UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index) ∉
          current.counter.usedRev) :
    ∃ result, activateWorklistProduction? current productionInstance =
      some result := by
  obtain ⟨activated, activatedEq⟩ := activateProduction?_total_fresh {
      payload := current.payload.phaseC
      counter := current.counter
    } productionInstance productionFresh witnessFresh
  refine ⟨({
    payload := ⟨activated.1.payload,
      current.payload.completionBackpointers⟩
    counter := activated.1.counter
  }, activated.2), ?_⟩
  unfold activateWorklistProduction?
  rw [activatedEq]
  rfl

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem PhaseCContentGrowth.itemsAndEdges
    {file : WorkspaceFile} {tokens : List Token}
    {before after : CountedState tokens (PhaseCWorklist file tokens)}
    (growth : PhaseCContentGrowth before after)
    {item : ContextualItemKey tokens}
    {key : ContextualPackedEdgeKey tokens}
    (materialized : item ∈ before.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ before.payload.phaseC.contextualEdges ∧
        retained.val = key) :
    item ∈ after.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ after.payload.phaseC.contextualEdges ∧
        retained.val = key := by
  obtain ⟨itemMember, retained, edgeMember, same⟩ := materialized
  exact ⟨growth.items itemMember, retained, growth.edges edgeMember, same⟩

private theorem attemptContextualPrediction?_materialized_of_ledger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting : ContextualItemKey tokens) (predicted : ProductionId)
    (item : ContextualItemKey tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (computed : contextualPredictedItem? waiting predicted =
      some (item, productionInstance))
    (enabled : MemoEnablesProduction current.payload.phaseC.memo
      productionInstance)
    (selected : attemptContextualPrediction? current waiting predicted =
      some result) :
    item ∈ result.payload.phaseC.contextualItems := by
  rcases attemptContextualPrediction?_materialization_boundary current result
      waiting predicted item productionInstance computed enabled selected with
    old | materialized
  · have growth := attemptContextualPrediction?_contentGrowth current result
      waiting predicted selected
    rw [contextualPredictedItem?_item_eq_instance waiting predicted item
      productionInstance computed]
    exact growth.items (ledger.prediction productionInstance enabled old)
  · exact materialized

private theorem attemptContextualPredictions?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (waiting : ContextualItemKey tokens) :
    ∀ productions
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      attemptContextualPredictions? waiting productions current =
        some result →
      ∀ predicted, predicted ∈ productions →
      ∀ item productionInstance,
        contextualPredictedItem? waiting predicted =
          some (item, productionInstance) →
        MemoEnablesProduction current.payload.phaseC.memo
          productionInstance →
        item ∈ result.payload.phaseC.contextualItems := by
  intro productions
  induction productions with
  | nil => simp
  | cons head rest induction =>
      intro current result ledger selected predicted member item
        productionInstance computed enabled
      rw [attemptContextualPredictions?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      rw [List.mem_cons] at member
      rcases member with same | member
      · subst predicted
        exact (attemptContextualPredictions?_contentGrowth waiting rest next
          result continued).items
          (attemptContextualPrediction?_materialized_of_ledger current next
            waiting head item productionInstance ledger computed enabled
              nextEq)
      · have firstGrowth := attemptContextualPrediction?_contentGrowth current
          next waiting head nextEq
        exact induction next result
          (attemptContextualPrediction?_attemptLedger current next waiting
            head ledger nextEq) continued predicted member item
              productionInstance computed (by
                rw [firstGrowth.memo]
                exact enabled)

private theorem contextualScannedEdge?_applicable
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (selected : contextualScannedEdge? owned before = some (after, edge)) :
    contextualScanApplicable before = true := by
  unfold contextualScannedEdge? at selected
  unfold contextualScanApplicable
  split at selected <;> try contradiction
  next nextInRange =>
    split at selected <;> try contradiction
    next terminal nextEq =>
      split at selected <;> try contradiction
      next currentInRange =>
        simp [List.getElem?_eq_getElem nextInRange, nextEq,
          currentInRange]

private theorem attemptContextualScan?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (before after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (computed : contextualScannedEdge? owned before = some (after, edge))
    (selected : attemptContextualScan? owned current before = some result) :
    after ∈ result.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .scanned edge.before edge.after edge.cursor := by
  unfold attemptContextualScan? at selected
  rw [if_pos (contextualScannedEdge?_applicable owned before after edge
    computed)] at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, remainder⟩
  rw [computed] at remainder
  simp only [Option.bind_eq_some_iff] at remainder
  rcases remainder with ⟨withItem, itemEq, edgeEq⟩
  have itemCoverage := insertContextualItem?_coverage attempted withItem
    .scan after itemEq
  have edgeCoverage := insertContextualScannedEdge?_coverage withItem result
    edge edgeEq
  exact ⟨edgeCoverage.1.items itemCoverage.2, edgeCoverage.2⟩

private theorem attemptContextualCompletion?_materialized_of_ledger
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (waiting finished after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualCompletedEdge file tokens)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (computed : contextualCompletedEdge? (file := file) waiting finished =
      some (after, edge))
    (selected : attemptContextualCompletion? current waiting finished =
      some result) :
    after ∈ result.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .completed edge.waiting edge.finished edge.after
          edge.shared := by
  rcases attemptContextualCompletion?_materialization_boundary current result
      waiting finished after edge computed selected with old | materialized
  · have growth := attemptContextualCompletion?_contentGrowth current result
      waiting finished selected
    obtain ⟨itemMember, retained, edgeMember, same⟩ :=
      ledger.completion waiting finished after edge computed old
    exact ⟨growth.items itemMember, retained, growth.edges edgeMember, same⟩
  · exact materialized

private theorem attemptContextualCompletionsWith?_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (pivot : ContextualItemKey tokens) :
    ∀ others
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      attemptContextualCompletionsWith? pivot others current = some result →
      ∀ other, other ∈ others →
      (∀ after edge,
        contextualCompletedEdge? (file := file) pivot other =
          some (after, edge) →
        after ∈ result.payload.phaseC.contextualItems ∧
          ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
            retained.val = .completed edge.waiting edge.finished edge.after
              edge.shared) ∧
      (∀ after edge,
        contextualCompletedEdge? (file := file) other pivot =
          some (after, edge) →
        after ∈ result.payload.phaseC.contextualItems ∧
          ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
            retained.val = .completed edge.waiting edge.finished edge.after
              edge.shared) := by
  intro others
  induction others with
  | nil => simp
  | cons head rest induction =>
      intro current result ledger selected other member
      rw [attemptContextualCompletionsWith?] at selected
      cases forwardEq : attemptContextualCompletion? current pivot head with
      | none => simp [forwardEq] at selected
      | some forward =>
          rw [forwardEq] at selected
          simp only [Option.bind_eq_bind, Option.bind_some] at selected
          have forwardLedger := attemptContextualCompletion?_attemptLedger
            current forward pivot head ledger forwardEq
          by_cases same : head = pivot
          · rw [if_pos same] at selected
            subst head
            rw [List.mem_cons] at member
            rcases member with equal | member
            · subst other
              constructor <;> intro after edge computed
              · exact (attemptContextualCompletionsWith?_contentGrowth pivot
                  rest forward result selected).itemsAndEdges
                  (attemptContextualCompletion?_materialized_of_ledger current
                    forward pivot pivot after edge ledger computed forwardEq)
              · exact (attemptContextualCompletionsWith?_contentGrowth pivot
                  rest forward result selected).itemsAndEdges
                  (attemptContextualCompletion?_materialized_of_ledger current
                    forward pivot pivot after edge ledger computed forwardEq)
            · exact induction forward result forwardLedger selected other member
          · rw [if_neg same] at selected
            simp only [Option.bind_eq_some_iff] at selected
            rcases selected with ⟨reverse, reverseEq, continued⟩
            rw [List.mem_cons] at member
            rcases member with equal | member
            · subst other
              constructor
              · intro after edge computed
                exact (attemptContextualCompletionsWith?_contentGrowth pivot
                  rest reverse result continued).itemsAndEdges
                  ((attemptContextualCompletion?_contentGrowth forward reverse
                    head pivot reverseEq).itemsAndEdges
                    (attemptContextualCompletion?_materialized_of_ledger current
                      forward pivot head after edge ledger computed forwardEq))
              · intro after edge computed
                exact (attemptContextualCompletionsWith?_contentGrowth pivot
                  rest reverse result continued).itemsAndEdges
                  (attemptContextualCompletion?_materialized_of_ledger forward
                    reverse head pivot after edge forwardLedger computed
                      reverseEq)
            · exact induction reverse result
                (attemptContextualCompletion?_attemptLedger forward reverse
                  head pivot forwardLedger reverseEq) continued other member

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem processContextualItem?_prediction_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (pivot : ContextualItemKey tokens)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (predicted : ProductionId) (item : ContextualItemKey tokens)
    (productionInstance : ProductionInstanceKey tokens)
    (computed : contextualPredictedItem? pivot predicted =
      some (item, productionInstance))
    (enabled : MemoEnablesProduction current.payload.phaseC.memo
      productionInstance)
    (selected : processContextualItem? owned pivot current = some result) :
    item ∈ result.payload.phaseC.contextualItems := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predictions, predictionsEq, scanned, scannedEq, completionsEq⟩
  have predictedMember := attemptContextualPredictions?_materializes pivot
    allProductionIds current predictions ledger predictionsEq predicted
      (Grammar.allProductionIds_complete predicted) item productionInstance
        computed enabled
  exact (attemptContextualCompletionsWith?_contentGrowth pivot
    scanned.payload.phaseC.contextualItems scanned result
      completionsEq).items
    ((attemptContextualScan?_contentGrowth owned predictions scanned pivot
      scannedEq).items predictedMember)

private theorem processContextualItem?_scan_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (pivot after : ContextualItemKey tokens)
    (edge : StructurallyValidContextualScannedEdge file tokens)
    (computed : contextualScannedEdge? owned pivot = some (after, edge))
    (selected : processContextualItem? owned pivot current = some result) :
    after ∈ result.payload.phaseC.contextualItems ∧
      ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
        retained.val = .scanned edge.before edge.after edge.cursor := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predictions, predictionsEq, scanned, scannedEq, completionsEq⟩
  exact (attemptContextualCompletionsWith?_contentGrowth pivot
    scanned.payload.phaseC.contextualItems scanned result
      completionsEq).itemsAndEdges
    (attemptContextualScan?_materializes owned predictions scanned pivot after
      edge computed scannedEq)

private theorem processContextualItem?_completion_materializes
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (pivot other : ContextualItemKey tokens)
    (otherMember : other ∈ current.payload.phaseC.contextualItems)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : processContextualItem? owned pivot current = some result) :
    (∀ after edge,
      contextualCompletedEdge? (file := file) pivot other =
        some (after, edge) →
      after ∈ result.payload.phaseC.contextualItems ∧
        ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
          retained.val = .completed edge.waiting edge.finished edge.after
            edge.shared) ∧
    (∀ after edge,
      contextualCompletedEdge? (file := file) other pivot =
        some (after, edge) →
      after ∈ result.payload.phaseC.contextualItems ∧
        ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
          retained.val = .completed edge.waiting edge.finished edge.after
            edge.shared) := by
  unfold processContextualItem? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨predictions, predictionsEq, scanned, scannedEq, completionsEq⟩
  have predictionsGrowth := attemptContextualPredictions?_contentGrowth pivot
    allProductionIds current predictions predictionsEq
  have predictionsLedger := attemptContextualPredictions?_attemptLedger pivot
    allProductionIds current predictions ledger predictionsEq
  have scannedGrowth := attemptContextualScan?_contentGrowth owned predictions
    scanned pivot scannedEq
  have scannedLedger := attemptContextualScan?_attemptLedger owned predictions
    scanned pivot predictionsLedger scannedEq
  exact attemptContextualCompletionsWith?_materializes pivot
    scanned.payload.phaseC.contextualItems scanned result scannedLedger
      completionsEq other (scannedGrowth.items
        (predictionsGrowth.items otherMember))

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private def PhaseCFairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseCWorklist file tokens)) : Prop :=
  (contextualRoot tokens ∈ current.payload.phaseC.contextualItems) ∧
  (∀ waiting, waiting ∈ current.payload.phaseC.contextualItems →
    ∀ predicted item productionInstance,
      contextualPredictedItem? waiting predicted =
        some (item, productionInstance) →
      MemoEnablesProduction current.payload.phaseC.memo
        productionInstance →
      waiting ∈ current.payload.phaseC.itemQueue ∨
        item ∈ current.payload.phaseC.contextualItems) ∧
  (∀ before, before ∈ current.payload.phaseC.contextualItems →
    ∀ after edge,
      contextualScannedEdge? owned before = some (after, edge) →
      before ∈ current.payload.phaseC.itemQueue ∨
        (after ∈ current.payload.phaseC.contextualItems ∧
          ∃ retained, retained ∈ current.payload.phaseC.contextualEdges ∧
            retained.val = .scanned edge.before edge.after edge.cursor)) ∧
  ∀ waiting, waiting ∈ current.payload.phaseC.contextualItems →
    ∀ finished, finished ∈ current.payload.phaseC.contextualItems →
    ∀ after edge,
      contextualCompletedEdge? (file := file) waiting finished =
        some (after, edge) →
      waiting ∈ current.payload.phaseC.itemQueue ∨
      finished ∈ current.payload.phaseC.itemQueue ∨
        (after ∈ current.payload.phaseC.contextualItems ∧
          ∃ retained, retained ∈ current.payload.phaseC.contextualEdges ∧
            retained.val = .completed edge.waiting edge.finished edge.after
              edge.shared)

private theorem dequeueContextualItem?_fairShape
    {file : WorkspaceFile} {tokens : List Token}
    (before current : CountedState tokens (PhaseCWorklist file tokens))
    (head pivot : ContextualItemKey tokens)
    (rest : List (ContextualItemKey tokens))
    (queue : before.payload.phaseC.itemQueue = head :: rest)
    (selected : dequeueContextualItem? before = some (pivot, current)) :
    pivot = head ∧
      current.payload.phaseC.memo = before.payload.phaseC.memo ∧
      current.payload.phaseC.contextualItems =
        before.payload.phaseC.contextualItems ∧
      current.payload.phaseC.contextualEdges =
        before.payload.phaseC.contextualEdges ∧
      current.payload.phaseC.itemQueue = rest := by
  unfold dequeueContextualItem? at selected
  simp only [queue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at output
  rcases output with ⟨headEq, nextEqual⟩
  subst pivot
  subst next
  rw [runMappedPrimitive?_payload before _ _ nextEq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem processContextualItem?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (before current result : CountedState tokens (PhaseCWorklist file tokens))
    (pivot : ContextualItemKey tokens)
    (rest : List (ContextualItemKey tokens))
    (fair : PhaseCFairPending owned before)
    (beforeQueue : before.payload.phaseC.itemQueue = pivot :: rest)
    (currentMemo : current.payload.phaseC.memo =
      before.payload.phaseC.memo)
    (currentItems : current.payload.phaseC.contextualItems =
      before.payload.phaseC.contextualItems)
    (currentEdges : current.payload.phaseC.contextualEdges =
      before.payload.phaseC.contextualEdges)
    (currentQueue : current.payload.phaseC.itemQueue = rest)
    (ledger : PhaseCAttemptLedgerMaterialized current)
    (selected : processContextualItem? owned pivot current = some result) :
    PhaseCFairPending owned result := by
  have growth := processContextualItem?_contentGrowth owned pivot current result
    selected
  have carryItem : ∀ {item},
      item ∈ before.payload.phaseC.contextualItems →
      item ∈ result.payload.phaseC.contextualItems := by
    intro item member
    exact growth.items (currentItems.symm ▸ member)
  have carryQueue : ∀ {item}, item ≠ pivot →
      item ∈ before.payload.phaseC.itemQueue →
      item ∈ result.payload.phaseC.itemQueue := by
    intro item different member
    rw [beforeQueue, List.mem_cons] at member
    rcases member with equal | member
    · exact (different equal).elim
    · exact growth.itemQueue (currentQueue.symm ▸ member)
  have carryMaterialized : ∀ {item key},
      item ∈ before.payload.phaseC.contextualItems ∧
        (∃ retained, retained ∈ before.payload.phaseC.contextualEdges ∧
          retained.val = key) →
      item ∈ result.payload.phaseC.contextualItems ∧
        ∃ retained, retained ∈ result.payload.phaseC.contextualEdges ∧
          retained.val = key := by
    intro item key materialized
    obtain ⟨itemMember, retained, edgeMember, same⟩ := materialized
    exact ⟨carryItem itemMember, retained,
      growth.edges (currentEdges.symm ▸ edgeMember), same⟩
  refine ⟨carryItem fair.1, ?_, ?_, ?_⟩
  · intro waiting waitingMember predicted item productionInstance computed
      enabled
    rcases growth.newItemsQueued waiting waitingMember with old | queued
    · by_cases same : waiting = pivot
      · subst waiting
        right
        apply processContextualItem?_prediction_materializes owned current
          result pivot ledger predicted item productionInstance computed
        · rw [← growth.memo]
          exact enabled
        · exact selected
      · rcases fair.2.1 waiting (currentItems ▸ old) predicted item
          productionInstance computed (by
            rw [← currentMemo, ← growth.memo]
            exact enabled) with queued | materialized
        · exact Or.inl (carryQueue same queued)
        · exact Or.inr (carryItem materialized)
    · exact Or.inl queued
  · intro beforeItem beforeMember after edge computed
    rcases growth.newItemsQueued beforeItem beforeMember with old | queued
    · by_cases same : beforeItem = pivot
      · subst beforeItem
        exact Or.inr (processContextualItem?_scan_materializes owned current
          result pivot after edge computed selected)
      · rcases fair.2.2.1 beforeItem (currentItems ▸ old) after edge computed with
          queued | materialized
        · exact Or.inl (carryQueue same queued)
        · exact Or.inr (carryMaterialized materialized)
    · exact Or.inl queued
  · intro waiting waitingMember finished finishedMember after edge computed
    rcases growth.newItemsQueued waiting waitingMember with
      waitingOld | waitingQueued
    · rcases growth.newItemsQueued finished finishedMember with
        finishedOld | finishedQueued
      · by_cases waitingSame : waiting = pivot
        · subst waiting
          exact Or.inr (Or.inr
            ((processContextualItem?_completion_materializes owned current
              result pivot finished finishedOld ledger selected).1
                after edge computed))
        · by_cases finishedSame : finished = pivot
          · subst finished
            exact Or.inr (Or.inr
              ((processContextualItem?_completion_materializes owned current
                result pivot waiting waitingOld ledger selected).2
                  after edge computed))
          · rcases fair.2.2.2 waiting (currentItems ▸ waitingOld)
                finished (currentItems ▸ finishedOld) after edge computed with
              waitingQueued | finishedQueued | materialized
            · exact Or.inl (carryQueue waitingSame waitingQueued)
            · exact Or.inr (Or.inl
                (carryQueue finishedSame finishedQueued))
            · exact Or.inr (Or.inr (carryMaterialized materialized))
      · exact Or.inr (Or.inl finishedQueued)
    · exact Or.inl waitingQueued

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem beginPhaseCWorklist?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : beginPhaseCWorklist? current = some result) :
    PhaseCFairPending owned result := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  have payload := runMappedPrimitive?_payload current _ _ enteredEq
  unfold PhaseCFairPending
  rw [payload]
  refine ⟨by simp [contextualRoot], ?_, ?_, ?_⟩
  · intro waiting member predicted item productionInstance computed enabled
    left
    simpa only [List.mem_singleton] using member
  · intro before member after edge computed
    left
    simpa only [List.mem_singleton] using member
  · intro waiting waitingMember finished finishedMember after edge computed
    left
    simpa only [List.mem_singleton] using waitingMember

private theorem dequeueContextualEdge?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : StructurallyValidContextualPackedEdge file tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (fair : PhaseCFairPending owned current)
    (selected : dequeueContextualEdge? current = some result) :
    PhaseCFairPending owned result.2 := by
  unfold dequeueContextualEdge? at selected
  cases queue : current.payload.phaseC.edgeQueue with
  | nil => simp [queue] at selected
  | cons edge rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, resultEq⟩
      cases resultEq
      have payload := runMappedPrimitive?_payload current _ _ nextEq
      unfold PhaseCFairPending at fair ⊢
      rw [payload]
      exact fair

private theorem runPhaseCQueues?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∀ fuel
      (current result : CountedState tokens (PhaseCWorklist file tokens)),
      PhaseCAttemptLedgerMaterialized current →
      PhaseCFairPending owned current →
      runPhaseCQueues? owned fuel current = some result →
      PhaseCFairPending owned result := by
  intro fuel
  induction fuel with
  | zero =>
      intro current result ledger fair selected
      rw [runPhaseCQueues?] at selected
      split at selected <;> try contradiction
      cases selected
      exact fair
  | succ fuel induction =>
      intro current result ledger fair selected
      rw [runPhaseCQueues?] at selected
      cases items : current.payload.phaseC.itemQueue with
      | nil =>
          cases edges : current.payload.phaseC.edgeQueue with
          | nil =>
              simp only [items, edges] at selected
              cases selected
              exact fair
          | cons edge rest =>
              simp only [items, edges] at selected
              cases dequeued : dequeueContextualEdge? current with
              | none => simp [dequeued] at selected
              | some pair =>
                  rw [dequeued] at selected
                  exact induction pair.2 result
                    (dequeueContextualEdge?_attemptLedger current pair ledger
                      dequeued)
                    (dequeueContextualEdge?_fairPending owned current pair fair
                      dequeued) selected
      | cons item rest =>
          simp only [items] at selected
          cases dequeued : dequeueContextualItem? current with
          | none => simp [dequeued] at selected
          | some pair =>
              rw [dequeued] at selected
              rcases pair with ⟨pivot, afterDequeue⟩
              simp only at selected
              cases processed :
                  processContextualItem? owned pivot afterDequeue with
              | none => simp [processed] at selected
              | some next =>
                  rw [processed] at selected
                  have afterLedger := dequeueContextualItem?_attemptLedger
                    current (pivot, afterDequeue) ledger dequeued
                  have shape := dequeueContextualItem?_fairShape current
                    afterDequeue item pivot rest items dequeued
                  have pivotEq := shape.1
                  subst item
                  exact induction next result
                    (processContextualItem?_attemptLedger owned pivot
                      afterDequeue next afterLedger processed)
                    (processContextualItem?_fairPending owned current
                      afterDequeue next pivot rest fair items shape.2.1
                      shape.2.2.1 shape.2.2.2.1 shape.2.2.2.2
                      afterLedger processed) selected

private theorem executePhaseCWorklist?_fairPending
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (fresh : PhaseCInitialFresh current.counter)
    (selected : executePhaseCWorklist? owned current = some result) :
    PhaseCFairPending owned result := by
  unfold executePhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, runEq⟩
  exact runPhaseCQueues?_fairPending owned _ entered result
    (beginPhaseCWorklist?_attemptLedger current entered fresh enteredEq)
    (beginPhaseCWorklist?_fairPending owned current entered enteredEq) runEq

private theorem executeObservedPhaseABCWorklist?_fairPending
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    PhaseCFairPending owned result := by
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, phaseBEq, phaseCEq⟩
  exact executePhaseCWorklist?_fairPending owned phaseB result
    (executeObservedPhaseAB?_phaseCInitialFresh file tokens owned phaseB
      phaseBEq) phaseCEq

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

private theorem executePhaseCWorklist?_queues_empty
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executePhaseCWorklist? owned current = some result) :
    result.payload.phaseC.itemQueue = [] ∧
      result.payload.phaseC.edgeQueue = [] := by
  unfold executePhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, runEq⟩
  exact runPhaseCQueues?_queues_empty owned _ entered result runEq

private theorem executeObservedPhaseABCWorklist?_operationalClosure
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (selected : executeObservedPhaseABCWorklist? file tokens owned =
      some result) :
    OperationalContextualClosure file tokens result.payload.phaseC.memo
      result.payload.phaseC.contextualItems
      result.payload.phaseC.contextualEdges := by
  have fair := executeObservedPhaseABCWorklist?_fairPending file tokens owned
    result selected
  unfold executeObservedPhaseABCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseB, phaseBEq, phaseCEq⟩
  have empty := executePhaseCWorklist?_queues_empty owned phaseB result phaseCEq
  refine ⟨by simpa [contextualRoot] using fair.1, ?_, ?_, ?_⟩
  · intro waiting predicted waitingMember next enabled
    let item : ContextualItemKey tokens := {
      raw := {
        production := predicted
        dot := ⟨0, Nat.zero_lt_succ _⟩
        origin := waiting.raw.current
        current := waiting.raw.current
      }
      context := descendContext waiting predicted
    }
    let productionInstance : ProductionInstanceKey tokens := {
      production := predicted
      origin := waiting.raw.current
      context := descendContext waiting predicted
    }
    have computed : contextualPredictedItem? waiting predicted =
        some (item, productionInstance) := by
      simpa [item, productionInstance] using
        contextualPredictedItem?_complete waiting predicted next
    rcases fair.2.1 waiting waitingMember predicted item productionInstance
        computed enabled with queued | materialized
    · simp [empty.1] at queued
    · exact materialized
  · intro before after cursor beforeMember structural
    obtain ⟨edge, computed, beforeEq, afterEq, cursorEq⟩ :=
      contextualScannedEdge?_complete owned before after cursor structural
    rcases fair.2.2.1 before beforeMember after edge computed with
      queued | materialized
    · simp [empty.1] at queued
    · refine ⟨materialized.1, ?_⟩
      simpa [beforeEq, afterEq, cursorEq] using materialized.2
  · intro waiting finished after shared waitingMember finishedMember structural
    obtain ⟨edge, computed, waitingEq, finishedEq, afterEq, sharedEq⟩ :=
      contextualCompletedEdge?_complete waiting finished after shared structural
    rcases fair.2.2.2 waiting waitingMember finished finishedMember after edge
        computed with queued | queued | materialized
    · simp [empty.1] at queued
    · simp [empty.1] at queued
    · refine ⟨materialized.1, ?_⟩
      simpa [waitingEq, finishedEq, afterEq, sharedEq] using materialized.2

/-- Every successful observed contextual worklist is extensionally closed
under all enabled predictions and all structurally valid scan/completion
steps. -/
theorem executeObservedContextualWorklist?_operationalClosure
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : ContextualWorklistResult file tokens)
    (selected : executeObservedContextualWorklist? file tokens owned =
      some result) :
    OperationalContextualClosure file tokens result.memo
      result.items result.edges := by
  unfold executeObservedContextualWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  exact executeObservedPhaseABCWorklist?_operationalClosure file tokens owned
    internal internalEq

end Chart

end Solcore.Surface.Multi

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

/-- Raw retained-symbol observation with its exact successor boundary. -/
def observedImmediatelyAfterRawSymbolBool
    {tokens : List Token} (symbol : Symbol)
    (boundary after : Boundary tokens) : Bool :=
  observedRawSymbolAtBool boundary symbol &&
    decide (after.val = boundary.val + 1)

/-- The first allowed symbol returning to one delimiter depth, generalized
from G06's fixed delimiter family for use by match-arm headers. -/
def observedNextSameDepthDelimiterBool
    (tokens : List Token) (start cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) : Bool :=
  observedSameDelimiterDepthBool tokens start cursor &&
    observedAllowedSymbolAtBool cursor allowed &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if start.val ≤ earlier.val && earlier.val < cursor.val &&
          observedSameDelimiterDepthBool tokens start earlier then
        !observedAllowedSymbolAtBool earlier allowed
      else
        true

/-- Public proof-free view of the canonical match-arm header oracle. -/
def observedSaturatedMatchArmHeaderObservation
    (tokens : List Token) : MatchArmHeaderObservation tokens :=
  fun regionStart cursor =>
    decide (regionStart.val ≤ cursor.val) &&
      observedSameDelimiterDepthBool tokens regionStart cursor &&
      observedRawSymbolAtBool cursor .pipe &&
      match observedBoundaryAt? tokens (cursor.val + 1) with
      | none => false
      | some patternStart =>
          observedImmediatelyAfterRawSymbolBool .pipe cursor patternStart &&
            (List.finRange (tokens.length + 2)).any fun arrowCursor =>
              observedNextSameDepthDelimiterBool tokens patternStart
                  arrowCursor ⟨.fatArrow, []⟩ &&
                saturatedRawGreatestEndObservation tokens
                  (.aux Grammar.matchArmPatternListSite.site)
                  patternStart arrowCursor arrowCursor

private theorem observedImmediatelyAfterRawSymbolBool_eq_phaseA
    {tokens : List Token} (symbol : Symbol)
    (boundary after : Boundary tokens) :
    observedImmediatelyAfterRawSymbolBool symbol boundary after =
      phaseAImmediatelyAfterSymbolBool symbol boundary after := by
  simp [observedImmediatelyAfterRawSymbolBool,
    phaseAImmediatelyAfterSymbolBool, observedRawSymbolAtBool_eq_phaseA]

private theorem observedSameDelimiterDepthBool_eq_phaseA
    (tokens : List Token) (start finish : Boundary tokens) :
    observedSameDelimiterDepthBool tokens start finish =
      phaseASameDelimiterDepthBool tokens start finish := by
  unfold observedSameDelimiterDepthBool phaseASameDelimiterDepthBool
  have run := phaseADelimiterRun?_observed tokens [] start finish
  simp only [List.map_nil] at run
  rw [← run]
  cases phaseADelimiterRun? tokens [] start finish <;> simp

private theorem observedNextSameDepthDelimiterBool_eq_phaseA
    (tokens : List Token) (start cursor : Boundary tokens)
    (allowed : NonemptyList Symbol) :
    observedNextSameDepthDelimiterBool tokens start cursor allowed =
      phaseANextSameDepthDelimiterBool tokens start cursor allowed := by
  simp only [observedNextSameDepthDelimiterBool,
    phaseANextSameDepthDelimiterBool,
    observedSameDelimiterDepthBool_eq_phaseA,
    observedAllowedSymbolAtBool_eq_phaseA]

/-- The public header view is definitionally faithful to the canonical raw
saturation oracle consumed by Phase B. -/
theorem saturatedMatchArmHeaderObservation_eq_observed
    (tokens : List Token) (regionStart cursor : Boundary tokens) :
    saturatedMatchArmHeaderObservation tokens regionStart cursor =
      observedSaturatedMatchArmHeaderObservation tokens
        regionStart cursor := by
  simp only [saturatedMatchArmHeaderObservation,
    observedSaturatedMatchArmHeaderObservation,
    observedSameDelimiterDepthBool_eq_phaseA,
    observedRawSymbolAtBool_eq_phaseA,
    observedBoundaryAt?_eq_phaseA,
    observedImmediatelyAfterRawSymbolBool_eq_phaseA,
    observedNextSameDepthDelimiterBool_eq_phaseA]

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

/-- Proof-free matching-brace bit used by the statement-region observer. -/
def observedMatchingBraceBool
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) : Bool :=
  observedRawSymbolAtBool openCursor .leftBrace &&
    observedRawSymbolAtBool closeCursor .rightBrace &&
    match observedBoundaryAt? tokens (openCursor.val + 1) with
    | none => false
    | some interiorStart =>
        decide (observedProtectedDelimiterRun? tokens [.rightBrace]
          interiorStart closeCursor = some [.rightBrace])

/-- A proof-free brace frame strictly containing one cursor. -/
def observedContainingBraceFrameBool
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Bool :=
  decide (openCursor.val < cursor.val) &&
    decide (cursor.val < closeCursor.val) &&
    observedMatchingBraceBool tokens openCursor closeCursor

/-- The proof-free containing brace frame with greatest opening cursor. -/
def observedInnermostContainingBraceFrameBool
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    Bool :=
  observedContainingBraceFrameBool tokens cursor openCursor closeCursor &&
    (List.finRange (tokens.length + 2)).all fun otherOpen =>
      (List.finRange (tokens.length + 2)).all fun otherClose =>
        !observedContainingBraceFrameBool tokens cursor otherOpen otherClose ||
          decide (otherOpen.val ≤ openCursor.val)

/-- Public proof-free next-arm-or-close view over canonical raw saturation. -/
def observedSaturatedNextArmOrCloseBool
    (tokens : List Token)
    (regionStart closeCursor regionEnd : Boundary tokens) : Bool :=
  decide (regionStart.val ≤ regionEnd.val) &&
    decide (regionEnd.val ≤ closeCursor.val) &&
    observedSameDelimiterDepthBool tokens regionStart regionEnd &&
    (decide (regionEnd = closeCursor) ||
      observedSaturatedMatchArmHeaderObservation tokens
        regionStart regionEnd) &&
    (List.finRange (tokens.length + 2)).all fun earlier =>
      if regionStart.val ≤ earlier.val &&
          earlier.val < regionEnd.val &&
          observedSameDelimiterDepthBool tokens regionStart earlier then
        !(decide (earlier = closeCursor) ||
          observedSaturatedMatchArmHeaderObservation tokens
            regionStart earlier)
      else
        true

/-- Public proof-free view of the canonical nearest statement-region oracle. -/
def observedSaturatedStatementRegionObservation
    (tokens : List Token) : StatementRegionObservation tokens :=
  fun regionStart regionEnd =>
    let bracedBody :=
      (List.finRange (tokens.length + 2)).any fun openCursor =>
        observedImmediatelyAfterRawSymbolBool .leftBrace openCursor
            regionStart &&
          observedMatchingBraceBool tokens openCursor regionEnd
    let armBody :=
      (List.finRange (tokens.length + 2)).any fun arrowCursor =>
        observedImmediatelyAfterRawSymbolBool .fatArrow arrowCursor
            regionStart &&
          (List.finRange (tokens.length + 2)).any fun openCursor =>
            (List.finRange (tokens.length + 2)).any fun closeCursor =>
              observedInnermostContainingBraceFrameBool tokens arrowCursor
                  openCursor closeCursor &&
                observedSaturatedNextArmOrCloseBool tokens regionStart
                  closeCursor regionEnd
    bracedBody || armBody

private theorem phaseADelimiterCloser_map_eq_rightBrace_iff
    (values : PhaseADelimiterStack) :
    values.map PhaseADelimiterCloser.observed = [.rightBrace] ↔
      values = [.rightBrace] := by
  cases values with
  | nil => simp
  | cons head tail =>
      cases head <;> cases tail <;>
        simp [PhaseADelimiterCloser.observed]

private theorem phaseAMatchingBraceBool_eq_observed
    (tokens : List Token) (openCursor closeCursor : Boundary tokens) :
    phaseAMatchingDelimiterBool tokens openCursor closeCursor
        .leftBrace .rightBrace =
      observedMatchingBraceBool tokens openCursor closeCursor := by
  unfold phaseAMatchingDelimiterBool phaseADelimiterPair?
    observedMatchingBraceBool
  simp only [decide_true, Bool.true_and,
    observedRawSymbolAtBool_eq_phaseA, observedBoundaryAt?_eq_phaseA]
  cases boundary : phaseABoundaryAt? tokens (openCursor.val + 1)
  · rfl
  · rename_i interiorStart
    change (phaseASymbolAtBool openCursor .leftBrace &&
        phaseASymbolAtBool closeCursor .rightBrace &&
        decide (phaseAProtectedDelimiterRun? tokens [.rightBrace]
          interiorStart closeCursor = some [.rightBrace])) =
      (phaseASymbolAtBool openCursor .leftBrace &&
        phaseASymbolAtBool closeCursor .rightBrace &&
        decide (observedProtectedDelimiterRun? tokens [.rightBrace]
          interiorStart closeCursor = some [.rightBrace]))
    have run := phaseAProtectedDelimiterRun?_observed tokens
      [.rightBrace] interiorStart closeCursor
    simp only [PhaseADelimiterCloser.observed, List.map_cons,
      List.map_nil] at run
    rw [← run]
    cases phaseAProtectedDelimiterRun? tokens [.rightBrace]
      interiorStart closeCursor with
    | none => simp
    | some values =>
        simp only [Option.map_some, Option.some.injEq,
          phaseADelimiterCloser_map_eq_rightBrace_iff]

private theorem phaseAInnermostContainingBraceFrameBool_eq_observed
    (tokens : List Token) (cursor openCursor closeCursor : Boundary tokens) :
    phaseAInnermostContainingBraceFrameBool tokens cursor openCursor
        closeCursor =
      observedInnermostContainingBraceFrameBool tokens cursor openCursor
        closeCursor := by
  simp only [phaseAInnermostContainingBraceFrameBool,
    phaseAContainingBraceFrameBool,
    observedInnermostContainingBraceFrameBool,
    observedContainingBraceFrameBool,
    phaseAMatchingBraceBool_eq_observed]

private theorem saturatedNextArmOrCloseBool_eq_observed
    (tokens : List Token)
    (regionStart closeCursor regionEnd : Boundary tokens) :
    saturatedNextArmOrCloseBool tokens regionStart closeCursor regionEnd =
      observedSaturatedNextArmOrCloseBool tokens regionStart closeCursor
        regionEnd := by
  simp only [saturatedNextArmOrCloseBool,
    observedSaturatedNextArmOrCloseBool,
    observedSameDelimiterDepthBool_eq_phaseA,
    saturatedMatchArmHeaderObservation_eq_observed]

/-- The public statement-region view is definitionally faithful to the
canonical raw-saturation oracle consumed by Phase B. -/
theorem saturatedStatementRegionObservation_eq_observed
    (tokens : List Token) (regionStart regionEnd : Boundary tokens) :
    saturatedStatementRegionObservation tokens regionStart regionEnd =
      observedSaturatedStatementRegionObservation tokens
        regionStart regionEnd := by
  simp only [saturatedStatementRegionObservation,
    observedSaturatedStatementRegionObservation,
    observedImmediatelyAfterRawSymbolBool_eq_phaseA,
    phaseAMatchingBraceBool_eq_observed,
    phaseAInnermostContainingBraceFrameBool_eq_observed,
    saturatedNextArmOrCloseBool_eq_observed]

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

private theorem contextualLinearKey_injective {tokens : List Token} :
    Function.Injective (contextualLinearKey (tokens := tokens)) := by
  intro left right equal
  have raw : left.raw = right.raw := dottedItem_eq_of_fields
    (congrArg (fun key => key.dotted.production) equal)
    (congrArg (fun key => key.dotted.dot.val) equal)
    (congrArg (fun key => key.origin) equal)
    (congrArg (fun key => key.current) equal)
  have context : left.context = right.context := by
    have source := congrArg ChartLinearKey.source equal
    simpa [contextualLinearKey] using source
  exact contextualItem_eq_of_fields raw context

private structure PhaseCItemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens)) : Prop where
  inserted : ∀ (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens),
    (.linear source.unitKind (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev →
    item ∈ current.payload.phaseC.contextualItems
  dequeued : ∀ item,
    (.linear .L01_itemDequeue (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev →
    item ∈ current.payload.phaseC.contextualItems
  predicted : ∀ item production,
    (.prediction .R01_predictionAttempt
      (contextualPredictionKey item production) : UnitAddress tokens) ∈
        current.counter.usedRev →
    (.linear .L01_itemDequeue (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev
  scanned : ∀ item,
    (.linear .L04_scanAttempt (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev →
    (.linear .L01_itemDequeue (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev
  scannedEdge : ∀ item,
    (.linear .L06_scannedEdgeInsert (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev →
    (.linear .L01_itemDequeue (contextualLinearKey item) :
      UnitAddress tokens) ∈ current.counter.usedRev
  queueFresh : ∀ item, item ∈ current.payload.phaseC.itemQueue →
    (.linear .L01_itemDequeue (contextualLinearKey item) :
      UnitAddress tokens) ∉ current.counter.usedRev
  itemsNodup : current.payload.phaseC.contextualItems.Nodup
  queueNodup : current.payload.phaseC.itemQueue.Nodup
  queueSubset : current.payload.phaseC.itemQueue ⊆
    current.payload.phaseC.contextualItems

private theorem beginPhaseCWorklist?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBSealed file tokens))
    (result : CountedState tokens (PhaseCWorklist file tokens))
    (fresh : PhaseCInitialFresh current.counter)
    (selected : beginPhaseCWorklist? current = some result) :
    PhaseCItemSafe result := by
  unfold beginPhaseCWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨entered, enteredEq, resultEq⟩
  cases resultEq
  unfold enterPhaseC? at enteredEq
  have payload := runMappedPrimitive?_payload current _ _ enteredEq
  have used := runMappedPrimitive?_usedRev current _ _ entered enteredEq
  constructor
  · intro source item member
    rw [used, List.mem_cons] at member
    rcases member with equal | old
    · cases source with
      | prediction =>
          simp only [ContextualItemInsertSource.unitKind,
            UnitAddress.linear.injEq, true_and] at equal
          have itemEq := contextualLinearKey_injective equal
          rw [itemEq, payload]
          simp
      | scan => simp [ContextualItemInsertSource.unitKind] at equal
      | completion => simp [ContextualItemInsertSource.unitKind] at equal
    · exact (fresh _ (by
        cases source <;>
          simp [phaseCInitialAddress, contextualLinearKey])).elim old
  · intro item member
    rw [used, List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · exact (fresh _ (by
        simp [phaseCInitialAddress, contextualLinearKey])).elim old
  · intro item production member
    rw [used, List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · exact (fresh _ (by
        simp [phaseCInitialAddress, contextualPredictionKey])).elim old
  · intro item member
    rw [used, List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · exact (fresh _ (by
        simp [phaseCInitialAddress, contextualLinearKey])).elim old
  · intro item member
    rw [used, List.mem_cons] at member
    rcases member with equal | old
    · simp at equal
    · exact (fresh _ (by
        simp [phaseCInitialAddress, contextualLinearKey])).elim old
  · intro item member usedItem
    rw [payload] at member
    simp only [List.mem_singleton] at member
    subst item
    rw [used, List.mem_cons] at usedItem
    rcases usedItem with equal | old
    · simp at equal
    · exact fresh _ (by
        simp [phaseCInitialAddress, contextualLinearKey]) old
  · simp [payload]
  · simp [payload]
  · intro item member
    simpa [payload] using member

private theorem insertContextualItem?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (safe : PhaseCItemSafe current)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCItemSafe result := by
  unfold insertContextualItem? at selected
  split at selected
  next present =>
    cases selected
    exact safe
  next absent =>
    have payload := runMappedPrimitive?_payload current _ _ selected
    have used := runMappedPrimitive?_usedRev current _ _ result selected
    have itemAbsent : item ∉ current.payload.phaseC.contextualItems := by
      intro member
      exact absent ((phaseCItemMemberBool_true_iff _ item).mpr member)
    constructor
    · intro candidateSource candidate member
      rw [used, List.mem_cons] at member
      rcases member with equal | old
      · simp only [UnitAddress.linear.injEq] at equal
        have keys : contextualLinearKey candidate =
            contextualLinearKey item := equal.2
        rw [contextualLinearKey_injective keys, payload]
        simp
      · rw [payload]
        exact List.mem_append_left _
          (safe.inserted candidateSource candidate old)
    · intro candidate member
      rw [used, List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [ContextualItemInsertSource.unitKind] at equal
      · rw [payload]
        exact List.mem_append_left _ (safe.dequeued candidate old)
    · intro candidate production member
      rw [used, List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [ContextualItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _
          (safe.predicted candidate production old)
    · intro candidate member
      rw [used, List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [ContextualItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scanned candidate old)
    · intro candidate member
      rw [used, List.mem_cons] at member
      rcases member with equal | old
      · cases source <;>
          simp [ContextualItemInsertSource.unitKind] at equal
      · rw [used]
        exact List.mem_cons_of_mem _ (safe.scannedEdge candidate old)
    · intro candidate member usedCandidate
      rw [payload] at member
      simp only [List.mem_append, List.mem_singleton] at member
      rw [used, List.mem_cons] at usedCandidate
      rcases member with oldMember | equal
      · rcases usedCandidate with collision | oldUsed
        · cases source <;>
            simp [ContextualItemInsertSource.unitKind] at collision
        · exact safe.queueFresh candidate oldMember oldUsed
      · subst candidate
        rcases usedCandidate with collision | oldUsed
        · cases source <;>
            simp [ContextualItemInsertSource.unitKind] at collision
        · exact itemAbsent (safe.dequeued item oldUsed)
    · rw [payload, List.nodup_append]
      refine ⟨safe.itemsNodup, by simp, ?_⟩
      intro candidate member singleton singletonMember equal
      have singletonEq : singleton = item :=
        List.eq_of_mem_singleton singletonMember
      apply itemAbsent
      rw [← singletonEq, ← equal]
      exact member
    · rw [payload]
      have notQueued : item ∉ current.payload.phaseC.itemQueue :=
        fun member => itemAbsent (safe.queueSubset member)
      rw [List.nodup_append]
      refine ⟨safe.queueNodup, by simp, ?_⟩
      intro candidate member singleton singletonMember equal
      have singletonEq : singleton = item :=
        List.eq_of_mem_singleton singletonMember
      apply notQueued
      rw [← singletonEq, ← equal]
      exact member
    · intro candidate member
      rw [payload] at member ⊢
      simp only [List.mem_append, List.mem_singleton] at member ⊢
      exact member.elim (fun old => Or.inl (safe.queueSubset old)) Or.inr

private theorem insertContextualItem?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (safe : PhaseCItemSafe current) :
    ∃ result, insertContextualItem? current source item = some result := by
  unfold insertContextualItem?
  split
  next present => exact ⟨current, rfl⟩
  next absent =>
    have fresh : (.linear source.unitKind (contextualLinearKey item) :
        UnitAddress tokens) ∉ current.counter.usedRev := by
      intro used
      exact absent ((phaseCItemMemberBool_true_iff _ item).mpr
        (safe.inserted source item used))
    simp [runMappedPrimitive?, fresh]

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

/-- Phase C preserves the exact canonical guard memo produced by the
successful observed Phase-A/Phase-B prefix. -/
theorem executeObservedContextualWorklist?_memo_eq_saturated
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    (result : ContextualWorklistResult file tokens)
    (selected : executeObservedContextualWorklist? file tokens owned =
      some result) :
    result.memo = saturatedGuardMemo owned := by
  unfold executeObservedContextualWorklist? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨internal, internalEq, resultEq⟩
  cases resultEq
  unfold executeObservedPhaseABCWorklist? at internalEq
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at internalEq
  rcases internalEq with ⟨phaseB, phaseBEq, phaseCEq⟩
  have memoPreserved :=
    (executePhaseCWorklist?_operationalInvariant owned phaseB internal
      phaseCEq).2
  let guardResult : GuardWorklistResult tokens := {
    memo := phaseB.payload.memo
  }
  have guardSelected :
      executeObservedGuardWorklist? file tokens owned =
        some guardResult := by
    unfold executeObservedGuardWorklist?
    rw [phaseBEq]
    rfl
  have canonical := executeObservedGuardWorklist?_memo_eq_saturated
    file tokens owned guardResult guardSelected
  change internal.payload.phaseC.memo = saturatedGuardMemo owned
  exact memoPreserved.trans (by simpa [guardResult] using canonical)

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

private theorem dequeueContextualItem?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (result : ContextualItemKey tokens ×
      CountedState tokens (PhaseCWorklist file tokens))
    (safe : PhaseCItemSafe current)
    (selected : dequeueContextualItem? current = some result) :
    PhaseCItemSafe result.2 := by
  unfold dequeueContextualItem? at selected
  cases queue : current.payload.phaseC.itemQueue with
  | nil => simp [queue] at selected
  | cons head rest =>
      simp only [queue, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, output⟩
      cases output
      have payload := runMappedPrimitive?_payload current _ _ nextEq
      have used := runMappedPrimitive?_usedRev current _ _ next nextEq
      have unique : head ∉ rest ∧ rest.Nodup := by
        have queueNodup := safe.queueNodup
        rw [queue, List.nodup_cons] at queueNodup
        exact queueNodup
      constructor
      · intro source item member
        rw [used, List.mem_cons] at member
        rcases member with equal | old
        · cases source <;>
            simp [ContextualItemInsertSource.unitKind] at equal
        · rw [payload]
          exact safe.inserted source item old
      · intro item member
        rw [used, List.mem_cons] at member
        rcases member with equal | old
        · simp only [UnitAddress.linear.injEq] at equal
          rw [contextualLinearKey_injective equal.2, payload]
          exact safe.queueSubset (by simp [queue])
        · rw [payload]
          exact safe.dequeued item old
      · intro item production member
        rw [used, List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.predicted item production old)
      · intro item member
        rw [used, List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.scanned item old)
      · intro item member
        rw [used, List.mem_cons] at member
        rcases member with equal | old
        · simp at equal
        · rw [used]
          exact List.mem_cons_of_mem _ (safe.scannedEdge item old)
      · intro item member usedItem
        rw [payload] at member
        rw [used, List.mem_cons] at usedItem
        rcases usedItem with collision | old
        · simp only [UnitAddress.linear.injEq] at collision
          have same := contextualLinearKey_injective collision.2
          exact unique.1 (same ▸ member)
        · exact safe.queueFresh item (by simp [queue, member]) old
      · simpa [payload] using safe.itemsNodup
      · simpa [payload] using unique.2
      · intro item member
        rw [payload] at member ⊢
        exact safe.queueSubset (by simp [queue, member])

private structure PhaseCItemWorkFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (item : ContextualItemKey tokens) : Prop where
  dequeued : (.linear .L01_itemDequeue (contextualLinearKey item) :
    UnitAddress tokens) ∈ current.counter.usedRev
  predictions : ∀ production,
    (.prediction .R01_predictionAttempt
      (contextualPredictionKey item production) : UnitAddress tokens) ∉
        current.counter.usedRev
  scan : (.linear .L04_scanAttempt (contextualLinearKey item) :
    UnitAddress tokens) ∉ current.counter.usedRev
  scannedEdge : (.linear .L06_scannedEdgeInsert
    (contextualLinearKey item) : UnitAddress tokens) ∉
      current.counter.usedRev

private theorem dequeueContextualItem?_workFresh
    {file : WorkspaceFile} {tokens : List Token}
    (current after : CountedState tokens (PhaseCWorklist file tokens))
    (item : ContextualItemKey tokens)
    (rest : List (ContextualItemKey tokens))
    (queue : current.payload.phaseC.itemQueue = item :: rest)
    (safe : PhaseCItemSafe current)
    (selected : dequeueContextualItem? current = some (item, after)) :
    PhaseCItemWorkFresh after item := by
  unfold dequeueContextualItem? at selected
  simp only [queue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at selected
  rcases selected with ⟨next, nextEq, output⟩
  simp only [pure, Option.some.injEq, Prod.mk.injEq, true_and] at output
  subst next
  have used := runMappedPrimitive?_usedRev current _ _ after nextEq
  have dequeueFresh := safe.queueFresh item (by simp [queue])
  constructor
  · rw [used]
    simp
  · intro production member
    rw [used, List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.predicted item production old)
  · intro member
    rw [used, List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.scanned item old)
  · intro member
    rw [used, List.mem_cons] at member
    rcases member with collision | old
    · simp at collision
    · exact dequeueFresh (safe.scannedEdge item old)

private theorem dequeueContextualItem?_total
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (item : ContextualItemKey tokens)
    (rest : List (ContextualItemKey tokens))
    (queue : current.payload.phaseC.itemQueue = item :: rest)
    (safe : PhaseCItemSafe current) :
    ∃ after, dequeueContextualItem? current = some (item, after) := by
  have fresh := safe.queueFresh item (by simp [queue])
  unfold dequeueContextualItem?
  rw [queue]
  simp [runMappedPrimitive?, fresh]

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

private def PhaseCActivationSafe {tokens : List Token}
    (counter : Counter tokens) : Prop :=
  ∀ productionInstance index slot,
    UnitAddress.guardWitness slot
      (guardCellAddress productionInstance index) ∈ counter.usedRev →
    UnitAddress.production productionInstance ∈ counter.usedRev

private theorem productionInstance_eq_of_guardCellAddress_eq
    {tokens : List Token}
    {left right : ProductionInstanceKey tokens}
    {leftIndex : Fin (guardOf left.production).length}
    {rightIndex : Fin (guardOf right.production).length}
    (equal : guardCellAddress left leftIndex =
      guardCellAddress right rightIndex) :
    left = right := by
  cases left
  cases right
  simp only [guardCellAddress, Prod.mk.injEq] at equal
  simp_all

private theorem chargeAddresses?_usedRev
    {tokens : List Token} {state : Type} :
    ∀ addresses (current result : CountedState tokens state),
      chargeAddresses? current addresses = some result →
      result.counter.usedRev =
        addresses.reverse ++ current.counter.usedRev := by
  intro addresses
  induction addresses with
  | nil =>
      intro current result selected
      cases selected
      simp
  | cons address rest induction =>
      intro current result selected
      rw [chargeAddresses?] at selected
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
      rcases selected with ⟨next, nextEq, continued⟩
      rw [induction next result continued,
        runMappedPrimitive?_usedRev current address id next nextEq]
      simp [List.reverse_cons, List.append_assoc]

private theorem runMappedPrimitive?_activationSafe_of_not_witness
    {tokens : List Token} {before after : Type}
    (current : CountedState tokens before)
    (address : UnitAddress tokens) (transition : before → after)
    (result : CountedState tokens after)
    (safe : PhaseCActivationSafe current.counter)
    (notWitness : ∀ productionInstance index slot,
      address ≠ UnitAddress.guardWitness slot
        (guardCellAddress productionInstance index))
    (selected : runMappedPrimitive? current address transition =
      some result) :
    PhaseCActivationSafe result.counter := by
  intro productionInstance index slot member
  rw [runMappedPrimitive?_usedRev current address transition result selected,
    List.mem_cons] at member ⊢
  rcases member with equal | old
  · exact (notWitness productionInstance index slot equal.symm).elim
  · exact Or.inr (safe productionInstance index slot old)

private theorem PhaseCInitialFresh.activationSafe
    {tokens : List Token} {counter : Counter tokens}
    (fresh : PhaseCInitialFresh counter) :
    PhaseCActivationSafe counter := by
  intro productionInstance index slot member
  exact (fresh (.guardWitness slot
    (guardCellAddress productionInstance index))
      (by simp [phaseCInitialAddress])).elim member

private theorem processGuardCell?_activationSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (safe : PhaseCActivationSafe current.counter)
    (activated : UnitAddress.production productionInstance ∈
      current.counter.usedRev)
    (selected : processGuardCell? current productionInstance index =
      some result) :
    PhaseCActivationSafe result.1.counter ∧
      UnitAddress.production productionInstance ∈
        result.1.counter.usedRev := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  have inspectedUsed := chargeAddresses?_usedRev _ current inspected
    inspectedEq
  have insertedUsed := runMappedPrimitive?_usedRev inspected _ _ inserted
    insertedEq
  have oldSubset : current.counter.usedRev ⊆ inserted.counter.usedRev := by
    intro address member
    rw [insertedUsed, inspectedUsed]
    simp [member]
  have activatedResult := oldSubset activated
  refine ⟨?_, activatedResult⟩
  intro candidate candidateIndex slot member
  rw [insertedUsed, List.mem_cons] at member
  rcases member with insertedMember | inspectedMember
  · have sameAddress :=
      (UnitAddress.guardWitness.inj insertedMember).2
    have sameProduction := productionInstance_eq_of_guardCellAddress_eq
      sameAddress
    subst candidate
    exact activatedResult
  · rw [inspectedUsed, List.mem_append, List.mem_reverse] at inspectedMember
    rcases inspectedMember with lookup | old
    · simp only [List.mem_map] at lookup
      rcases lookup with ⟨headSlot, _slotMember, equal⟩
      have sameAddress := (UnitAddress.guardWitness.inj equal).2
      have sameProduction := productionInstance_eq_of_guardCellAddress_eq
        sameAddress
      subst candidate
      exact activatedResult
    · exact oldSubset (safe candidate candidateIndex slot old)

private theorem processGuardCells?_activationSafe
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ indices
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      PhaseCActivationSafe current.counter →
      UnitAddress.production productionInstance ∈
        current.counter.usedRev →
      processGuardCells? productionInstance indices current = some result →
      PhaseCActivationSafe result.1.counter ∧
        UnitAddress.production productionInstance ∈
          result.1.counter.usedRev := by
  intro indices
  induction indices with
  | nil =>
      intro current result safe activated selected
      cases selected
      exact ⟨safe, activated⟩
  | cons index rest induction =>
      intro current result safe activated selected
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨next, nextEq, finished, finishedEq, resultEq⟩
      cases resultEq
      have nextSafe := processGuardCell?_activationSafe current
        productionInstance index next safe activated nextEq
      exact induction next.1 finished nextSafe.1 nextSafe.2 finishedEq

private theorem activateProduction?_activationSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (safe : PhaseCActivationSafe current.counter)
    (selected : activateProduction? current productionInstance = some result) :
    PhaseCActivationSafe result.1.counter := by
  unfold activateProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨attempted, attemptedEq, processedEq⟩
  have attemptedSafe :=
    runMappedPrimitive?_activationSafe_of_not_witness current
      (.production productionInstance) id attempted safe (by simp)
        attemptedEq
  have activated : UnitAddress.production productionInstance ∈
      attempted.counter.usedRev := by
    rw [runMappedPrimitive?_usedRev current _ id attempted attemptedEq]
    simp
  exact (processGuardCells?_activationSafe productionInstance _ attempted
    result attemptedSafe activated processedEq).1

private theorem activateWorklistProduction?_activationSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (safe : PhaseCActivationSafe current.counter)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCActivationSafe result.1.counter := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  exact activateProduction?_activationSafe {
    payload := current.payload.phaseC
    counter := current.counter
  } productionInstance activated safe activatedEq

end Solcore.Surface.Multi.Chart

namespace Solcore.Surface.Multi.Chart

open Grammar
open Solcore.Workspace

private theorem processGuardCell?_nonActivationAddress
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (target : UnitAddress tokens)
    (notWitness : ∀ slot, target ≠ UnitAddress.guardWitness slot
      (guardCellAddress productionInstance index))
    (selected : processGuardCell? current productionInstance index =
      some result) :
    target ∈ result.1.counter.usedRev →
      target ∈ current.counter.usedRev := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  rw [runMappedPrimitive?_usedRev inspected _ _ inserted insertedEq,
    List.mem_cons]
  rintro (equal | member)
  · exact (notWitness .insertWitness equal).elim
  · rw [chargeAddresses?_usedRev _ current inspected inspectedEq,
      List.mem_append, List.mem_reverse] at member
    rcases member with lookup | old
    · simp only [List.mem_map] at lookup
      rcases lookup with ⟨slot, _slotMember, equal⟩
      exact (notWitness slot equal.symm).elim
    · exact old

private theorem processGuardCells?_nonActivationAddress
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ indices
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
      (target : UnitAddress tokens),
      (∀ index, index ∈ indices → ∀ slot,
        target ≠ UnitAddress.guardWitness slot
          (guardCellAddress productionInstance index)) →
      processGuardCells? productionInstance indices current = some result →
      target ∈ result.1.counter.usedRev →
      target ∈ current.counter.usedRev := by
  intro indices
  induction indices with
  | nil =>
      intro current result target _notWitness selected member
      cases selected
      exact member
  | cons index rest induction =>
      intro current result target notWitness selected member
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨next, nextEq, finished, finishedEq, resultEq⟩
      cases resultEq
      apply processGuardCell?_nonActivationAddress current
        productionInstance index next target
        (notWitness index (by simp)) nextEq
      exact induction next.1 finished target
        (fun candidate candidateMember =>
          notWitness candidate (by simp [candidateMember]))
        finishedEq member

private theorem activateWorklistProduction?_nonActivationAddress
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (target : UnitAddress tokens)
    (notProduction : target ≠ UnitAddress.production productionInstance)
    (notWitness : ∀ index slot, target ≠ UnitAddress.guardWitness slot
      (guardCellAddress productionInstance index))
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    target ∈ result.1.counter.usedRev →
      target ∈ current.counter.usedRev := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  unfold activateProduction? at activatedEq
  rcases Option.bind_eq_some_iff.mp activatedEq with
    ⟨attempted, attemptedEq, processedEq⟩
  intro member
  have attemptedMember := processGuardCells?_nonActivationAddress
    productionInstance _ attempted activated target
      (fun index _member => notWitness index) processedEq member
  rw [runMappedPrimitive?_usedRev
    { payload := current.payload.phaseC, counter := current.counter }
    (.production productionInstance) id attempted attemptedEq,
    List.mem_cons] at attemptedMember
  exact attemptedMember.elim (fun equal => (notProduction equal).elim) id

private theorem processGuardCell?_used_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCOpen file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (index : Fin (guardOf productionInstance.production).length)
    (result : CountedState tokens (PhaseCOpen file tokens) × Bool)
    (selected : processGuardCell? current productionInstance index =
      some result) :
    current.counter.usedRev ⊆ result.1.counter.usedRev := by
  unfold processGuardCell? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with
    ⟨inspected, inspectedEq, inserted, insertedEq, resultEq⟩
  cases resultEq
  intro address member
  rw [runMappedPrimitive?_usedRev inspected _ _ inserted insertedEq,
    chargeAddresses?_usedRev _ current inspected inspectedEq]
  simp [member]

private theorem processGuardCells?_used_mono
    {file : WorkspaceFile} {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens) :
    ∀ indices
      (current : CountedState tokens (PhaseCOpen file tokens))
      (result : CountedState tokens (PhaseCOpen file tokens) × Bool),
      processGuardCells? productionInstance indices current = some result →
      current.counter.usedRev ⊆ result.1.counter.usedRev := by
  intro indices
  induction indices with
  | nil =>
      intro current result selected
      cases selected
      exact fun _ => id
  | cons index rest induction =>
      intro current result selected
      simp only [processGuardCells?, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at selected
      rcases selected with
        ⟨next, nextEq, finished, finishedEq, resultEq⟩
      cases resultEq
      intro address member
      exact induction next.1 finished finishedEq
        (processGuardCell?_used_mono current productionInstance index next
          nextEq member)

private theorem activateWorklistProduction?_used_mono
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    current.counter.usedRev ⊆ result.1.counter.usedRev := by
  unfold activateWorklistProduction? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨activated, activatedEq, resultEq⟩
  cases resultEq
  unfold activateProduction? at activatedEq
  rcases Option.bind_eq_some_iff.mp activatedEq with
    ⟨attempted, attemptedEq, processedEq⟩
  intro address member
  apply processGuardCells?_used_mono productionInstance _ attempted activated
    processedEq
  rw [runMappedPrimitive?_usedRev
    { payload := current.payload.phaseC, counter := current.counter }
    (.production productionInstance) id attempted attemptedEq]
  exact List.mem_cons_of_mem _ member

private theorem activateWorklistProduction?_itemSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseCWorklist file tokens))
    (productionInstance : ProductionInstanceKey tokens)
    (result : CountedState tokens (PhaseCWorklist file tokens) × Bool)
    (safe : PhaseCItemSafe current)
    (selected : activateWorklistProduction? current productionInstance =
      some result) :
    PhaseCItemSafe result.1 := by
  have carrier := activateWorklistProduction?_reachCarrier current
    productionInstance result selected
  have itemsEq := congrArg PhaseCReachCarrier.items carrier
  have queueEq := congrArg PhaseCReachCarrier.itemQueue carrier
  change result.1.payload.phaseC.contextualItems =
    current.payload.phaseC.contextualItems at itemsEq
  change result.1.payload.phaseC.itemQueue =
    current.payload.phaseC.itemQueue at queueEq
  have usedMono := activateWorklistProduction?_used_mono current
    productionInstance result selected
  constructor
  · intro source item member
    rw [itemsEq]
    exact safe.inserted source item
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected member)
  · intro item member
    rw [itemsEq]
    exact safe.dequeued item
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected member)
  · intro item production member
    apply usedMono
    exact safe.predicted item production
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected member)
  · intro item member
    apply usedMono
    exact safe.scanned item
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected member)
  · intro item member
    apply usedMono
    exact safe.scannedEdge item
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected member)
  · intro item member used
    rw [queueEq] at member
    exact safe.queueFresh item member
      (activateWorklistProduction?_nonActivationAddress current
        productionInstance result _ (by simp) (by simp) selected used)
  · rw [itemsEq]
    exact safe.itemsNodup
  · rw [queueEq]
    exact safe.queueNodup
  · intro item member
    rw [queueEq] at member
    rw [itemsEq]
    exact safe.queueSubset member

private theorem insertContextualItem?_activationSafe
    {file : WorkspaceFile} {tokens : List Token}
    (current result : CountedState tokens (PhaseCWorklist file tokens))
    (source : ContextualItemInsertSource)
    (item : ContextualItemKey tokens)
    (safe : PhaseCActivationSafe current.counter)
    (selected : insertContextualItem? current source item = some result) :
    PhaseCActivationSafe result.counter := by
  unfold insertContextualItem? at selected
  split at selected
  next present => cases selected; exact safe
  next absent =>
    exact runMappedPrimitive?_activationSafe_of_not_witness current _ _ result
      safe (by simp) selected

end Solcore.Surface.Multi.Chart
