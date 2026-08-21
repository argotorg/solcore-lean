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

end Solcore.Surface.Multi
