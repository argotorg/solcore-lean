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

end Chart

namespace Chart

open Grammar
open Solcore.Workspace

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

private def AllGuardMemosFinal
    {file : WorkspaceFile} {tokens : List Token}
    (state : PhaseBSealed file tokens) : Prop :=
  ∀ key, ∃ decision, state.memo key = .final decision

private theorem sealIndexedPhaseB?_allFinal
    {file : WorkspaceFile} {tokens : List Token}
    (current : CountedState tokens (PhaseBIndexed file tokens))
    (result : CountedState tokens (PhaseBSealed file tokens))
    (invariant : PhaseBFinalizationInvariant current.payload)
    (selected : sealIndexedPhaseB? current = some result) :
    AllGuardMemosFinal result.payload := by
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
    AllGuardMemosFinal result.payload := by
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
    AllGuardMemosFinal result.payload := by
  unfold executeObservedPhaseAB? at selected
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at selected
  rcases selected with ⟨phaseA, phaseASelected,
    indexed, indexedSelected, phaseBSelected⟩
  exact executeIndexedPhaseB?_allFinal indexed result phaseBSelected

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

end Solcore.Surface.Multi
