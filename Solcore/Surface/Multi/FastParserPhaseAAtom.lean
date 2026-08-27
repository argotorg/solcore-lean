import Solcore.Surface.Multi.FastParserPhaseATerminal

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-!
Canonical atom-production scans derived from the terminal Phase-A table.

Every successful terminal-atom fact determines the dot-zero item, the
one-symbol completed item, and the checked scan edge between them.  The
construction is local to terminal atom productions; it does not yet perform
prediction, nonterminal completion, guard evaluation, or root selection.

`PrefixValues` is indexed by a `ContextualItemKey`, so the semantic adapter
below uses the plain context as a type-level carrier.  This does not assert
contextual reachability, chart membership, or a Phase-C reduction.
-/

private theorem transport_zero_scan_complete_single
    {file : WorkspaceFile} {tokens : List Token}
    {prior scanned full : List GrammarSymbol}
    {source target : GrammarSymbol}
    (zeroLayout : [] = prior)
    (scanLayout : prior ++ [source] = scanned)
    (completeLayout : scanned = full)
    (viewLayout : full = [target])
    (symbolLayout : source = target)
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport completeLayout
          (GrammarSymbolValues.transport scanLayout
            (GrammarSymbolValues.append
              (GrammarSymbolValues.transport zeroLayout ())
              (value, ())))) =
      (Eq.mp
        (congrArg (GrammarSymbolValue file tokens) symbolLayout) value,
        ()) := by
  subst prior
  subst scanned
  subst full
  subst target
  simp [GrammarSymbolValues.transport_self,
    GrammarSymbolValues.append]
  rfl

private theorem transport_type_cycle
    {first second third : Type}
    (left : first = second) (middle : second = third)
    (right : third = first) (value : first) :
    Eq.mp right (Eq.mp middle (Eq.mp left value)) = value := by
  cases left
  cases middle
  rfl

private theorem mapped_values_nodup
    {alpha beta : Type} (function : alpha → beta)
    (values : List alpha) (unique : values.Nodup)
    (injective : Function.Injective function) :
    (values.map function).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at unique ⊢
  rw [List.pairwise_map]
  exact unique.imp fun different equal => different (injective equal)

private theorem fastTerminalWorkItem_eq_of_fields
    {tokens : List Token}
    {left right : FastTerminalWorkItem tokens}
    (atomEqual : left.atom = right.atom)
    (cursorEqual : left.cursor = right.cursor) :
    left = right := by
  rcases left with ⟨leftAtom, leftCursor⟩
  rcases right with ⟨rightAtom, rightCursor⟩
  simp only at atomEqual cursorEqual
  subst rightAtom
  subst rightCursor
  rfl

namespace FastTerminalFact

/-- The canonical dot-zero item for a matched terminal atom. -/
def beforeItem
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) : DottedItem tokens := {
  production := .atom fact.work.atom.site
  dot := ⟨0, by simp [ProductionId.rhs]⟩
  origin := fact.work.cursor.beforeBoundary
  current := fact.work.cursor.beforeBoundary
}

/-- The canonical complete item after consuming the matched terminal. -/
def afterItem
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) : DottedItem tokens := {
  production := .atom fact.work.atom.site
  dot := ⟨1, by simp [ProductionId.rhs]⟩
  origin := fact.work.cursor.beforeBoundary
  current := fact.work.cursor.afterBoundary
}

/-- The canonical atom item expects the terminal carried by its fact. -/
theorem beforeItem_next
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    NextSymbol fact.beforeItem
      (.terminal fact.work.atom.terminal) := by
  constructor
  · simp [beforeItem, ProductionId.rhs]
  · simp [beforeItem, ProductionId.rhs, AtomSite.symbol,
      fact.work.atom.atomEq, EbnfAtom.grammarSymbol]

/-- The post-scan atom item is complete. -/
theorem afterItem_complete
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    CompleteItem fact.afterItem := by
  simp [CompleteItem, afterItem, ProductionId.rhs]

/-- The canonical before/after pair is the exact one-symbol advancement. -/
theorem beforeItem_advance
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    AdvanceItem fact.beforeItem fact.work.cursor.afterBoundary
      fact.afterItem := by
  simp [AdvanceItem, beforeItem, afterItem]

/-- The checked scan witness determined by a successful terminal fact. -/
def scannedWitness
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    ScannedEdgeWitness file tokens fact.beforeItem fact.afterItem
      fact.work.cursor := {
  terminal := fact.work.atom.terminal
  matched := fact.matched.val
  sameCursor := fact.matched.property
  next := fact.beforeItem_next
  atCurrent := rfl
  advance := by
    rw [fact.matched.property]
    exact fact.beforeItem_advance
}

/-- The proof-irrelevant valid edge corresponding to the checked scan. -/
def scannedEdge
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) : PackedEdge file tokens :=
  ⟨.scanned fact.beforeItem fact.afterItem fact.work.cursor,
    packedEdge_scanned_valid_iff.mpr ⟨fact.scannedWitness⟩⟩

@[simp] theorem scannedEdge_key
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    fact.scannedEdge.val =
      .scanned fact.beforeItem fact.afterItem fact.work.cursor := by
  rfl

/-- Distinct terminal facts determine distinct canonical raw scan edges. -/
theorem scannedEdge_injective
    {file : WorkspaceFile} {tokens : List Token} :
    Function.Injective
      (@FastTerminalFact.scannedEdge file tokens) := by
  intro left right edgeEqual
  apply FastTerminalFact.work_injective
  have keyEqual := congrArg Subtype.val edgeEqual
  have fields := PackedEdgeKey.scanned.inj keyEqual
  have beforeEqual : left.beforeItem = right.beforeItem := fields.1
  have productionEqual :
      left.beforeItem.production = right.beforeItem.production :=
    congrArg DottedItem.production beforeEqual
  have siteEqual : left.work.atom.site = right.work.atom.site :=
    ProductionId.atom.inj productionEqual
  have atomEqual : left.work.atom = right.work.atom :=
    FastTerminalAtomSite.site_injective siteEqual
  have cursorEqual : left.work.cursor = right.work.cursor := fields.2.2
  exact fastTerminalWorkItem_eq_of_fields atomEqual cursorEqual

/-- The raw dot-zero item viewed through a plain-context semantic index. -/
def beforePlainItem
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) : ContextualItemKey tokens := {
  raw := fact.beforeItem
  context := .plain
}

/-- The raw completed item viewed through the same plain-context index. -/
def afterPlainItem
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) : ContextualItemKey tokens := {
  raw := fact.afterItem
  context := .plain
}

/-- The contextual scan retains the exact terminal witness used to compute
the semantic prefix value. -/
def witnessedPlainScannedEdge
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    WitnessedContextualScannedEdge file tokens := {
  before := fact.beforePlainItem
  after := fact.afterPlainItem
  cursor := fact.work.cursor
  witness := fact.scannedWitness
  sameContext := rfl
}

/-- The unique semantic value at the canonical dot-zero atom item. -/
def zeroPrefix
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    PrefixValues file tokens fact.beforePlainItem :=
  PrefixValues.zeroValue fact.beforePlainItem rfl

/-- The semantic prefix obtained by scanning the retained terminal witness. -/
def scannedPrefix
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    PrefixValues file tokens fact.afterPlainItem :=
  PrefixValues.scanValue fact.beforePlainItem
    fact.afterPlainItem fact.work.atom.terminal
    fact.scannedWitness.next fact.matched.val
    fact.scannedWitness.advance fact.zeroPrefix

/-- Reindex the complete one-symbol prefix as the atom production RHS. -/
def rhsValues
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    GrammarSymbolValues file tokens
      (ProductionId.atom fact.work.atom.site).rhs :=
  PrefixValues.fullValue fact.afterPlainItem
    fact.afterItem_complete fact.scannedPrefix

/-- Execute the checked atom-production action on the scanned RHS value. -/
def completedValue
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    NonterminalValue file tokens
      (ProductionId.atom fact.work.atom.site).lhs :=
  AtomSite.pack fact.work.atom.site fact.rhsValues

/-- Viewing the completed auxiliary at its terminal-atom shape recovers the
exact matched terminal retained by the Phase-A fact. -/
theorem completedValue_atAtom
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    AtomSite.packAtAtom fact.work.atom.site
        (.terminal fact.work.atom.terminal) fact.work.atom.atomEq
        fact.rhsValues =
      EbnfValue.terminalAtom fact.work.atom.terminal
        fact.matched.val := by
  rw [AtomSite.pack_terminal_eq]
  congr 1
  have symbolLayout :
      GrammarSymbol.terminal fact.work.atom.terminal =
        fact.work.atom.site.symbol := by
    simp [AtomSite.symbol, fact.work.atom.atomEq,
      EbnfAtom.grammarSymbol]
  have viewed :
      GrammarSymbolValues.view
          (ProductionId.rhs_atom fact.work.atom.site) fact.rhsValues =
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens) symbolLayout)
            fact.matched.val,
          ()) := by
    apply transport_zero_scan_complete_single
      (prefix_zero_layout fact.beforePlainItem.raw rfl)
      (prefix_scan_layout fact.beforePlainItem.raw
        fact.afterPlainItem.raw fact.work.atom.terminal
        fact.matched.val.cursor.afterBoundary fact.scannedWitness.next
        fact.scannedWitness.advance)
      (prefix_full_layout fact.afterPlainItem.raw
        fact.afterItem_complete)
      (ProductionId.rhs_atom fact.work.atom.site)
      symbolLayout fact.matched.val
  rw [viewed]
  exact transport_type_cycle
    (congrArg (GrammarSymbolValue file tokens) symbolLayout)
    (congrArg (GrammarSymbolValue file tokens)
      fact.work.atom.site.symbol_eq)
    (congrArg (GrammarSymbolValue file tokens)
      (congrArg EbnfAtom.grammarSymbol fact.work.atom.atomEq))
    fact.matched.val

/-- The stored completed auxiliary value is exactly the terminal-atom value
of the retained match. -/
theorem completedValue_exact
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    EbnfValue.transport
        (congrArg EbnfExpr.atom fact.work.atom.atomEq)
        (EbnfValue.atShape fact.work.atom.site.expression_eq_atom
          fact.completedValue) =
      EbnfValue.terminalAtom fact.work.atom.terminal
        fact.matched.val := by
  simpa [completedValue, AtomSite.packAtAtom] using
    fact.completedValue_atAtom

end FastTerminalFact

/-- A materialized terminal-atom result.  Its semantic value is constrained
to be the canonical checked action result derived from its source fact. -/
structure FastTerminalAtomSeed
    (file : WorkspaceFile) (tokens : List Token) where
  fact : FastTerminalFact file tokens
  value : NonterminalValue file tokens
    (ProductionId.atom fact.work.atom.site).lhs
  value_eq : value = fact.completedValue

namespace FastTerminalAtomSeed

/-- Materialize the canonical semantic result of one terminal fact. -/
def ofFact
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    FastTerminalAtomSeed file tokens := {
  fact
  value := fact.completedValue
  value_eq := rfl
}

/-- The raw valid scan edge from which this atom result was computed. -/
def scannedEdge
    {file : WorkspaceFile} {tokens : List Token}
    (seed : FastTerminalAtomSeed file tokens) : PackedEdge file tokens :=
  seed.fact.scannedEdge

/-- Every seed value retains the exact matched terminal of its source fact. -/
theorem value_exact
    {file : WorkspaceFile} {tokens : List Token}
    (seed : FastTerminalAtomSeed file tokens) :
    EbnfValue.transport
        (congrArg EbnfExpr.atom seed.fact.work.atom.atomEq)
        (EbnfValue.atShape seed.fact.work.atom.site.expression_eq_atom
          seed.value) =
      EbnfValue.terminalAtom seed.fact.work.atom.terminal
        seed.fact.matched.val := by
  rw [seed.value_eq]
  exact seed.fact.completedValue_exact

/-- Canonical materialization preserves fact identity. -/
theorem ofFact_injective
    {file : WorkspaceFile} {tokens : List Token} :
    Function.Injective
      (@ofFact file tokens) := by
  intro left right equal
  exact congrArg FastTerminalAtomSeed.fact equal

end FastTerminalAtomSeed

namespace FastTerminalPhaseAExecution

/-- Materialize semantic atom results from the already-computed fact table;
terminal comparisons are not evaluated again. -/
def atomSeeds
    {file : WorkspaceFile} {tokens : List Token}
    (execution : FastTerminalPhaseAExecution file tokens) :
    List (FastTerminalAtomSeed file tokens) :=
  execution.facts.map FastTerminalAtomSeed.ofFact

end FastTerminalPhaseAExecution

/-- Materialize every successful terminal fact in canonical fact-table order. -/
def allFastTerminalAtomSeeds
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    List (FastTerminalAtomSeed file tokens) :=
  (allFastTerminalFacts file owned).map FastTerminalAtomSeed.ofFact

/-- Canonical valid raw scan edges in successful fact-table order. -/
def allFastTerminalAtomScannedEdges
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    List (PackedEdge file tokens) :=
  (allFastTerminalFacts file owned).map FastTerminalFact.scannedEdge

/-- Projecting the materialized seed table recovers the terminal fact table. -/
@[simp] theorem allFastTerminalAtomSeeds_fact_map
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (allFastTerminalAtomSeeds file owned).map
        FastTerminalAtomSeed.fact =
      allFastTerminalFacts file owned := by
  unfold allFastTerminalAtomSeeds
  rw [List.map_map]
  induction allFastTerminalFacts file owned with
  | nil => rfl
  | cons fact facts induction =>
      simp only [List.map_cons]
      rw [induction]
      rfl

/-- Every retained terminal fact has its canonical materialized atom seed. -/
theorem allFastTerminalAtomSeeds_complete
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (fact : FastTerminalFact file tokens)
    (member : fact ∈ allFastTerminalFacts file owned) :
    FastTerminalAtomSeed.ofFact fact ∈
      allFastTerminalAtomSeeds file owned := by
  exact List.mem_map.mpr ⟨fact, member, rfl⟩

/-- The canonical atom-seed table contains no repeated seed. -/
theorem allFastTerminalAtomSeeds_nodup
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (allFastTerminalAtomSeeds file owned).Nodup := by
  exact mapped_values_nodup FastTerminalAtomSeed.ofFact _
    (allFastTerminalFacts_nodup file owned)
    FastTerminalAtomSeed.ofFact_injective

/-- No canonical terminal-atom raw scan edge is repeated. -/
theorem allFastTerminalAtomScannedEdges_nodup
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (allFastTerminalAtomScannedEdges file owned).Nodup := by
  exact mapped_values_nodup FastTerminalFact.scannedEdge _
    (allFastTerminalFacts_nodup file owned)
    FastTerminalFact.scannedEdge_injective

/-- Semantic materialization preserves the successful fact-table length. -/
@[simp] theorem allFastTerminalAtomSeeds_length
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (allFastTerminalAtomSeeds file owned).length =
      (allFastTerminalFacts file owned).length := by
  simp [allFastTerminalAtomSeeds]

/-- A canonical work item has a materialized atom seed exactly when its
terminal matches declaratively at that cursor. -/
theorem allFastTerminalAtomSeeds_work_iff
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens)
    (member : work ∈ allFastTerminalWorkItems tokens) :
    (∃ seed ∈ allFastTerminalAtomSeeds file owned,
        seed.fact.work = work) ↔
      ∃ value span,
        TerminalAt file tokens work.cursor value span ∧
          TerminalMatches work.atom.terminal value := by
  rw [← allFastTerminalFacts_work_iff file owned work member]
  constructor
  · rintro ⟨seed, seedMember, seedWork⟩
    obtain ⟨fact, factMember, seedEqual⟩ :=
      List.mem_map.mp seedMember
    subst seed
    exact ⟨fact, factMember, seedWork⟩
  · rintro ⟨fact, factMember, factWork⟩
    exact ⟨FastTerminalAtomSeed.ofFact fact,
      allFastTerminalAtomSeeds_complete file owned fact factMember,
      factWork⟩

/-- The total terminal executor's atom seeds reuse its retained fact table
exactly. -/
@[simp] theorem executeFastTerminalPhaseA_atomSeeds
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA file owned).atomSeeds =
      allFastTerminalAtomSeeds file owned := by
  rw [FastTerminalPhaseAExecution.atomSeeds,
    executeFastTerminalPhaseA_facts]
  rfl

end Solcore.Surface.Multi
