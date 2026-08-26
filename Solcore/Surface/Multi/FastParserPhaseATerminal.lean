import Solcore.Surface.Multi.ParserScheduleTransition

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-!
The terminal-atom base of the finite fast-parser schedule.

This module enumerates every terminal atom in the fixed grammar at every
retained-token or logical-end cursor.  Each comparison owns memo slot zero of
its grammar-site family and records a checked `MatchedTerminal` on success.
It deliberately stops before nonterminal closure, guards, reductions, and a
whole-module parse result.
-/

/-- A fixed grammar atom whose payload is a terminal symbol. -/
structure FastTerminalAtomSite where
  site : Grammar.AtomSite
  terminal : TerminalSymbol
  atomEq : site.atom = .terminal terminal
  deriving Repr, DecidableEq

namespace FastTerminalAtomSite

/-- Select a terminal atom from one grammar atom site. -/
def ofAtomSite? (site : Grammar.AtomSite) : Option FastTerminalAtomSite :=
  match selected : site.atom with
  | .terminal terminal => some {
      site
      terminal
      atomEq := selected
    }
  | .nonterminal _ => none

/-- Selection retains the exact grammar atom site supplied to the selector. -/
theorem ofAtomSite?_site
    {source : Grammar.AtomSite} {result : FastTerminalAtomSite}
    (selected : ofAtomSite? source = some result) :
    result.site = source := by
  unfold ofAtomSite? at selected
  split at selected
  · exact (congrArg FastTerminalAtomSite.site
      (Option.some.inj selected)).symm
  · cases selected

/-- A terminal-atom descriptor is determined by its grammar site. -/
theorem site_injective : Function.Injective FastTerminalAtomSite.site := by
  intro left right siteEqual
  rcases left with ⟨leftSite, leftTerminal, leftAtomEq⟩
  rcases right with ⟨rightSite, rightTerminal, rightAtomEq⟩
  simp only at siteEqual
  subst rightSite
  have terminalEqual : leftTerminal = rightTerminal := by
    exact EbnfAtom.terminal.inj (leftAtomEq.symm.trans rightAtomEq)
  subst rightTerminal
  rfl

/-- Selecting the grammar site of a terminal descriptor succeeds. -/
theorem ofAtomSite?_self_exists (atom : FastTerminalAtomSite) :
    ∃ result, ofAtomSite? atom.site = some result := by
  cases selected : ofAtomSite? atom.site with
  | some result => exact ⟨result, rfl⟩
  | none =>
      unfold ofAtomSite? at selected
      split at selected
      · cases selected
      · rename_i rule atomSelected
        rw [atom.atomEq] at atomSelected
        cases atomSelected

end FastTerminalAtomSite

private theorem filterMap_nodup_of_functional
    {alpha beta : Type} (select : alpha → Option beta)
    (values : List alpha) (unique : values.Nodup)
    (functional : ∀ (left right : alpha) (result : beta),
      select left = some result → select right = some result →
        left = right) :
    (values.filterMap select).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at unique ⊢
  rw [List.pairwise_filterMap]
  exact unique.imp (fun {left right} different result leftSelected
    other otherSelected equal => by
      subst other
      exact different
        (functional left right result leftSelected otherSelected))

/-- Terminal atom sites in the canonical grammar-site order. -/
def allFastTerminalAtomSites : List FastTerminalAtomSite :=
  Grammar.allAtomSites.filterMap FastTerminalAtomSite.ofAtomSite?

/-- Every fixed terminal atom occurs in the canonical terminal-site list. -/
theorem allFastTerminalAtomSites_complete
    (atom : FastTerminalAtomSite) :
    atom ∈ allFastTerminalAtomSites := by
  obtain ⟨result, selected⟩ :=
    FastTerminalAtomSite.ofAtomSite?_self_exists atom
  have resultEqual : result = atom :=
    FastTerminalAtomSite.site_injective
      (FastTerminalAtomSite.ofAtomSite?_site selected)
  subst result
  apply List.mem_filterMap.mpr
  exact ⟨atom.site, Grammar.allAtomSites_complete atom.site, selected⟩

/-- The canonical terminal-site list contains no repeated grammar site. -/
theorem allFastTerminalAtomSites_nodup :
    allFastTerminalAtomSites.Nodup := by
  apply filterMap_nodup_of_functional
    FastTerminalAtomSite.ofAtomSite? Grammar.allAtomSites
    Grammar.allAtomSites_nodup
  intro left right result leftSelected rightSelected
  exact (FastTerminalAtomSite.ofAtomSite?_site leftSelected).symm.trans
    (FastTerminalAtomSite.ofAtomSite?_site rightSelected)

/-- One terminal comparison owned by the fixed Phase-A base. -/
structure FastTerminalWorkItem (tokens : List Token) where
  atom : FastTerminalAtomSite
  cursor : TerminalCursor tokens
  deriving Repr, DecidableEq

/-- Named memo-slot roles owned by the terminal-atom base. -/
inductive FastTerminalMemoRole where
  | compare
  deriving Repr, DecidableEq

namespace FastTerminalMemoRole

/-- Terminal comparison owns memo slot zero; all other slots remain available
to later operations of the same grammar-site family. -/
def slot : FastTerminalMemoRole → Fin 256
  | .compare => ⟨0, by omega⟩

end FastTerminalMemoRole

/-- Every terminal comparison in grammar-site-major, cursor-minor order. -/
def allFastTerminalWorkItems (tokens : List Token) :
    List (FastTerminalWorkItem tokens) :=
  allFastTerminalAtomSites.flatMap fun atom =>
    (List.finRange (tokens.length + 1)).map fun cursor => {
      atom
      cursor
    }

private theorem map_nodup_of_injective
    {alpha beta : Type} (function : alpha → beta) (values : List alpha)
    (unique : values.Nodup) (injective : Function.Injective function) :
    (values.map function).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at unique ⊢
  rw [List.pairwise_map]
  exact unique.imp fun different equal => different (injective equal)

private theorem finRange_nodup (size : Nat) :
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
        have valueEqual := congrArg Fin.val equal
        simp at valueEqual
      · exact map_nodup_of_injective Fin.succ _ induction (by
          intro left right equal
          apply Fin.ext
          exact Nat.succ.inj (congrArg Fin.val equal))

private theorem dependentFlatMap_nodup
    {alpha gamma : Type} {beta : alpha → Type}
    (values : List alpha) (items : (value : alpha) → List (beta value))
    (make : (value : alpha) → beta value → gamma)
    (valuesUnique : values.Nodup)
    (itemsUnique : ∀ value, (items value).Nodup)
    (makeInjective : ∀ {left right} {leftItem : beta left}
      {rightItem : beta right},
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
      have mappedUnique :
          ((items head).map (make head)).Nodup := by
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
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

/-- Every terminal-site/cursor pair occurs in the canonical worklist. -/
theorem allFastTerminalWorkItems_complete
    {tokens : List Token} (work : FastTerminalWorkItem tokens) :
    work ∈ allFastTerminalWorkItems tokens := by
  rw [allFastTerminalWorkItems, List.mem_flatMap]
  refine ⟨work.atom, allFastTerminalAtomSites_complete work.atom, ?_⟩
  rw [List.mem_map]
  exact ⟨work.cursor, List.mem_finRange work.cursor, rfl⟩

/-- The canonical terminal worklist visits each site/cursor pair once. -/
theorem allFastTerminalWorkItems_nodup (tokens : List Token) :
    (allFastTerminalWorkItems tokens).Nodup := by
  apply dependentFlatMap_nodup allFastTerminalAtomSites
    (fun _ => List.finRange (tokens.length + 1))
    (fun atom cursor => ({ atom, cursor } : FastTerminalWorkItem tokens))
    allFastTerminalAtomSites_nodup
  · intro _
    exact finRange_nodup _
  · intro left right leftCursor rightCursor equal
    cases equal
    rfl

/-- The worklist has one comparison per terminal site and logical cursor. -/
@[simp] theorem allFastTerminalWorkItems_length (tokens : List Token) :
    (allFastTerminalWorkItems tokens).length =
      allFastTerminalAtomSites.length * (tokens.length + 1) := by
  unfold allFastTerminalWorkItems
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_finRange]
  induction allFastTerminalAtomSites with
  | nil => simp
  | cons atom atoms induction =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [induction]
      rw [Nat.add_mul]
      simp [Nat.add_comm]

namespace FastTerminalWorkItem

/-- Schedule address assigned to one terminal comparison. -/
def address {tokens : List Token}
    (work : FastTerminalWorkItem tokens) : FastParserUnitAddress tokens :=
  .memoSlot {
    kind := FastMemoKindIndex.ofKind (.site work.atom.site.site)
    start := work.cursor.beforeBoundary
    finish := work.cursor.afterBoundary
    slot := FastTerminalMemoRole.compare.slot
  }

private theorem atomSite_site_injective :
    Function.Injective (fun site : Grammar.AtomSite => site.site) := by
  intro left right equal
  rcases left with ⟨leftSite, leftKind⟩
  rcases right with ⟨rightSite, rightKind⟩
  simp only at equal
  subst rightSite
  rfl

/-- Different terminal comparisons receive different memo addresses. -/
theorem address_injective {tokens : List Token} :
    Function.Injective (@address tokens) := by
  intro left right equal
  unfold address at equal
  injection equal with memoEqual
  have kindEqual := congrArg FastMemoSlotAddress.kind memoEqual
  have ownerEqual := FastMemoKindIndex.ofKind_injective kindEqual
  have rawSiteEqual : left.atom.site.site = right.atom.site.site :=
    Grammar.FastMemoKeyKind.site.inj ownerEqual
  have atomSiteEqual : left.atom.site = right.atom.site :=
    atomSite_site_injective rawSiteEqual
  have atomEqual : left.atom = right.atom :=
    FastTerminalAtomSite.site_injective atomSiteEqual
  have startEqual := congrArg FastMemoSlotAddress.start memoEqual
  have cursorValueEqual : left.cursor.val = right.cursor.val :=
    congrArg (fun boundary : Boundary tokens => boundary.val) startEqual
  have cursorEqual : left.cursor = right.cursor :=
    Fin.ext cursorValueEqual
  cases left
  cases right
  simp_all

/-- The checked result of one terminal comparison. -/
abbrev Result
    (file : WorkspaceFile) {tokens : List Token}
    (work : FastTerminalWorkItem tokens) :=
  Option { matched : MatchedTerminal file tokens work.atom.terminal //
    matched.cursor = work.cursor }

/-- Execute one terminal comparison. -/
def evaluate
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens) : Result file work :=
  MatchedTerminal.atCursor? file tokens owned
    work.atom.terminal work.cursor

/-- Executable comparison succeeds exactly when the declarative terminal
relations hold at this work item's cursor. -/
theorem evaluate_isSome_eq_true_iff
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens) :
    (work.evaluate file owned).isSome = true ↔
      ∃ value span,
        TerminalAt file tokens work.cursor value span ∧
          TerminalMatches work.atom.terminal value := by
  constructor
  · intro present
    cases selected : work.evaluate file owned with
    | none => simp [selected] at present
    | some result =>
        obtain ⟨terminalAt, terminalMatches⟩ :=
          MatchedTerminal.atCursor?_sound owned work.atom.terminal
            work.cursor selected
        exact ⟨result.val.value, result.val.span,
          terminalAt, terminalMatches⟩
  · rintro ⟨value, span, terminalAt, terminalMatches⟩
    obtain ⟨result, selected⟩ :=
      MatchedTerminal.atCursor?_complete owned work.atom.terminal
        work.cursor terminalAt terminalMatches
    rw [evaluate, selected]
    rfl

end FastTerminalWorkItem

/-- The startup event followed by the complete terminal-comparison worklist. -/
inductive FastTerminalEvent (tokens : List Token) where
  | startup
  | compare (work : FastTerminalWorkItem tokens)
  deriving Repr, DecidableEq

namespace FastTerminalEvent

/-- Schedule address charged by one terminal-base event. -/
def address {tokens : List Token} :
    FastTerminalEvent tokens → FastParserUnitAddress tokens
  | .startup => .fixed .startup
  | .compare work => work.address

/-- Event identity is preserved by its fixed schedule address. -/
theorem address_injective {tokens : List Token} :
    Function.Injective (@address tokens) := by
  intro left right equal
  cases left with
  | startup =>
      cases right with
      | startup => rfl
      | compare work => cases equal
  | compare leftWork =>
      cases right with
      | startup => cases equal
      | compare rightWork =>
          have workEqual := FastTerminalWorkItem.address_injective
            equal
          cases workEqual
          rfl

end FastTerminalEvent

/-- Canonical terminal-base events, with startup charged exactly once. -/
def allFastTerminalEvents (tokens : List Token) :
    List (FastTerminalEvent tokens) :=
  .startup :: (allFastTerminalWorkItems tokens).map .compare

/-- Canonical schedule addresses for the terminal-base execution. -/
def allFastTerminalAddresses (tokens : List Token) :
    List (FastParserUnitAddress tokens) :=
  (allFastTerminalEvents tokens).map FastTerminalEvent.address

/-- The canonical event list contains no repeated semantic operation. -/
theorem allFastTerminalEvents_nodup (tokens : List Token) :
    (allFastTerminalEvents tokens).Nodup := by
  rw [allFastTerminalEvents, List.nodup_cons]
  constructor
  · intro member
    rw [List.mem_map] at member
    rcases member with ⟨work, _, equal⟩
    cases equal
  · exact map_nodup_of_injective FastTerminalEvent.compare _
      (allFastTerminalWorkItems_nodup tokens) (by
        intro left right equal
        exact FastTerminalEvent.compare.inj equal)

/-- Canonical terminal-base addresses are pairwise distinct. -/
theorem allFastTerminalAddresses_nodup (tokens : List Token) :
    (allFastTerminalAddresses tokens).Nodup := by
  exact map_nodup_of_injective FastTerminalEvent.address _
    (allFastTerminalEvents_nodup tokens)
    FastTerminalEvent.address_injective

/-- Startup plus one address per terminal comparison is charged. -/
@[simp] theorem allFastTerminalAddresses_length (tokens : List Token) :
    (allFastTerminalAddresses tokens).length =
      1 + (allFastTerminalWorkItems tokens).length := by
  simp [allFastTerminalAddresses, allFastTerminalEvents, Nat.add_comm]

/-- One work item paired with its checked terminal-comparison result. -/
structure FastTerminalObservation
    (file : WorkspaceFile) (tokens : List Token) where
  work : FastTerminalWorkItem tokens
  result : work.Result file

/-- A successful terminal comparison retained as a finite Phase-A fact. -/
structure FastTerminalFact
    (file : WorkspaceFile) (tokens : List Token) where
  work : FastTerminalWorkItem tokens
  matched : { value : MatchedTerminal file tokens work.atom.terminal //
    value.cursor = work.cursor }

namespace FastTerminalFact

/-- Every retained terminal fact satisfies both declarative terminal
relations. -/
theorem sound
    {file : WorkspaceFile} {tokens : List Token}
    (fact : FastTerminalFact file tokens) :
    TerminalAt file tokens fact.work.cursor
        fact.matched.val.value fact.matched.val.span ∧
      TerminalMatches fact.work.atom.terminal fact.matched.val.value := by
  constructor
  · simpa only [fact.matched.property] using fact.matched.val.at
  · exact fact.matched.val.matches

end FastTerminalFact

namespace FastTerminalObservation

/-- Evaluate a work item and retain its identity beside the result. -/
def evaluate
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens) :
    FastTerminalObservation file tokens := {
  work
  result := work.evaluate file owned
}

/-- Retain a fact exactly when the comparison matched. -/
def fact?
    {file : WorkspaceFile} {tokens : List Token}
    (observation : FastTerminalObservation file tokens) :
    Option (FastTerminalFact file tokens) :=
  match observation.result with
  | none => none
  | some matched => some {
      work := observation.work
      matched
    }

end FastTerminalObservation

/-- Canonical evaluated observations in worklist order. -/
def allFastTerminalObservations
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    List (FastTerminalObservation file tokens) :=
  (allFastTerminalWorkItems tokens).map
    (FastTerminalObservation.evaluate file owned)

/-- Successful observations retained in canonical worklist order. -/
def allFastTerminalFacts
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    List (FastTerminalFact file tokens) :=
  (allFastTerminalObservations file owned).filterMap
    FastTerminalObservation.fact?

/-- Observation identities reproduce the canonical worklist exactly. -/
@[simp] theorem allFastTerminalObservations_work_map
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (allFastTerminalObservations file owned).map
        FastTerminalObservation.work =
      allFastTerminalWorkItems tokens := by
  unfold allFastTerminalObservations
  rw [List.map_map]
  induction allFastTerminalWorkItems tokens with
  | nil => rfl
  | cons work works induction =>
      simp only [List.map_cons]
      rw [induction]
      rfl

/-- No terminal work identity is repeated in the observation table. -/
theorem allFastTerminalObservations_work_nodup
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ((allFastTerminalObservations file owned).map
      FastTerminalObservation.work).Nodup := by
  rw [allFastTerminalObservations_work_map]
  exact allFastTerminalWorkItems_nodup tokens

/-- Every canonical work item has an evaluated observation entry. -/
theorem allFastTerminalObservations_work_complete
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens)
    (member : work ∈ allFastTerminalWorkItems tokens) :
    ∃ observation ∈ allFastTerminalObservations file owned,
      observation.work = work := by
  refine ⟨FastTerminalObservation.evaluate file owned work, ?_, rfl⟩
  exact List.mem_map.mpr ⟨work, member, rfl⟩

/-- A declarative terminal match is retained by the canonical fact table. -/
theorem allFastTerminalFacts_complete
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens)
    (member : work ∈ allFastTerminalWorkItems tokens)
    {value : TerminalStreamValue} {span : SourceSpan}
    (terminalAt : TerminalAt file tokens work.cursor value span)
    (terminalMatches : TerminalMatches work.atom.terminal value) :
    ∃ fact ∈ allFastTerminalFacts file owned,
      fact.work = work := by
  obtain ⟨matched, selected⟩ :=
    MatchedTerminal.atCursor?_complete owned work.atom.terminal work.cursor
      terminalAt terminalMatches
  let observation := FastTerminalObservation.evaluate file owned work
  let fact : FastTerminalFact file tokens := {
    work
    matched
  }
  refine ⟨fact, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  refine ⟨observation, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨work, member, rfl⟩
  · simp [FastTerminalObservation.fact?, observation,
      FastTerminalObservation.evaluate, FastTerminalWorkItem.evaluate,
      selected, fact]

/-- The canonical fact table contains a work item exactly when its terminal
matches declaratively at that cursor. -/
theorem allFastTerminalFacts_work_iff
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens)
    (member : work ∈ allFastTerminalWorkItems tokens) :
    (∃ fact ∈ allFastTerminalFacts file owned,
        fact.work = work) ↔
      ∃ value span,
        TerminalAt file tokens work.cursor value span ∧
          TerminalMatches work.atom.terminal value := by
  constructor
  · rintro ⟨fact, _factMember, factWork⟩
    obtain ⟨terminalAt, terminalMatches⟩ := fact.sound
    subst work
    exact ⟨fact.matched.val.value, fact.matched.val.span,
      terminalAt, terminalMatches⟩
  · rintro ⟨value, span, terminalAt, terminalMatches⟩
    exact allFastTerminalFacts_complete file owned work member
      terminalAt terminalMatches

/-- Result of the terminal-atom base execution. -/
structure FastTerminalPhaseAExecution
    (file : WorkspaceFile) (tokens : List Token) where
  trace : FastParserScheduleTrace tokens
  observations : List (FastTerminalObservation file tokens)
  facts : List (FastTerminalFact file tokens)

/-- Execute and charge the complete terminal-atom base. -/
def executeFastTerminalPhaseA?
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    Option (FastTerminalPhaseAExecution file tokens) :=
  match (FastParserScheduleTrace.empty tokens).chargeAll?
      (allFastTerminalAddresses tokens) with
  | none => none
  | some trace =>
    let observations := allFastTerminalObservations file owned
    some {
      trace
      observations
      facts := observations.filterMap FastTerminalObservation.fact?
    }

/-- The canonical terminal execution always succeeds because its schedule
addresses are pairwise distinct. -/
theorem executeFastTerminalPhaseA?_exists
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    ∃ execution, executeFastTerminalPhaseA? file owned = some execution := by
  obtain ⟨trace, selected⟩ :=
    FastParserScheduleTrace.chargeAll?_empty_exists_of_nodup
      (allFastTerminalAddresses_nodup tokens)
  refine ⟨{
    trace
    observations := allFastTerminalObservations file owned
    facts := allFastTerminalFacts file owned
  }, ?_⟩
  simp [executeFastTerminalPhaseA?, allFastTerminalFacts, selected]

/-- The option-valued executor is constructively known to succeed. -/
theorem executeFastTerminalPhaseA?_isSome_eq_true
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA? file owned).isSome = true := by
  exact Option.isSome_iff_exists.mpr
    (executeFastTerminalPhaseA?_exists file owned)

/-- Total executable terminal-atom Phase-A base. -/
def executeFastTerminalPhaseA
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    FastTerminalPhaseAExecution file tokens :=
  (executeFastTerminalPhaseA? file owned).get
    (executeFastTerminalPhaseA?_isSome_eq_true file owned)

/-- The total executor is exactly the successful option-valued result. -/
@[simp] theorem executeFastTerminalPhaseA?_selected
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    executeFastTerminalPhaseA? file owned =
      some (executeFastTerminalPhaseA file owned) := by
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨executeFastTerminalPhaseA?_isSome_eq_true file owned, rfl⟩

/-- Successful execution exposes the exact underlying schedule run. -/
theorem executeFastTerminalPhaseA?_trace
    {file : WorkspaceFile} {tokens : List Token}
    {owned : TokensOwnedBy file tokens}
    {execution : FastTerminalPhaseAExecution file tokens}
    (selected : executeFastTerminalPhaseA? file owned = some execution) :
    (FastParserScheduleTrace.empty tokens).chargeAll?
        (allFastTerminalAddresses tokens) = some execution.trace := by
  unfold executeFastTerminalPhaseA? at selected
  split at selected
  · cases selected
  · rename_i trace traceSelected
    have executionEqual := Option.some.inj selected
    cases executionEqual
    exact traceSelected

/-- Successful execution returns the complete observation table. -/
theorem executeFastTerminalPhaseA?_observations
    {file : WorkspaceFile} {tokens : List Token}
    {owned : TokensOwnedBy file tokens}
    {execution : FastTerminalPhaseAExecution file tokens}
    (selected : executeFastTerminalPhaseA? file owned = some execution) :
    execution.observations = allFastTerminalObservations file owned := by
  unfold executeFastTerminalPhaseA? at selected
  split at selected
  · cases selected
  · have executionEqual := Option.some.inj selected
    cases executionEqual
    rfl

/-- Successful execution returns exactly the successful terminal facts. -/
theorem executeFastTerminalPhaseA?_facts
    {file : WorkspaceFile} {tokens : List Token}
    {owned : TokensOwnedBy file tokens}
    {execution : FastTerminalPhaseAExecution file tokens}
    (selected : executeFastTerminalPhaseA? file owned = some execution) :
    execution.facts = allFastTerminalFacts file owned := by
  unfold executeFastTerminalPhaseA? at selected
  split at selected
  · cases selected
  · have executionEqual := Option.some.inj selected
    cases executionEqual
    rfl

/-- The trace charges startup and every terminal comparison exactly once. -/
theorem executeFastTerminalPhaseA?_actualUnits
    {file : WorkspaceFile} {tokens : List Token}
    {owned : TokensOwnedBy file tokens}
    {execution : FastTerminalPhaseAExecution file tokens}
    (selected : executeFastTerminalPhaseA? file owned = some execution) :
    execution.trace.actualUnits =
      1 + (allFastTerminalWorkItems tokens).length := by
  have traceSelected := executeFastTerminalPhaseA?_trace selected
  have charged := FastParserScheduleTrace.chargeAll?_actualUnits traceSelected
  simpa using charged

/-- The terminal base fits the fixed parser schedule bound. -/
theorem executeFastTerminalPhaseA?_actualUnits_le_parseBound
    {file : WorkspaceFile} {tokens : List Token}
    {owned : TokensOwnedBy file tokens}
    {execution : FastTerminalPhaseAExecution file tokens}
    (_selected : executeFastTerminalPhaseA? file owned = some execution) :
    execution.trace.actualUnits ≤ parseBound (tokens.length + 1) :=
  execution.trace.actualUnits_le_parseBound

/-- The terminal event count itself fits the fixed parser schedule. -/
theorem fastTerminalEventCount_le_parseBound (tokens : List Token) :
    1 + (allFastTerminalWorkItems tokens).length ≤
      parseBound (tokens.length + 1) := by
  rw [← allFastTerminalAddresses_length]
  exact FastParserScheduleTrace.nodup_length_le_parseBound
    (allFastTerminalAddresses_nodup tokens)

/-- The total executor returns the canonical observation table. -/
@[simp] theorem executeFastTerminalPhaseA_observations
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA file owned).observations =
      allFastTerminalObservations file owned := by
  exact executeFastTerminalPhaseA?_observations
    (executeFastTerminalPhaseA?_selected file owned)

/-- The total executor returns the canonical successful fact table. -/
@[simp] theorem executeFastTerminalPhaseA_facts
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA file owned).facts =
      allFastTerminalFacts file owned := by
  exact executeFastTerminalPhaseA?_facts
    (executeFastTerminalPhaseA?_selected file owned)

/-- The total executor charges startup and every comparison exactly once. -/
@[simp] theorem executeFastTerminalPhaseA_actualUnits
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA file owned).trace.actualUnits =
      1 + (allFastTerminalWorkItems tokens).length := by
  exact executeFastTerminalPhaseA?_actualUnits
    (executeFastTerminalPhaseA?_selected file owned)

/-- The total terminal-base executor remains within `parseBound`. -/
theorem executeFastTerminalPhaseA_actualUnits_le_parseBound
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens) :
    (executeFastTerminalPhaseA file owned).trace.actualUnits ≤
      parseBound (tokens.length + 1) := by
  exact executeFastTerminalPhaseA?_actualUnits_le_parseBound
    (executeFastTerminalPhaseA?_selected file owned)

/-- A work item occurs in the total executor's fact table exactly when its
terminal matches declaratively. -/
theorem executeFastTerminalPhaseA_fact_work_iff
    (file : WorkspaceFile) {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (work : FastTerminalWorkItem tokens)
    (member : work ∈ allFastTerminalWorkItems tokens) :
    (∃ fact ∈ (executeFastTerminalPhaseA file owned).facts,
        fact.work = work) ↔
      ∃ value span,
        TerminalAt file tokens work.cursor value span ∧
          TerminalMatches work.atom.terminal value := by
  rw [executeFastTerminalPhaseA_facts]
  exact allFastTerminalFacts_work_iff file owned work member

end Solcore.Surface.Multi
