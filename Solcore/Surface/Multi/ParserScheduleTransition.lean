import Solcore.Surface.Multi.ParserScheduleTrace

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
Executable list transitions for the fixed fast-schedule trace.

The transition accepts a list only when its canonical address ranks are
pairwise distinct and every individual trace charge succeeds.  The companion
relation records exactly that sequence of successful charges.  This is a
generic schedule kernel: it neither defines parsing steps nor identifies these
transitions with parser or chart behavior.
-/

namespace FastParserUnitAddress

/-- The natural-number form of the canonical rank. -/
def rankValue {tokens : List Token}
    (address : FastParserUnitAddress tokens) : Nat :=
  address.rank.val

/-- Canonical ranks of a schedule-address list, in list order. -/
def rankValues {tokens : List Token}
    (addresses : List (FastParserUnitAddress tokens)) : List Nat :=
  addresses.map rankValue

@[simp] theorem rankValues_nil {tokens : List Token} :
    rankValues ([] : List (FastParserUnitAddress tokens)) = [] := by
  rfl

@[simp] theorem rankValues_cons {tokens : List Token}
    (address : FastParserUnitAddress tokens)
    (addresses : List (FastParserUnitAddress tokens)) :
    rankValues (address :: addresses) =
      address.rankValue :: FastParserUnitAddress.rankValues addresses := by
  rfl

theorem rankValue_injective {tokens : List Token} :
    Function.Injective
      (@FastParserUnitAddress.rankValue tokens) := by
  intro left right equal
  apply FastParserUnitAddress.rank_injective
  apply Fin.ext
  exact equal

/-- Distinct addresses have distinct canonical ranks, and conversely. -/
theorem rankValues_nodup_iff {tokens : List Token}
    {addresses : List (FastParserUnitAddress tokens)} :
    (FastParserUnitAddress.rankValues addresses).Nodup ↔
      addresses.Nodup := by
  induction addresses with
  | nil => simp
  | cons address addresses induction =>
      rw [rankValues_cons, List.nodup_cons, List.nodup_cons]
      constructor
      · intro rankUnique
        constructor
        · intro member
          apply rankUnique.1
          exact List.mem_map.mpr ⟨address, member, rfl⟩
        · exact induction.mp rankUnique.2
      · intro addressUnique
        constructor
        · intro rankMember
          obtain ⟨candidate, candidateMember, sameRank⟩ :=
            List.mem_map.mp rankMember
          have sameAddress : candidate = address := by
            apply rankValue_injective
            exact sameRank
          exact addressUnique.1 (sameAddress ▸ candidateMember)
        · exact induction.mpr addressUnique.2

end FastParserUnitAddress

namespace FastParserScheduleTrace

/-- An unvisited address has a successful single-address transition. -/
theorem charge?_exists_of_not_visited {tokens : List Token}
    (trace : FastParserScheduleTrace tokens)
    (address : FastParserUnitAddress tokens)
    (unvisited : trace.visited address = false) :
    ∃ result, trace.charge? address = some result := by
  cases selected : trace.charge? address with
  | none =>
      have present :=
        (charge?_eq_none_iff_visited trace address).mp selected
      rw [unvisited] at present
      cases present
  | some result =>
      exact ⟨result, rfl⟩

/-- Charge an ordered address list.  A repeated canonical rank is rejected
before any charge in that list is returned to the caller. -/
def chargeAll? {tokens : List Token}
    (initial : FastParserScheduleTrace tokens) :
    List (FastParserUnitAddress tokens) →
      Option (FastParserScheduleTrace tokens)
  | [] => some initial
  | address :: addresses =>
      if address.rankValue ∈ FastParserUnitAddress.rankValues addresses then
        none
      else
        match initial.charge? address with
        | none => none
        | some next => next.chargeAll? addresses

/-- Declarative form of a successful list charge.  Each constructor records
one fresh canonical rank and one successful trace transition. -/
inductive Run {tokens : List Token} :
    FastParserScheduleTrace tokens →
      List (FastParserUnitAddress tokens) →
        FastParserScheduleTrace tokens → Prop where
  | nil (trace : FastParserScheduleTrace tokens) : Run trace [] trace
  | cons
      {initial next final : FastParserScheduleTrace tokens}
      {address : FastParserUnitAddress tokens}
      {addresses : List (FastParserUnitAddress tokens)}
      (rankFresh : address.rankValue ∉
        FastParserUnitAddress.rankValues addresses)
      (selected : initial.charge? address = some next)
      (tail : Run next addresses final) :
      Run initial (address :: addresses) final

@[simp] theorem chargeAll?_nil {tokens : List Token}
    (trace : FastParserScheduleTrace tokens) :
    trace.chargeAll? [] = some trace := by
  rfl

/-- The executable list transition and the declarative run relation agree. -/
theorem chargeAll?_eq_some_iff_run {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)} :
    initial.chargeAll? addresses = some final ↔
      Run initial addresses final := by
  induction addresses generalizing initial final with
  | nil =>
      constructor
      · intro selected
        cases selected
        exact .nil initial
      · intro run
        cases run
        rfl
  | cons address addresses induction =>
      unfold chargeAll?
      by_cases rankFresh : address.rankValue ∉
          FastParserUnitAddress.rankValues addresses
      · rw [if_neg (by simpa using rankFresh)]
        cases selected : initial.charge? address with
        | none =>
            constructor
            · intro impossible
              cases impossible
            · intro run
              cases run with
              | cons _ runSelected _ =>
                  rw [selected] at runSelected
                  cases runSelected
        | some next =>
            rw [induction]
            constructor
            · intro tail
              exact .cons rankFresh selected tail
            · intro run
              cases run with
              | cons _ runSelected tail =>
                  rw [selected] at runSelected
                  cases runSelected
                  exact tail
      · have rankPresent :
            address.rankValue ∈
              FastParserUnitAddress.rankValues addresses := by
          exact Decidable.byContradiction rankFresh
        rw [if_pos rankPresent]
        constructor
        · intro impossible
          cases impossible
        · intro run
          cases run with
          | cons runFresh _ _ =>
              exact (runFresh rankPresent).elim

/-- A declarative run determines a unique final trace. -/
theorem Run.deterministic {tokens : List Token}
    {initial left right : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (leftRun : Run initial addresses left)
    (rightRun : Run initial addresses right) :
    left = right := by
  have leftSelected : initial.chargeAll? addresses = some left :=
    chargeAll?_eq_some_iff_run.mpr leftRun
  have rightSelected : initial.chargeAll? addresses = some right :=
    chargeAll?_eq_some_iff_run.mpr rightRun
  rw [leftSelected] at rightSelected
  exact Option.some.inj rightSelected

/-- Two successful executable evaluations have the same final trace. -/
theorem chargeAll?_deterministic {tokens : List Token}
    {initial left right : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (leftSelected : initial.chargeAll? addresses = some left)
    (rightSelected : initial.chargeAll? addresses = some right) :
    left = right := by
  rw [leftSelected] at rightSelected
  exact Option.some.inj rightSelected

/-- Every successful run increases the charged-unit count by its list length. -/
theorem Run.actualUnits {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (run : Run initial addresses final) :
    final.actualUnits = initial.actualUnits + addresses.length := by
  induction run with
  | nil trace => simp
  | cons rankFresh selected tail induction =>
      rw [induction, charge?_actualUnits selected]
      simp
      omega

/-- The final ledger of every successful run fits the fixed schedule. -/
theorem Run.finalLedgerFits {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (_run : Run initial addresses final) :
    final.ledger.FitsWithin (fastParserScheduleAddressCapacity tokens) := by
  exact final.ledger_fitsWithin

/-- A successful run consumes no more units than the parser schedule bound. -/
theorem Run.length_le_parseBound {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (run : Run initial addresses final) :
    initial.actualUnits + addresses.length ≤
      parseBound (tokens.length + 1) := by
  rw [← run.actualUnits]
  exact final.actualUnits_le_parseBound

/-- From the empty trace, a successful list length itself is schedule-bounded. -/
theorem Run.empty_length_le_parseBound {tokens : List Token}
    {final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (run : Run (empty tokens) addresses final) :
    addresses.length ≤ parseBound (tokens.length + 1) := by
  simpa using run.length_le_parseBound

/-- Successful runs contain no repeated canonical ranks. -/
theorem Run.rankValues_nodup {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (run : Run initial addresses final) :
    (FastParserUnitAddress.rankValues addresses).Nodup := by
  induction run with
  | nil trace => simp
  | cons rankFresh selected tail induction =>
      exact List.nodup_cons.mpr ⟨rankFresh, induction⟩

/-- Rank injectivity turns successful rank freshness into address freshness. -/
theorem Run.addresses_nodup {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (run : Run initial addresses final) :
    addresses.Nodup := by
  exact FastParserUnitAddress.rankValues_nodup_iff.mp
    run.rankValues_nodup

/-- Executable success exposes the exact charged-unit equation. -/
theorem chargeAll?_actualUnits {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (selected : initial.chargeAll? addresses = some final) :
    final.actualUnits = initial.actualUnits + addresses.length := by
  exact (chargeAll?_eq_some_iff_run.mp selected).actualUnits

/-- Executable success exposes the final ledger-capacity certificate. -/
theorem chargeAll?_ledger_fitsWithin {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (_selected : initial.chargeAll? addresses = some final) :
    final.ledger.FitsWithin (fastParserScheduleAddressCapacity tokens) := by
  exact final.ledger_fitsWithin

/-- Executable success is bounded by the fixed parser schedule. -/
theorem chargeAll?_length_le_parseBound {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (selected : initial.chargeAll? addresses = some final) :
    initial.actualUnits + addresses.length ≤
      parseBound (tokens.length + 1) := by
  exact (chargeAll?_eq_some_iff_run.mp selected).length_le_parseBound

/-- Executable success from an empty trace bounds the address-list length. -/
theorem chargeAll?_empty_length_le_parseBound {tokens : List Token}
    {final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (selected : (empty tokens).chargeAll? addresses = some final) :
    addresses.length ≤ parseBound (tokens.length + 1) := by
  exact (chargeAll?_eq_some_iff_run.mp selected).empty_length_le_parseBound

/-- Executable success entails duplicate-free addresses. -/
theorem chargeAll?_addresses_nodup {tokens : List Token}
    {initial final : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (selected : initial.chargeAll? addresses = some final) :
    addresses.Nodup := by
  exact (chargeAll?_eq_some_iff_run.mp selected).addresses_nodup

/-- A duplicate-free address list succeeds from any trace on which every
listed address is initially unvisited. -/
theorem chargeAll?_exists_of_nodup_unvisited {tokens : List Token}
    {initial : FastParserScheduleTrace tokens}
    {addresses : List (FastParserUnitAddress tokens)}
    (unique : addresses.Nodup)
    (unvisited : ∀ address, address ∈ addresses →
      initial.visited address = false) :
    ∃ final, initial.chargeAll? addresses = some final := by
  induction addresses generalizing initial with
  | nil =>
      exact ⟨initial, rfl⟩
  | cons address addresses induction =>
      have rankUnique :
          (FastParserUnitAddress.rankValues
            (address :: addresses)).Nodup :=
        FastParserUnitAddress.rankValues_nodup_iff.mpr unique
      rw [FastParserUnitAddress.rankValues_cons,
        List.nodup_cons] at rankUnique
      rw [List.nodup_cons] at unique
      have addressUnvisited : initial.visited address = false :=
        unvisited address (by simp)
      obtain ⟨next, selected⟩ :=
        charge?_exists_of_not_visited initial address addressUnvisited
      have remainingUnvisited : ∀ candidate, candidate ∈ addresses →
          next.visited candidate = false := by
        intro candidate candidateMember
        apply charge?_success_preserves_not_visited selected
        · intro equalRank
          have equalValue : address.rankValue = candidate.rankValue :=
            congrArg Fin.val equalRank
          have equalAddress : address = candidate :=
            FastParserUnitAddress.rankValue_injective equalValue
          apply unique.1
          rw [equalAddress]
          exact candidateMember
        · exact unvisited candidate (by simp [candidateMember])
      obtain ⟨final, tailSelected⟩ :=
        induction unique.2 remainingUnvisited
      refine ⟨final, ?_⟩
      unfold chargeAll?
      rw [if_neg rankUnique.1, selected]
      exact tailSelected

/-- Every duplicate-free address list succeeds from the empty trace. -/
theorem chargeAll?_empty_exists_of_nodup {tokens : List Token}
    {addresses : List (FastParserUnitAddress tokens)}
    (unique : addresses.Nodup) :
    ∃ final, (empty tokens).chargeAll? addresses = some final := by
  apply chargeAll?_exists_of_nodup_unvisited unique
  intro address _member
  exact empty_visited tokens address

/-- Empty-trace totality can be chosen with its exact unit count and final
ledger-capacity certificate exposed together. -/
theorem chargeAll?_empty_exists_accounted_of_nodup {tokens : List Token}
    {addresses : List (FastParserUnitAddress tokens)}
    (unique : addresses.Nodup) :
    ∃ final,
      (empty tokens).chargeAll? addresses = some final ∧
      final.actualUnits = addresses.length ∧
      final.ledger.FitsWithin (fastParserScheduleAddressCapacity tokens) := by
  obtain ⟨final, selected⟩ := chargeAll?_empty_exists_of_nodup unique
  refine ⟨final, selected, ?_, ?_⟩
  · simpa using chargeAll?_actualUnits selected
  · exact chargeAll?_ledger_fitsWithin selected

/-- Empty-trace execution succeeds exactly for duplicate-free address lists. -/
theorem chargeAll?_empty_success_iff_nodup {tokens : List Token}
    {addresses : List (FastParserUnitAddress tokens)} :
    (∃ final, (empty tokens).chargeAll? addresses = some final) ↔
      addresses.Nodup := by
  constructor
  · rintro ⟨final, selected⟩
    exact chargeAll?_addresses_nodup selected
  · exact chargeAll?_empty_exists_of_nodup

/-- Duplicate-free address lists fit the same token-indexed parser bound that
governs successful trace executions. -/
theorem nodup_length_le_parseBound {tokens : List Token}
    {addresses : List (FastParserUnitAddress tokens)}
    (unique : addresses.Nodup) :
    addresses.length ≤ parseBound (tokens.length + 1) := by
  obtain ⟨final, selected⟩ :=
    chargeAll?_empty_exists_of_nodup unique
  exact chargeAll?_empty_length_le_parseBound selected

/-- An adjacent repeated address always makes the list transition fail. -/
@[simp] theorem chargeAll?_immediate_duplicate {tokens : List Token}
    (initial : FastParserScheduleTrace tokens)
    (address : FastParserUnitAddress tokens)
    (addresses : List (FastParserUnitAddress tokens)) :
    initial.chargeAll? (address :: address :: addresses) = none := by
  simp [chargeAll?]

end FastParserScheduleTrace

end Solcore.Surface.Multi
