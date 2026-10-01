set_option autoImplicit false

namespace Solcore.Frontend.TraitResolution

universe u v w

/-- A resolved trait obligation. The distinguished `subject` is kept separate
from the remaining trait arguments so source predicates can be represented
without losing their written role. -/
structure Predicate (Trait : Type u) (Ty : Type v) where
  trait : Trait
  subject : Ty
  arguments : List Ty
  deriving Repr, BEq, DecidableEq

/-- A generic implementation rule before its head has been matched against a
goal. Type variables, when present, live in the caller's `Ty` representation. -/
structure ImplRule (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  id : ImplId
  head : Predicate Trait Ty
  wherePredicates : List (Predicate Trait Ty)
  /-- A default implementation participates only when the ordinary tier has a
  definite `noSolution`.  The default preserves existing rule literals. -/
  isDefault : Bool := false
  deriving Repr, BEq, DecidableEq

/-- One implementation whose head matched a goal. `premises` must already have
the head matcher's substitution applied. -/
structure Candidate (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  implId : ImplId
  premises : List (Predicate Trait Ty)
  /-- The priority tier inherited from the matched implementation rule. -/
  isDefault : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Boundary owned by the type layer: freshen an implementation, match its head,
and return its instantiated where predicates. `none` means the head does not
match. -/
abbrev HeadMatcher (Trait : Type u) (Ty : Type v) (ImplId : Type w) :=
  ImplRule Trait Ty ImplId → Predicate Trait Ty →
    Option (List (Predicate Trait Ty))

/-- A finite implementation catalog plus the type-specific head matcher. -/
structure Program (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  rules : List (ImplRule Trait Ty ImplId)
  matchHead : HeadMatcher Trait Ty ImplId

variable {Trait : Type u} {Ty : Type v} {ImplId : Type w}

/-- Exact monomorphic head matching, useful before a unifier is connected. -/
@[reducible] def exactHeadMatcher [DecidableEq Trait] [DecidableEq Ty] :
    HeadMatcher Trait Ty ImplId :=
  fun rule goal =>
    if rule.head = goal then some rule.wherePredicates else none

namespace Program

/-- Enumerate all matching rules in declaration order. -/
@[reducible] def candidates (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty) : List (Candidate Trait Ty ImplId) :=
  program.rules.filterMap fun rule =>
    (program.matchHead rule goal).map fun premises =>
      { implId := rule.id
        premises := premises
        isDefault := rule.isDefault }

/-- Matching non-default implementations in their declaration order. -/
@[reducible] def ordinaryCandidates (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty) : List (Candidate Trait Ty ImplId) :=
  (program.candidates goal).filter fun candidate => !candidate.isDefault

/-- Matching default implementations in their declaration order. -/
@[reducible] def defaultCandidates (program : Program Trait Ty ImplId)
    (goal : Predicate Trait Ty) : List (Candidate Trait Ty ImplId) :=
  (program.candidates goal).filter fun candidate => candidate.isDefault

end Program

/-- Executable evidence records the selected implementation and evidence for
each instantiated where predicate in source order. -/
inductive Evidence (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  | byImpl
      (goal : Predicate Trait Ty)
      (implId : ImplId)
      (premises : List (Evidence Trait Ty ImplId))
  deriving Repr

namespace Evidence

mutual
/-- Structural comparison retains the derived comparison's goal, implementation,
and ordered-premise checks while making its finite recursion proof-visible. -/
def beq [BEq Trait] [BEq Ty] [BEq ImplId] :
    Evidence Trait Ty ImplId → Evidence Trait Ty ImplId → Bool
  | .byImpl goal implementation premises, .byImpl otherGoal otherImplementation otherPremises =>
      goal == otherGoal && (implementation == otherImplementation && beqList premises otherPremises)

def beqList [BEq Trait] [BEq Ty] [BEq ImplId] :
    List (Evidence Trait Ty ImplId) → List (Evidence Trait Ty ImplId) → Bool
  | [], [] => true
  | first :: rest, other :: remaining => beq first other && beqList rest remaining
  | _, _ => false
end

end Evidence

instance instBEqEvidence [BEq Trait] [BEq Ty] [BEq ImplId] : BEq (Evidence Trait Ty ImplId) where
  beq := Evidence.beq

namespace Evidence

private instance predicateLawful [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty] :
    LawfulBEq (Predicate Trait Ty) where
  eq_of_beq := by
    intro left right same
    cases left with
    | mk a b c =>
      cases right with
      | mk x y z =>
        change ((a == x) && ((b == y) && (c == z))) = true at same
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        rcases same with ⟨rfl, rfl, rfl⟩
        rfl
  rfl := by
    intro value
    change ((value.trait == value.trait) && ((value.subject == value.subject) && (value.arguments == value.arguments))) = true
    simp

mutual
/-- Equality reflection requires lawful comparisons of every retained field. -/
theorem eq_of_beq [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty]
    [BEq ImplId] [LawfulBEq ImplId] (left right : Evidence Trait Ty ImplId)
    (same : beq left right = true) : left = right := by
  cases left with
  | byImpl goal implementation premises =>
    cases right with
    | byImpl otherGoal otherImplementation otherPremises =>
      simp only [beq, Bool.and_eq_true, beq_iff_eq] at same
      rcases same with ⟨rfl, rfl, tails⟩
      rw [list_eq_of_beq premises otherPremises tails]

theorem list_eq_of_beq [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty]
    [BEq ImplId] [LawfulBEq ImplId] (left right : List (Evidence Trait Ty ImplId))
    (same : beqList left right = true) : left = right := by
  cases left with
  | nil => cases right <;> simp_all [beqList]
  | cons head rest =>
    cases right with
    | nil => cases same
    | cons other remaining =>
      simp only [beqList, Bool.and_eq_true] at same
      rw [eq_of_beq head other same.1, list_eq_of_beq rest remaining same.2]
end

mutual
theorem beq_self [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty]
    [BEq ImplId] [LawfulBEq ImplId] (value : Evidence Trait Ty ImplId) : beq value value = true := by
  cases value with
  | byImpl goal implementation premises => simp only [beq, BEq.rfl, Bool.true_and, list_beq_self premises]

theorem list_beq_self [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty]
    [BEq ImplId] [LawfulBEq ImplId] (values : List (Evidence Trait Ty ImplId)) : beqList values values = true := by
  cases values with
  | nil => rfl
  | cons head rest => simp only [beqList, beq_self head, list_beq_self rest, Bool.and_self]
end

end Evidence

instance instLawfulBEqEvidence [BEq Trait] [LawfulBEq Trait] [BEq Ty] [LawfulBEq Ty]
    [BEq ImplId] [LawfulBEq ImplId] : LawfulBEq (Evidence Trait Ty ImplId) where
  eq_of_beq := Evidence.eq_of_beq _ _
  rfl := Evidence.beq_self _

/-- Why bounded resolution could not make a coherent yes/no decision. -/
inductive InconclusiveReason (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  | depthLimit (goal : Predicate Trait Ty)
  | cycle (goal : Predicate Trait Ty)
  | ambiguous
      (goal : Predicate Trait Ty)
      (first second : ImplId)
  | incompleteCandidates
      (goal : Predicate Trait Ty)
      (successful : ImplId)
  deriving Repr, BEq, DecidableEq

/-- Three-way resolution result. Ambiguity is explicit inside `inconclusive`,
because selecting either overlapping implementation would be incoherent. -/
inductive Outcome (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  | success (evidence : Evidence Trait Ty ImplId)
  | noSolution
  | inconclusive (reason : InconclusiveReason Trait Ty ImplId)
  deriving Repr, BEq

/-- Small observable counters used to confirm that repeated obligations use the
completed-goal table rather than expanding the same goal again. -/
structure Statistics where
  expandedGoals : Nat := 0
  memoHits : Nat := 0
  deriving Repr, BEq, DecidableEq

/-- Public result of one bounded resolution query. -/
structure Report (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  outcome : Outcome Trait Ty ImplId
  statistics : Statistics
  deriving Repr, BEq

namespace Detail

/-! Implementation details are named so kernel-reduced consumer tests can unfold
the executable search without relying on native code generation. -/

abbrev Memo (Trait : Type u) (Ty : Type v) (ImplId : Type w) :=
  List (Predicate Trait Ty × Outcome Trait Ty ImplId)

structure SearchState (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  memo : Memo Trait Ty ImplId := []
  statistics : Statistics := {}

@[reducible] def lookupMemo? [DecidableEq Trait] [DecidableEq Ty]
    (goal : Predicate Trait Ty) : Memo Trait Ty ImplId →
      Option (Outcome Trait Ty ImplId)
  | [] => none
  | (cached, outcome) :: rest =>
      if cached = goal then some outcome else lookupMemo? goal rest

@[reducible] def isActive [DecidableEq Trait] [DecidableEq Ty]
    (goal : Predicate Trait Ty) : List (Predicate Trait Ty) → Bool
  | [] => false
  | candidate :: rest =>
      if candidate = goal then true else isActive goal rest

inductive PremiseOutcome
    (Trait : Type u) (Ty : Type v) (ImplId : Type w) where
  | success (evidence : List (Evidence Trait Ty ImplId))
  | noSolution
  | inconclusive (reason : InconclusiveReason Trait Ty ImplId)

@[reducible] def resolvePremises
    (resolveChild : SearchState Trait Ty ImplId → Predicate Trait Ty →
      Outcome Trait Ty ImplId × SearchState Trait Ty ImplId) :
    SearchState Trait Ty ImplId → List (Predicate Trait Ty) →
      PremiseOutcome Trait Ty ImplId × SearchState Trait Ty ImplId
  | state, [] => (.success [], state)
  | state, premise :: rest =>
      let (headOutcome, afterHead) := resolveChild state premise
      match headOutcome with
      | .noSolution => (.noSolution, afterHead)
      | .success headEvidence =>
          let (tailOutcome, afterTail) :=
            resolvePremises resolveChild afterHead rest
          match tailOutcome with
          | .success tailEvidence =>
              (.success (headEvidence :: tailEvidence), afterTail)
          | .noSolution => (.noSolution, afterTail)
          | .inconclusive reason => (.inconclusive reason, afterTail)
      | .inconclusive headReason =>
          let (tailOutcome, afterTail) :=
            resolvePremises resolveChild afterHead rest
          match tailOutcome with
          | .noSolution => (.noSolution, afterTail)
          | .success _ => (.inconclusive headReason, afterTail)
          | .inconclusive _ => (.inconclusive headReason, afterTail)

@[reducible] def resolveCandidates
    (resolveChild : SearchState Trait Ty ImplId → Predicate Trait Ty →
      Outcome Trait Ty ImplId × SearchState Trait Ty ImplId)
    (goal : Predicate Trait Ty) :
    SearchState Trait Ty ImplId → List (Candidate Trait Ty ImplId) →
      Option (ImplId × Evidence Trait Ty ImplId) →
      Option (InconclusiveReason Trait Ty ImplId) →
      Outcome Trait Ty ImplId × SearchState Trait Ty ImplId
  | state, [], none, none => (.noSolution, state)
  | state, [], none, some reason => (.inconclusive reason, state)
  | state, [], some (_, evidence), none => (.success evidence, state)
  | state, [], some (implId, _), some _ =>
      (.inconclusive (.incompleteCandidates goal implId), state)
  | state, candidate :: rest, firstSuccess, firstUnknown =>
      let (premiseOutcome, afterCandidate) :=
        resolvePremises resolveChild state candidate.premises
      match premiseOutcome with
      | .noSolution =>
          resolveCandidates resolveChild goal afterCandidate rest
            firstSuccess firstUnknown
      | .inconclusive reason =>
          resolveCandidates resolveChild goal afterCandidate rest
            firstSuccess (firstUnknown.orElse fun _ => some reason)
      | .success premiseEvidence =>
          let evidence := Evidence.byImpl goal candidate.implId premiseEvidence
          match firstSuccess with
          | none =>
              resolveCandidates resolveChild goal afterCandidate rest
                (some (candidate.implId, evidence)) firstUnknown
          | some (previousImpl, _) =>
              (.inconclusive
                (.ambiguous goal previousImpl candidate.implId), afterCandidate)

@[reducible] def cacheConclusive [DecidableEq Trait] [DecidableEq Ty]
    (goal : Predicate Trait Ty) (outcome : Outcome Trait Ty ImplId)
    (state : SearchState Trait Ty ImplId) : SearchState Trait Ty ImplId :=
  match outcome with
  | .success _
  | .noSolution => { state with memo := (goal, outcome) :: state.memo }
  | .inconclusive _ => state

@[reducible] def resolveAux [DecidableEq Trait] [DecidableEq Ty]
    (program : Program Trait Ty ImplId) :
    Nat → List (Predicate Trait Ty) → SearchState Trait Ty ImplId →
      Predicate Trait Ty → Outcome Trait Ty ImplId × SearchState Trait Ty ImplId
  | fuel, active, state, goal =>
      match lookupMemo? goal state.memo with
      | some outcome =>
          (outcome, { state with statistics.memoHits := state.statistics.memoHits + 1 })
      | none =>
          if isActive goal active then
            (.inconclusive (.cycle goal), state)
          else
            match fuel with
            | 0 => (.inconclusive (.depthLimit goal), state)
            | remaining + 1 =>
                let expanded :=
                  { state with
                    statistics.expandedGoals := state.statistics.expandedGoals + 1 }
                let resolveChild nextState child :=
                  resolveAux program remaining (goal :: active) nextState child
                let (ordinaryOutcome, afterOrdinary) :=
                  resolveCandidates resolveChild goal expanded
                    (program.ordinaryCandidates goal) none none
                let (outcome, finished) :=
                  match ordinaryOutcome with
                  | .noSolution =>
                      resolveCandidates resolveChild goal afterOrdinary
                        (program.defaultCandidates goal) none none
                  | .success _
                  | .inconclusive _ => (ordinaryOutcome, afterOrdinary)
                (outcome, cacheConclusive goal outcome finished)

end Detail

/-- Resolve one trait obligation with a maximum implementation-chain depth.
The ordinary implementation tier is exhaustive and has priority.  The default
tier is searched only after ordinary resolution establishes a definite
`noSolution`; any ordinary ambiguity or incomplete search blocks fallback.
Completed success and no-solution entries are tabled. Cycles, depth exhaustion,
ambiguity, and searches that might still hide a competing implementation remain
explicitly inconclusive. -/
@[reducible] def resolve [DecidableEq Trait] [DecidableEq Ty]
    (program : Program Trait Ty ImplId) (maxDepth : Nat)
    (goal : Predicate Trait Ty) : Report Trait Ty ImplId :=
  let (outcome, state) := Detail.resolveAux program maxDepth [] {} goal
  { outcome := outcome, statistics := state.statistics }

end Solcore.Frontend.TraitResolution
