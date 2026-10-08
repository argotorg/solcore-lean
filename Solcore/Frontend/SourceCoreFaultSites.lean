import Solcore.Frontend.SourceCoreBasic
import Solcore.Frontend.SourceCompilationPlan.Types

/-! Source diagnostics for returned Core language failures. Reasons are assigned
without modulo wrapping. Zero is reserved for function fallthrough, while each
ordinary local-read occurrence has its own positive reason and source span.
The next unused positive reason denotes escaped loop control. The table
contains metadata only; it never evaluates source code. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFaultSites

open SourceInference

structure Diagnostic where
  error : SourceTypedRuntime.RuntimeError
  site : SourceCoreElaboration.ErrorSite
  span : Option Syntax.SourceSpan
  deriving Repr, DecidableEq

structure ReadSite where
  expression : ExpressionId
  binder : Resolved.LocalId
  span : Syntax.SourceSpan
  reason : Core.Word
  deriving Repr, DecidableEq

structure Table where
  owner : Resolved.DeclarationId
  resultType : TypeSystem.Ty
  reads : List ReadSite
  escapedReason : Core.Word
  /-- Assignment diagnostics and other functions' boundary faults. -/
  additional : List (Core.Word × Diagnostic) := []
  deriving Repr, DecidableEq

inductive Error where
  | reasonSpaceExhausted
  | ownerMismatch (expression : ExpressionId) (binder : Resolved.LocalId)
  | duplicateOccurrence (expression : ExpressionId)
  deriving Repr, DecidableEq

private def collect (owner : Resolved.DeclarationId) :
    Nat → List Node → List ReadSite → Except Error (List ReadSite)
  | _, [], sites => .ok sites.reverse
  | index, .expression node :: rest, sites =>
      match node.form with
      | .reference _ (.local binder) => do
          if node.id.occurrence.owner ≠ owner ∨ binder.owner ≠ owner then
            throw (.ownerMismatch node.id binder)
          if sites.any (fun site => decide (site.expression = node.id)) then
            throw (.duplicateOccurrence node.id)
          let reason ← match Core.Word.ofNat? (index + 1) with
            | some reason => pure reason
            | none => .error .reasonSpaceExhausted
          collect owner (index + 1) rest
            ({ expression := node.id, binder, span := node.span, reason } :: sites)
      | _ => collect owner index rest sites
  | index, .statement _ :: rest, sites => collect owner index rest sites

def prepare (source : TypedSource) (resultType : TypeSystem.Ty) : Except Error Table := do
  let reads ← collect source.owner 0 source.nodes []
  let escapedReason ← match Core.Word.ofNat? (reads.length + 1) with
    | some reason => pure reason
    | none => .error .reasonSpaceExhausted
  pure { owner := source.owner, resultType, reads, escapedReason }

def Table.reasonAt (table : Table) (expression : ExpressionId) : Core.Word :=
  match table.reads.find? fun site => decide (site.expression = expression) with
  | some site => site.reason
  | none => Core.Word.zero

def Table.diagnostic? (table : Table) (reason : Core.Word) : Option Diagnostic :=
  if reason = Core.Word.zero then
    some {
      error := .functionFellThrough table.resultType
      site := .declaration table.owner
      span := none
    }
  else
    if reason = table.escapedReason then
      some {
        error := .controlEscapedFunction
        site := .declaration table.owner
        span := none
      }
    else
      match table.additional.find? fun site => decide (site.1 = reason) with
      | some site => some site.2
      | none =>
        (table.reads.find? fun site => decide (site.reason = reason)).map fun site => {
          error := .uninitializedLocal site.binder
          site := .occurrence site.expression.occurrence
          span := some site.span
        }

theorem Table.fallthrough_diagnostic (table : Table) :
    table.diagnostic? Core.Word.zero = some {
      error := .functionFellThrough table.resultType
      site := .declaration table.owner
      span := none
    } := by simp [Table.diagnostic?]

/-- A checked positive reason is recovered with its exact occurrence and span. -/
theorem Table.read_diagnostic {table : Table} {site : ReadSite}
    (positive : site.reason ≠ Core.Word.zero)
    (ordinary : site.reason ≠ table.escapedReason)
    (noBoundary : table.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : table.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site) :
    table.diagnostic? site.reason = some {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span
    } := by simp [Table.diagnostic?, positive, ordinary, noBoundary, found]

theorem Table.escaped_diagnostic (table : Table)
    (positive : table.escapedReason ≠ Core.Word.zero) :
    table.diagnostic? table.escapedReason = some {
      error := .controlEscapedFunction
      site := .declaration table.owner
      span := none
    } := by simp [Table.diagnostic?, positive]


/-- Static provenance of the original metadata collector. Each constructor
retains the actual checked token and the same accumulated read sites. -/
inductive ReadCollection (owner : Resolved.DeclarationId) :
    Nat → List Node → List ReadSite → List ReadSite → Prop where
  | nil {index sites} : ReadCollection owner index [] sites sites.reverse
  | local {index node name binder rest sites result reason}
      (form : node.form = .reference name (.local binder))
      (owned : node.id.occurrence.owner = owner ∧ binder.owner = owner)
      (fresh : ∀ site ∈ sites, site.expression ≠ node.id)
      (issued : Core.Word.ofNat? (index + 1) = some reason)
      (remaining : ReadCollection owner (index + 1) rest
        ({ expression := node.id, binder, span := node.span, reason } :: sites) result) :
      ReadCollection owner index (.expression node :: rest) sites result
  | other {index node rest sites result}
      (ordinary : ∀ name binder, node.form ≠ .reference name (.local binder))
      (remaining : ReadCollection owner index rest sites result) :
      ReadCollection owner index (.expression node :: rest) sites result
  | statement {index node rest sites result}
      (remaining : ReadCollection owner index rest sites result) :
      ReadCollection owner index (.statement node :: rest) sites result

private theorem read_bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem collect_receipt {owner : Resolved.DeclarationId} {index : Nat}
    {nodes : List Node} {sites result : List ReadSite}
    (accepted : collect owner index nodes sites = .ok result) :
    ReadCollection owner index nodes sites result := by
  induction nodes generalizing index sites with
  | nil => simp only [collect, Except.ok.injEq] at accepted; subst result; exact .nil
  | cons node rest ih =>
    cases node with
    | statement node => exact .statement (ih accepted)
    | expression node =>
      simp only [collect] at accepted
      split at accepted
      · next name binder form =>
        split at accepted
        · simp [bind, Except.bind] at accepted
        · next owned =>
          split at accepted
          · simp [bind, Except.bind] at accepted
          · next fresh =>
            split at accepted
            · next reason checked =>
              simp only [pure, Except.pure, bind, Except.bind] at accepted
              exact .local form (by grind)
                (by simpa only [Bool.not_eq_true, List.any_eq_false, decide_eq_false_iff_not] using fresh)
                checked (ih accepted)
            · simp [bind, Except.bind] at accepted
      · next ordinary =>
        exact .other (by intro name binder same; simp_all) (ih accepted)

/-- Every original accumulated row remains in the completed collection. -/
theorem ReadCollection.retains {owner : Resolved.DeclarationId} {index : Nat}
    {nodes : List Node} {sites result : List ReadSite}
    (receipt : ReadCollection owner index nodes sites result) :
    ∀ site ∈ sites, site ∈ result := by
  induction receipt with
  | nil => intro site member; exact List.mem_reverse.mpr member
  | «local» _ _ _ _ _ ih => intro site member; exact ih site (List.mem_cons_of_mem _ member)
  | other _ _ ih | statement _ ih => exact ih

/-- An actual Source local-reference node has its complete issued row. -/
theorem ReadCollection.covers {owner : Resolved.DeclarationId} {index : Nat}
    {nodes : List Node} {sites result : List ReadSite}
    (receipt : ReadCollection owner index nodes sites result)
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : .expression node ∈ nodes) (form : node.form = .reference name (.local binder)) :
    ∃ site ∈ result, site.expression = node.id ∧ site.binder = binder ∧ site.span = node.span := by
  induction receipt with
  | nil => simp at member
  | @«local» index selected selectedName selectedBinder rest sites result reason actualForm _ _ _ remaining ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
      have equal := actualForm.symm.trans form
      cases equal
      exact ⟨_, remaining.retains _ List.mem_cons_self, rfl, rfl, rfl⟩
    · exact ih member
  | other ordinary remaining ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same; exact (ordinary _ _ form).elim
    · exact ih member
  | statement remaining ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same
    · exact ih member

private structure ReadInventory (next : Nat) (sites : List ReadSite) : Prop where
  bounded : ∀ site ∈ sites, 0 < site.reason.val ∧ site.reason.val ≤ next
  expressions : ∀ left ∈ sites, ∀ right ∈ sites, left.expression = right.expression → left = right
  reasons : ∀ left ∈ sites, ∀ right ∈ sites, left.reason = right.reason → left = right

private theorem read_word_value {number : Nat} {word : Core.Word}
    (accepted : Core.Word.ofNat? number = some word) : word.val = number := by
  unfold Core.Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private theorem ReadInventory.cons {index : Nat} {sites : List ReadSite}
    (inventory : ReadInventory index sites) {node : ExpressionNode} {binder : Resolved.LocalId} {reason : Core.Word}
    (fresh : ∀ site ∈ sites, site.expression ≠ node.id)
    (issued : Core.Word.ofNat? (index + 1) = some reason) :
    ReadInventory (index + 1) ({ expression := node.id, binder, span := node.span, reason } :: sites) := by
  have number := read_word_value issued
  refine ⟨?_, ?_, ?_⟩
  · intro site member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only using (show 0 < reason.val ∧ reason.val ≤ index + 1 by omega)
    · have bound := inventory.bounded site member; exact ⟨bound.1, by omega⟩
  · intro left leftMember right rightMember same
    rcases List.mem_cons.mp leftMember with rfl | leftMember
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · rfl
      · exact (fresh right rightMember same.symm).elim
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · exact (fresh left leftMember same).elim
      · exact inventory.expressions left leftMember right rightMember same
  · intro left leftMember right rightMember same
    rcases List.mem_cons.mp leftMember with rfl | leftMember
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · rfl
      · have bound := inventory.bounded right rightMember
        have equal := congrArg Fin.val same
        dsimp only at equal; omega
    · rcases List.mem_cons.mp rightMember with rfl | rightMember
      · have bound := inventory.bounded left leftMember
        have equal := congrArg Fin.val same
        dsimp only at equal; omega
      · exact inventory.reasons left leftMember right rightMember same

private theorem ReadInventory.reverse {index : Nat} {sites : List ReadSite}
    (inventory : ReadInventory index sites) : ReadInventory index sites.reverse := by
  exact ⟨fun site member => inventory.bounded site (List.mem_reverse.mp member),
    fun left leftMember right rightMember => inventory.expressions left (List.mem_reverse.mp leftMember)
      right (List.mem_reverse.mp rightMember),
    fun left leftMember right rightMember => inventory.reasons left (List.mem_reverse.mp leftMember)
      right (List.mem_reverse.mp rightMember)⟩

private theorem ReadCollection.inventory {owner : Resolved.DeclarationId} {index : Nat}
    {nodes : List Node} {sites result : List ReadSite}
    (receipt : ReadCollection owner index nodes sites result) :
    index = sites.length → ReadInventory index sites → ReadInventory result.length result := by
  induction receipt with
  | nil => intro same inventory; simpa only [List.length_reverse, same] using inventory.reverse
  | «local» _ _ fresh issued _ ih =>
    intro same inventory
    exact ih (by simp only [List.length_cons, same]) (inventory.cons fresh issued)
  | other _ _ ih | statement _ ih => exact ih

private theorem read_find_unique {α : Type} [DecidableEq α] {sites : List ReadSite} {site : ReadSite}
    (key : ReadSite → α) (member : site ∈ sites)
    (unique : ∀ candidate ∈ sites, key candidate = key site → candidate = site) :
    sites.find? (fun candidate => decide (key candidate = key site)) = some site := by
  induction sites with
  | nil => simp at member
  | cons head tail ih =>
    by_cases sameKey : key head = key site
    · have same := unique head List.mem_cons_self sameKey
      simp [same]
    · have tailMember : site ∈ tail := by
        rcases List.mem_cons.mp member with same | member
        · exact (sameKey (same ▸ rfl)).elim
        · exact member
      simpa only [List.find?_cons, decide_eq_false_iff_not.mpr sameKey, Bool.false_eq_true, ↓reduceIte] using
        ih tailMember (fun candidate belongs => unique candidate (List.mem_cons_of_mem head belongs))

/-- Acceptance retains the original full Source node collection and checked
escaped token; later program retokening can consume this static receipt. -/
theorem prepare_read_collection {source : TypedSource} {resultType : TypeSystem.Ty} {table : Table}
    (accepted : prepare source resultType = .ok table) :
    ReadCollection source.owner 0 source.nodes [] table.reads ∧
    table.owner = source.owner ∧ table.resultType = resultType ∧
    Core.Word.ofNat? (table.reads.length + 1) = some table.escapedReason ∧ table.additional = [] := by
  unfold prepare at accepted
  obtain ⟨reads, collected, accepted⟩ := read_bind_ok accepted
  split at accepted
  · next escaped issued =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    cases accepted
    exact ⟨collect_receipt collected, rfl, rfl, issued, rfl⟩
  · simp [bind, Except.bind] at accepted


/-- Actual preparation supplies both lookup keys and all ordinary read token
checks. The same full node, binder and span are recovered in the diagnostic. -/
theorem prepare_local_read {source : TypedSource} {resultType : TypeSystem.Ty} {table : Table}
    (accepted : prepare source resultType = .ok table)
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : .expression node ∈ source.nodes) (form : node.form = .reference name (.local binder)) :
    ∃ site,
      table.reads.find? (fun candidate => decide (candidate.expression = node.id)) = some site ∧
      site.expression = node.id ∧ site.binder = binder ∧ site.span = node.span ∧
      table.reasonAt node.id = site.reason ∧ site.reason ≠ Core.Word.zero ∧
      site.reason ≠ table.escapedReason ∧
      table.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site ∧
      table.diagnostic? site.reason = some {
        error := .uninitializedLocal binder
        site := .occurrence node.id.occurrence
        span := some node.span
      } := by
  obtain ⟨receipt, _owner, _result, escaped, additional⟩ := prepare_read_collection accepted
  have initial : ReadInventory 0 ([] : List ReadSite) := by
    constructor <;> simp
  have inventory := receipt.inventory rfl initial
  obtain ⟨site, belongs, expression, binderEq, spanEq⟩ := receipt.covers member form
  have byExpression := read_find_unique (fun candidate => candidate.expression) belongs
    (fun candidate member same => inventory.expressions candidate member site belongs same)
  have byReason := read_find_unique (fun candidate => candidate.reason) belongs
    (fun candidate member same => inventory.reasons candidate member site belongs same)
  have bound := inventory.bounded site belongs
  have positive : site.reason ≠ Core.Word.zero := by
    intro same; have number := congrArg Fin.val same; change site.reason.val = 0 at number; omega
  have ordinary : site.reason ≠ table.escapedReason := by
    intro same; have number := read_word_value escaped
    have equal := congrArg Fin.val same; omega
  have noAdditional : table.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none := by
    rw [additional]; rfl
  have diagnostic := Table.read_diagnostic positive ordinary noAdditional byReason
  refine ⟨site, ?_, expression, binderEq, spanEq, ?_, positive, ordinary, byReason, ?_⟩
  · simpa only [expression] using byExpression
  · unfold Table.reasonAt; rw [← expression, byExpression]
  · simpa only [expression, binderEq, spanEq] using diagnostic

/-- Duplicate checks in actual preparation make Source occurrence lookup
unique before the program replaces reason identities. -/
theorem prepare_read_occurrences_unique {source : TypedSource} {resultType : TypeSystem.Ty} {table : Table}
    (accepted : prepare source resultType = .ok table) :
    ∀ left ∈ table.reads, ∀ right ∈ table.reads, left.expression = right.expression → left = right := by
  have receipt := (prepare_read_collection accepted).1
  have initial : ReadInventory 0 ([] : List ReadSite) := by constructor <;> simp
  exact (receipt.inventory rfl initial).expressions

end Solcore.Frontend.SourceCoreFaultSites
