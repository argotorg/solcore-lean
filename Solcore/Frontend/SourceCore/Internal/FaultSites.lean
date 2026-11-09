import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCompilationPlan

/-!
# Fault sites

Source diagnostics for Core language failures: reasons, read and assignment sites, and program-wide
identities.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreFaultSites
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
        match table.reads.find? fun site => decide (site.reason = reason) with
        | some site => some {
            error := .uninitializedLocal site.binder
            site := .occurrence site.expression.occurrence
            span := some site.span
          }
        | none => (SourceCorePanics.code? reason).map fun code => {
            error := .panic code
            site := .declaration table.owner
            span := none
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

/-- No reason of the table lies in the panic range, so the reason of a panic
decodes as that panic. -/
def Table.PanicFree (table : Table) : Prop :=
  table.escapedReason.val < SourceCorePanics.base ∧
    (∀ site ∈ table.reads, site.reason.val < SourceCorePanics.base) ∧
    ∀ item ∈ table.additional, item.1.val < SourceCorePanics.base

/-- A panic reason decodes as its panic, at the table's function. -/
theorem Table.panic_diagnostic {table : Table} (free : table.PanicFree) (code : UInt8) :
    table.diagnostic? (SourceCorePanics.reason code) = some {
      error := .panic code
      site := .declaration table.owner
      span := none
    } := by
  obtain ⟨escaped, reads, additional⟩ := free
  have high := SourceCorePanics.base_le_reason code
  have positive : 0 < SourceCorePanics.base := by unfold SourceCorePanics.base; decide
  have nonzero : SourceCorePanics.reason code ≠ Core.Word.zero := by
    intro same
    have value := congrArg Fin.val same
    change (SourceCorePanics.reason code).val = 0 at value
    omega
  have notEscaped : SourceCorePanics.reason code ≠ table.escapedReason := by
    intro same
    have value := congrArg Fin.val same
    omega
  have noAdditional :
      table.additional.find? (fun site => decide (site.1 = SourceCorePanics.reason code)) = none := by
    apply List.find?_eq_none.mpr
    intro item member matched
    have value := congrArg Fin.val (of_decide_eq_true matched)
    have below := additional item member
    omega
  have noRead :
      table.reads.find? (fun site => decide (site.reason = SourceCorePanics.reason code)) = none := by
    apply List.find?_eq_none.mpr
    intro site member matched
    have value := congrArg Fin.val (of_decide_eq_true matched)
    have below := reads site member
    omega
  simp [Table.diagnostic?, nonzero, notEscaped, noAdditional, noRead, SourceCorePanics.code?_reason]

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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAssignmentFaultSites
/-! Metadata for absent Word/Integer assignment operands. Header items lack their own
occurrence and span, so they use the owning for statement. Repeated items with
the same site, binder and kind share a diagnostic. Reasons never wrap. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignmentFaultSites

open SourceInference

inductive Kind where
  | value (operator : Syntax.ValueAssignOp)
  | bitNot
  deriving Repr, BEq, DecidableEq

structure Site where
  site : SourceCoreElaboration.ErrorSite
  binder : Resolved.LocalId
  kind : Kind
  span : Syntax.SourceSpan
  reason : Core.Word
  /-- Successful RHS values match this checked scalar assignment target type. -/
  rhsType : TypeSystem.Ty := .word
  deriving Repr, DecidableEq

structure Table where
  sites : List Site
  deriving Repr, DecidableEq

inductive Error where
  | reasonSpaceExhausted
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  deriving Repr, DecidableEq

def Site.diagnostic (site : Site) : SourceCoreFaultSites.Diagnostic := {
  error := match site.kind with
    | .value operator => .invalidAssignmentOperands operator none (some site.rhsType)
    | .bitNot => .invalidUnaryOperand .bitNot none
  site := site.site
  span := some site.span
}

def Table.length (table : Table) : Nat := table.sites.length

def Table.reasonAt (table : Table) (location : SourceCoreElaboration.ErrorSite)
    (binder : Resolved.LocalId) (kind : Kind) : Core.Word :=
  match table.sites.find? fun site => decide
      (site.site = location ∧ site.binder = binder ∧ site.kind = kind) with
  | some site => site.reason
  | none => Core.Word.zero

def Table.diagnostics (table : Table) : List (Core.Word × SourceCoreFaultSites.Diagnostic) :=
  table.sites.map fun site => (site.reason, site.diagnostic)

def Table.diagnostic? (table : Table) (reason : Core.Word) : Option SourceCoreFaultSites.Diagnostic :=
  (table.sites.find? fun site => decide (site.reason = reason)).map Site.diagnostic

def add (owner : Resolved.DeclarationId) (firstReason : Nat) (sites : List Site)
    (location : SourceCoreElaboration.ErrorSite) (span : Syntax.SourceSpan)
    (assignment : AssignmentResolution) (kind : Kind) : Except Error (List Site) := do
  if assignment.target.root.owner ≠ owner then
    throw (.ownerMismatch owner assignment.target.root.owner)
  if assignment.target.type ≠ .word ∧ assignment.target.type ≠ .integer then return sites
  if sites.any (fun site => decide
      (site.site = location ∧ site.binder = assignment.target.root ∧ site.kind = kind)) then
    return sites
  let reason ← match Core.Word.ofNat? (firstReason + sites.length) with
    | some reason => pure reason
    | none => .error .reasonSpaceExhausted
  pure (sites ++ [{ site := location, binder := assignment.target.root, kind, span, reason, rhsType := assignment.target.type }])

def addItem (owner : Resolved.DeclarationId) (firstReason : Nat)
    (location : SourceCoreElaboration.ErrorSite) (span : Syntax.SourceSpan) :
    List Site → ForItemForm → Except Error (List Site)
  | sites, .assignValue assignment operator _ =>
      if operator = .equal then pure sites
      else add owner firstReason sites location span assignment (.value operator)
  | sites, .assignBitNot assignment => add owner firstReason sites location span assignment .bitNot
  | sites, _ => pure sites

def addStatement (owner : Resolved.DeclarationId) (firstReason : Nat)
    (sites : List Site) (node : StatementNode) : Except Error (List Site) := do
  if node.id.occurrence.owner ≠ owner then throw (.ownerMismatch owner node.id.occurrence.owner)
  let location := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  match node.form with
  | .assignValue assignment operator _ =>
      if operator = .equal then pure sites
      else add owner firstReason sites location node.span assignment (.value operator)
  | .assignBitNot assignment => add owner firstReason sites location node.span assignment .bitNot
  | .forLoop initializer _ post _ =>
      (initializer ++ post).foldlM (addItem owner firstReason location node.span) sites
  | _ => pure sites

/-- Inference records containing statements after their children. Sorting by
their original span restores source order before assigning diagnostic codes. -/
def prepare (source : TypedSource) (firstReason : Nat) : Except Error Table := do
  let statements := (source.nodes.filterMap fun
    | .statement node => some node
    | _ => none).mergeSort (fun left right => decide (left.span.startByte ≤ right.span.startByte))
  let sites ← statements.foldlM (addStatement source.owner firstReason) []
  pure { sites }

theorem Table.reasonAt_found {table : Table} {site : Site}
    {location : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {kind : Kind}
    (found : table.sites.find? (fun candidate => decide
      (candidate.site = location ∧ candidate.binder = binder ∧ candidate.kind = kind)) = some site) :
    table.reasonAt location binder kind = site.reason := by
  unfold Table.reasonAt
  rw [found]

theorem Table.diagnostic_found {table : Table} {site : Site}
    (found : table.sites.find? (fun candidate => decide (candidate.reason = site.reason)) = some site) :
    table.diagnostic? site.reason = some site.diagnostic := by
  simp [Table.diagnostic?, found]


/-- Every retained token belongs to the exact range reserved by the original
assignment preparation. Duplicate sites reuse the existing checked token. -/
private structure RangeInventory (first : Nat) (sites : List Site) : Prop where
  bounded : ∀ site ∈ sites, first ≤ site.reason.val ∧ site.reason.val < first + sites.length
  unique : ∀ left ∈ sites, ∀ right ∈ sites, left.reason = right.reason → left = right

private theorem range_word_value {number : Nat} {word : Core.Word}
    (issued : Core.Word.ofNat? number = some word) : word.val = number := by
  unfold Core.Word.ofNat? at issued
  split at issued
  · cases issued; rfl
  · cases issued

private theorem RangeInventory.append {first : Nat} {sites : List Site}
    (inventory : RangeInventory first sites) {selected : Site}
    (issued : Core.Word.ofNat? (first + sites.length) = some selected.reason) :
    RangeInventory first (sites ++ [selected]) := by
  have number := range_word_value issued
  refine ⟨?_, ?_⟩
  · intro site member
    rcases List.mem_append.mp member with member | member
    · have bound := inventory.bounded site member
      simp only [List.length_append, List.length_singleton]
      exact ⟨bound.1, by omega⟩
    · have same : site = selected := by simpa only [List.mem_singleton] using member
      subst site
      simp only [List.length_append, List.length_singleton]
      exact ⟨by omega, by omega⟩
  · intro left leftMember right rightMember same
    rcases List.mem_append.mp leftMember with leftMember | leftMember
    · rcases List.mem_append.mp rightMember with rightMember | rightMember
      · exact inventory.unique left leftMember right rightMember same
      · have equal : right = selected := by simpa only [List.mem_singleton] using rightMember
        subst right
        have bound := inventory.bounded left leftMember
        have equal := congrArg Fin.val same
        omega
    · have equal : left = selected := by simpa only [List.mem_singleton] using leftMember
      subst left
      rcases List.mem_append.mp rightMember with rightMember | rightMember
      · have bound := inventory.bounded right rightMember
        have equal := congrArg Fin.val same
        omega
      · have equal : right = selected := by simpa only [List.mem_singleton] using rightMember
        exact equal.symm

private theorem range_bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem add_range {owner : Resolved.DeclarationId} {first : Nat} {sites result : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (inventory : RangeInventory first sites)
    (accepted : add owner first sites location span assignment kind = .ok result) :
    RangeInventory first result := by
  by_cases owned : assignment.target.root.owner = owner
  · by_cases unsupported : assignment.target.type ≠ .word ∧ assignment.target.type ≠ .integer
    · simp [add, owned, unsupported] at accepted
      subst result
      exact inventory
    · by_cases duplicate : ∃ site ∈ sites,
          site.site = location ∧ site.binder = assignment.target.root ∧ site.kind = kind
      · simp [add, owned, unsupported, duplicate] at accepted
        subst result
        exact inventory
      · cases issued : Core.Word.ofNat? (first + sites.length) with
        | none =>
          simp [add, owned, unsupported, duplicate, issued] at accepted
          cases accepted
        | some reason =>
          simp [add, owned, unsupported, duplicate, issued] at accepted
          subst result
          exact inventory.append issued
  · simp [add, owned, bind, Except.bind] at accepted

private theorem addItem_range {owner : Resolved.DeclarationId} {first : Nat}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {sites result : List Site} {item : ForItemForm}
    (inventory : RangeInventory first sites)
    (accepted : addItem owner first location span sites item = .ok result) :
    RangeInventory first result := by
  cases item <;> simp only [addItem] at accepted
  all_goals try { simp only [pure, Except.pure, Except.ok.injEq] at accepted; subst result; exact inventory }
  case assignValue assignment operator rhs =>
    split at accepted
    · simp only [pure, Except.pure, Except.ok.injEq] at accepted; subst result; exact inventory
    · exact add_range inventory accepted
  case assignBitNot assignment => exact add_range inventory accepted

private theorem fold_range {α : Type} {first : Nat} {step : List Site → α → Except Error (List Site)}
    (preserves : ∀ {sites result item}, RangeInventory first sites →
      step sites item = .ok result → RangeInventory first result)
    {items : List α} {sites result : List Site}
    (inventory : RangeInventory first sites) (accepted : items.foldlM step sites = .ok result) :
    RangeInventory first result := by
  induction items generalizing sites with
  | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst result; exact inventory
  | cons item rest ih =>
    simp only [List.foldlM_cons] at accepted
    obtain ⟨middle, acted, remaining⟩ := range_bind_ok accepted
    exact ih (preserves inventory acted) remaining

private theorem addStatement_range {owner : Resolved.DeclarationId} {first : Nat}
    {sites result : List Site} {node : StatementNode}
    (inventory : RangeInventory first sites)
    (accepted : addStatement owner first sites node = .ok result) :
    RangeInventory first result := by
  by_cases owned : node.id.occurrence.owner = owner
  · cases form : node.form <;> simp [addStatement, owned, form] at accepted
    all_goals try { subst result; exact inventory }
    case assignValue assignment operator rhs =>
      by_cases equal : operator = .equal
      · simp [equal] at accepted; subst result; exact inventory
      · simp [equal] at accepted
        exact add_range inventory accepted
    case assignBitNot assignment => exact add_range inventory accepted
    case forLoop initializer condition post body =>
      obtain ⟨middle, initialized, posted⟩ := range_bind_ok accepted
      have middleInventory := fold_range
        (step := addItem owner first (.occurrence node.id.occurrence) node.span)
        (fun inventory accepted => addItem_range inventory accepted) inventory initialized
      exact fold_range (step := addItem owner first (.occurrence node.id.occurrence) node.span)
        (fun inventory accepted => addItem_range inventory accepted) middleInventory posted
  · simp [addStatement, owned, bind, Except.bind] at accepted

/-- Successful original preparation reserves one contiguous, nonwrapping range.
Both retained rows and exported diagnostic pairs use exactly that range. -/
theorem prepare_token_range {source : TypedSource} {first : Nat} {table : Table}
    (accepted : prepare source first = .ok table) :
    (∀ site ∈ table.sites, first ≤ site.reason.val ∧ site.reason.val < first + table.length) ∧
    (∀ pair ∈ table.diagnostics, first ≤ pair.1.val ∧ pair.1.val < first + table.length) ∧
    (∀ left ∈ table.sites, ∀ right ∈ table.sites, left.reason = right.reason → left = right) := by
  unfold prepare at accepted
  obtain ⟨sites, collected, accepted⟩ := range_bind_ok accepted
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst table
  have initial : RangeInventory first [] := by constructor <;> simp
  have inventory := fold_range (fun inventory accepted => addStatement_range inventory accepted) initial collected
  refine ⟨inventory.bounded, ?_, inventory.unique⟩
  intro pair member
  obtain ⟨site, belongs, rfl⟩ := List.mem_map.mp member
  exact inventory.bounded site belongs

end Solcore.Frontend.SourceCoreAssignmentFaultSites
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreProgramFaultSites
/-! Program-wide, nonwrapping failure identities. Each specialization keeps its
own read provider; the root entry carries their combined diagnostic table.
This pass only processes source metadata. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreProgramFaultSites

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Function where
  key : Key
  table : SourceCoreFaultSites.Table
  assignments : SourceCoreAssignmentFaultSites.Table
  fellThroughReason : Core.Word
  deriving Repr

structure Program where
  functions : List Function
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | sites (error : SourceCoreFaultSites.Error)
  | assignments (error : SourceCoreAssignmentFaultSites.Error)
  | plan (error : SourceCompilationPlan.Error)
  | invalidFunctionType (key : Key)
  deriving Repr, DecidableEq

private def reason (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? index with
  | some value => pure value
  | none => .error (.sites .reasonSpaceExhausted)

private def collect : Nat → List SourceSpecialization.SpecializedFunction → Except Error (List Function)
  | _, [] => pure []
  | next, specialized :: rest => do
      let sourceResult ← match specialized.function.type with
        | .function _ result => pure result
        | _ => .error (.invalidFunctionType specialized.key)
      let baseSites ← (SourceCoreFaultSites.prepare specialized.function.typedBody sourceResult).mapError Error.sites
      let reads ← baseSites.reads.zipIdx.mapM fun (site, index) => do
        let token ← reason (next + index)
        pure { site with reason := token }
      let assignments ← (SourceCoreAssignmentFaultSites.prepare specialized.function.typedBody
        (next + reads.length)).mapError Error.assignments
      let fellThroughReason ← reason (next + reads.length + assignments.length)
      let escapedReason ← reason (next + reads.length + assignments.length + 1)
      let remaining ← collect (next + reads.length + assignments.length + 2) rest
      let function : Function := {
        key := specialized.key
        table := { baseSites with
          reads := reads
          escapedReason := escapedReason
          additional := assignments.diagnostics }
        assignments
        fellThroughReason := fellThroughReason
      }
      pure (function :: remaining)

def Program.find? (program : Program) (key : Key) : Option Function :=
  program.functions.find? fun function => decide (function.key = key)

/-- Call after canonical plan authentication. Zero remains the root's public
fallthrough token; positive boundary reasons identify the actual callee. -/
def prepare (plan : Plan) (root : Key) : Except Error Program := do
  let functions ← collect 1 plan.specializations
  let selected ← match functions.find? (fun function => decide (function.key = root)) with
    | some function => pure function
    | none => .error (.plan (.missingSpecialization root))
  let reads := functions.flatMap (·.table.reads)
  let additional := functions.flatMap fun function => function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none
    })]
  pure { functions, rootTable := { selected.table with reads, additional } }

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- A program read row keeps its original Source identity while the genuine
checked conversion replaces only its reason. The input index is retained. -/
inductive ReadRetokening (first : Nat) :
    List (SourceCoreFaultSites.ReadSite × Nat) → List SourceCoreFaultSites.ReadSite → Prop where
  | nil : ReadRetokening first [] []
  | cons {site index rest result token}
      (issued : Core.Word.ofNat? (first + index) = some token)
      (remaining : ReadRetokening first rest result) :
      ReadRetokening first ((site, index) :: rest) ({ site with reason := token } :: result)

private theorem retoken_receipt {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {result : List SourceCoreFaultSites.ReadSite}
    (accepted : pairs.mapM (fun (site, index) => do
      let token ← reason (first + index)
      pure { site with reason := token }) = .ok result) : ReadRetokening first pairs result := by
  induction pairs generalizing result with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst result; exact .nil
  | cons pair rest ih =>
    simp only [List.mapM_cons] at accepted
    obtain ⟨head, made, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    rcases pair with ⟨site, index⟩
    dsimp only at made
    unfold reason at made
    split at made
    · next token issued =>
      simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at made
      subst head
      exact .cons issued (ih remaining)
    · simp [bind, Except.bind] at made

/-- The selected function retains its actual source preparation, original
retokening, assignment start and both issued boundary identities. -/
inductive FunctionIssuance (first : Nat) (row : SourceSpecialization.SpecializedFunction)
    (own : Function) : Prop where
  | intro {parameter result : TypeSystem.Ty} {base : SourceCoreFaultSites.Table}
      (key : own.key = row.key)
      (functionType : row.function.type = .function parameter result)
      (prepared : SourceCoreFaultSites.prepare row.function.typedBody result = .ok base)
      (reads : ReadRetokening first base.reads.zipIdx own.table.reads)
      (assignments : SourceCoreAssignmentFaultSites.prepare row.function.typedBody
        (first + own.table.reads.length) = .ok own.assignments)
      (fellThrough : Core.Word.ofNat? (first + own.table.reads.length + own.assignments.length) = some own.fellThroughReason)
      (escaped : Core.Word.ofNat? (first + own.table.reads.length + own.assignments.length + 1) = some own.table.escapedReason)
      (owner : own.table.owner = base.owner)
      (resultType : own.table.resultType = base.resultType)
      (additional : own.table.additional = own.assignments.diagnostics) : FunctionIssuance first row own

/-- This static receipt follows the same original ordered program collection. -/
inductive ProgramIssuance : Nat → List SourceSpecialization.SpecializedFunction → List Function → Prop where
  | nil {first} : ProgramIssuance first [] []
  | cons {first row rows own functions}
      (issued : FunctionIssuance first row own)
      (remaining : ProgramIssuance (first + own.table.reads.length + own.assignments.length + 2) rows functions) :
      ProgramIssuance first (row :: rows) (own :: functions)

private theorem reason_ok {index : Nat} {token : Core.Word} (accepted : reason index = .ok token) :
    Core.Word.ofNat? index = some token := by
  unfold reason at accepted
  split at accepted
  · next actual issued => cases accepted; exact issued
  · cases accepted

private theorem collect_issuance {first : Nat} {rows : List SourceSpecialization.SpecializedFunction} {functions : List Function}
    (accepted : collect first rows = .ok functions) : ProgramIssuance first rows functions := by
  induction rows generalizing first functions with
  | nil => simp only [collect, pure, Except.pure, Except.ok.injEq] at accepted; subst functions; exact .nil
  | cons row rows ih =>
    simp only [collect] at accepted
    split at accepted
    · next parameter result functionType =>
      obtain ⟨actualResult, resultMade, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, Except.ok.injEq] at resultMade
      subst actualResult
      obtain ⟨base, baseMade, accepted⟩ := bind_ok accepted
      obtain ⟨reads, readsMade, accepted⟩ := bind_ok accepted
      obtain ⟨assignments, assignmentsMade, accepted⟩ := bind_ok accepted
      obtain ⟨fellThrough, fellMade, accepted⟩ := bind_ok accepted
      obtain ⟨escaped, escapedMade, accepted⟩ := bind_ok accepted
      obtain ⟨remaining, remainingMade, accepted⟩ := bind_ok accepted
      cases accepted
      exact .cons (.intro rfl functionType (mapError_ok baseMade) (retoken_receipt readsMade)
        (mapError_ok assignmentsMade) (reason_ok fellMade) (reason_ok escapedMade) rfl rfl rfl) (ih remainingMade)
    · simp [bind, Except.bind] at accepted

private theorem collect_assignments_member {next : Nat}
    {rows : List SourceSpecialization.SpecializedFunction} {functions : List Function} {own : Function}
    (accepted : collect next rows = .ok functions) (member : own ∈ functions) :
    ∃ row, row ∈ rows ∧ row.key = own.key ∧
      ∃ first, SourceCoreAssignmentFaultSites.prepare row.function.typedBody first = .ok own.assignments := by
  induction rows generalizing next functions with
  | nil =>
    simp only [collect, pure, Except.pure] at accepted
    cases accepted
    simp at member
  | cons row rest ih =>
    simp only [collect] at accepted
    split at accepted
    · obtain ⟨result, _resultMade, accepted⟩ := bind_ok accepted
      obtain ⟨sites, _sitesMade, accepted⟩ := bind_ok accepted
      obtain ⟨reads, _readsMade, accepted⟩ := bind_ok accepted
      obtain ⟨assignments, assignmentsMade, accepted⟩ := bind_ok accepted
      obtain ⟨fellThrough, _fellThroughMade, accepted⟩ := bind_ok accepted
      obtain ⟨escaped, _escapedMade, accepted⟩ := bind_ok accepted
      obtain ⟨remaining, remainingMade, accepted⟩ := bind_ok accepted
      cases accepted
      rcases List.mem_cons.mp member with same | member
      · subst own
        exact ⟨row, List.mem_cons_self, rfl, next + reads.length, mapError_ok assignmentsMade⟩
      · obtain ⟨selected, belongs, key, first, prepared⟩ := ih remainingMade member
        exact ⟨selected, List.mem_cons_of_mem row belongs, key, first, prepared⟩
    · simp [bind, Except.bind] at accepted

private theorem exact_member {plan : Plan} {key : Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

/-- The actual selected diagnostic row retains the assignment preparation
for its exact specialization Source, including its allocated first token. -/
theorem prepare_assignments_at {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare row.function.typedBody first = .ok own.assignments := by
  unfold prepare at accepted
  obtain ⟨functions, collected, accepted⟩ := bind_ok accepted
  split at accepted
  · obtain ⟨selected, _selectedFound, accepted⟩ := bind_ok accepted
    cases accepted
    have member : own ∈ functions := List.mem_of_find?_eq_some found
    have key : own.key = key := of_decide_eq_true (List.find?_some (p := fun candidate : Function => decide (candidate.key = key)) found)
    obtain ⟨candidate, belongs, same, first, prepared⟩ := collect_assignments_member collected member
    have actual := exact_member record belongs (same.trans key)
    subst candidate
    exact ⟨first, prepared⟩
  · simp [bind, Except.bind] at accepted

/-- Retokening preserves every row's complete Source identity. -/
theorem ReadRetokening.origin {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    ∀ site ∈ reads, ∃ original index,
      (original, index) ∈ pairs ∧ site.expression = original.expression ∧
      site.binder = original.binder ∧ site.span = original.span ∧
      Core.Word.ofNat? (first + index) = some site.reason := by
  induction receipt with
  | nil => intro site member; simp at member
  | @cons original index rest result token issued remaining ih =>
    intro site member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨original, index, List.mem_cons_self, rfl, rfl, rfl, issued⟩
    · obtain ⟨original, index, belongs, expression, binder, span, issued⟩ := ih site member
      exact ⟨original, index, List.mem_cons_of_mem _ belongs, expression, binder, span, issued⟩

/-- Every input row is retained with the same index and exact checked token. -/
theorem ReadRetokening.covers {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    ∀ original index, (original, index) ∈ pairs → ∃ site ∈ reads,
      site.expression = original.expression ∧ site.binder = original.binder ∧
      site.span = original.span ∧ Core.Word.ofNat? (first + index) = some site.reason := by
  induction receipt with
  | nil => intro original index member; simp at member
  | @cons head position rest result token issued remaining ih =>
    intro original index member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨_, List.mem_cons_self, rfl, rfl, rfl, issued⟩
    · obtain ⟨site, belongs, expression, binder, span, issued⟩ := ih original index member
      exact ⟨site, List.mem_cons_of_mem _ belongs, expression, binder, span, issued⟩

theorem ReadRetokening.length {first : Nat} {pairs : List (SourceCoreFaultSites.ReadSite × Nat)}
    {reads : List SourceCoreFaultSites.ReadSite} (receipt : ReadRetokening first pairs reads) :
    reads.length = pairs.length := by
  induction receipt with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private theorem program_word_value {number : Nat} {word : Core.Word}
    (accepted : Core.Word.ofNat? number = some word) : word.val = number := by
  unfold Core.Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

/-- Checked program read tokens occupy exactly their genuine input interval. -/
theorem ReadRetokening.bounds {first : Nat} {original reads : List SourceCoreFaultSites.ReadSite}
    (receipt : ReadRetokening first original.zipIdx reads) :
    ∀ site ∈ reads, first ≤ site.reason.val ∧ site.reason.val < first + reads.length := by
  intro site member
  obtain ⟨before, index, belongs, _expression, _binder, _span, issued⟩ := receipt.origin site member
  have bound := List.snd_lt_of_mem_zipIdx belongs
  have number := program_word_value issued
  have count : reads.length = original.length := by simpa only [List.length_zipIdx] using receipt.length
  simp only [Nat.add_zero] at bound
  omega

/-- An actual selected function retains its precise row and allocated start. -/
theorem ProgramIssuance.member {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) :
    ∀ own ∈ functions, ∃ row ∈ rows, ∃ start, first ≤ start ∧ FunctionIssuance start row own := by
  induction receipt with
  | nil => intro own member; simp at member
  | @cons first row rows own functions issued remaining ih =>
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨row, List.mem_cons_self, first, Nat.le_refl _, issued⟩
    · obtain ⟨row, belongs, start, bound, issued⟩ := ih selected member
      exact ⟨row, List.mem_cons_of_mem _ belongs, start, by omega, issued⟩

/-- The original program preparation retains its actual ordered rows, selected
root, full read inventory and exact boundary diagnostics. -/
theorem prepare_issuance {plan : Plan} {root : Key} {diagnostics : Program}
    (accepted : prepare plan root = .ok diagnostics) :
    ∃ selected,
      ProgramIssuance 1 plan.specializations diagnostics.functions ∧
      diagnostics.functions.find? (fun function => decide (function.key = root)) = some selected ∧
      diagnostics.rootTable = { selected.table with
        reads := diagnostics.functions.flatMap (·.table.reads)
        additional := diagnostics.functions.flatMap (fun function => function.assignments.diagnostics ++ [
          (function.fellThroughReason, {
            error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
            site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
            span := none }),
          (function.table.escapedReason, {
            error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
            site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
            span := none })]) } := by
  unfold prepare at accepted
  obtain ⟨functions, collected, accepted⟩ := bind_ok accepted
  split at accepted
  · next selected found =>
    obtain ⟨actualSelected, same, accepted⟩ := bind_ok accepted
    cases same
    cases accepted
    exact ⟨selected, collect_issuance collected, found, rfl⟩
  · simp [bind, Except.bind] at accepted

/-- Canonical specialization selection exposes its original read preparation
and checked program retokening, rather than recovering Source from native code. -/
theorem prepare_function_issuance {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own) :
    ∃ first, 0 < first ∧ FunctionIssuance first row own := by
  obtain ⟨_selected, collection, _found, _table⟩ := prepare_issuance accepted
  have member : own ∈ diagnostics.functions := List.mem_of_find?_eq_some found
  have foundKey : own.key = key := of_decide_eq_true
    (List.find?_some (p := fun candidate : Function => decide (candidate.key = key)) found)
  obtain ⟨candidate, belongs, first, positive, issued⟩ := collection.member own member
  have sameKey : candidate.key = key := by cases issued with | intro same _ _ _ _ _ _ _ _ _ => exact same.symm.trans foundKey
  have same := exact_member record belongs sameKey
  subst candidate
  exact ⟨first, by omega, issued⟩

/-- Distinct original indices give distinct checked read reasons. -/
theorem ReadRetokening.unique_reasons {first : Nat} {original reads : List SourceCoreFaultSites.ReadSite}
    (receipt : ReadRetokening first original.zipIdx reads) :
    ∀ left ∈ reads, ∀ right ∈ reads, left.reason = right.reason → left = right := by
  intro left leftMember right rightMember same
  obtain ⟨beforeLeft, leftIndex, leftPair, leftExpression, leftBinder, leftSpan, leftIssued⟩ := receipt.origin left leftMember
  obtain ⟨beforeRight, rightIndex, rightPair, rightExpression, rightBinder, rightSpan, rightIssued⟩ := receipt.origin right rightMember
  have leftNumber := program_word_value leftIssued
  have rightNumber := program_word_value rightIssued
  have equal := congrArg Fin.val same
  have indices : leftIndex = rightIndex := by omega
  subst rightIndex
  have originals : beforeLeft = beforeRight := Option.some.inj
    ((List.mk_mem_zipIdx_iff_getElem?.mp leftPair).symm.trans (List.mk_mem_zipIdx_iff_getElem?.mp rightPair))
  subst beforeRight
  have expression := leftExpression.trans rightExpression.symm
  have binder := leftBinder.trans rightBinder.symm
  have span := leftSpan.trans rightSpan.symm
  cases left
  cases right
  dsimp only at expression binder span same
  cases expression
  cases binder
  cases span
  cases same
  rfl

private def boundaries (function : Function) : List (Core.Word × SourceCoreFaultSites.Diagnostic) :=
  function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none })]

private theorem FunctionIssuance.ranges {first : Nat} {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (receipt : FunctionIssuance first row own) :
    (∀ site ∈ own.table.reads, first ≤ site.reason.val ∧ site.reason.val < first + own.table.reads.length) ∧
    (∀ pair ∈ boundaries own, first + own.table.reads.length ≤ pair.1.val ∧
      pair.1.val < first + own.table.reads.length + own.assignments.length + 2) ∧
    (∀ left ∈ own.table.reads, ∀ right ∈ own.table.reads, left.reason = right.reason → left = right) := by
  cases receipt with
  | intro _ _ _ reads assignments fell escaped _ _ _ =>
    refine ⟨reads.bounds, ?_, reads.unique_reasons⟩
    intro pair member
    have assigned := (SourceCoreAssignmentFaultSites.prepare_token_range assignments).2.1
    have fellNumber := program_word_value fell
    have escapedNumber := program_word_value escaped
    rcases List.mem_append.mp member with member | member
    · have bounds := assigned pair member; exact ⟨bounds.1, by omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> dsimp only <;> omega

private structure ProgramReadInventory (first : Nat) (functions : List Function) : Prop where
  readsBelow : ∀ site ∈ functions.flatMap (·.table.reads), first ≤ site.reason.val
  boundariesBelow : ∀ pair ∈ functions.flatMap boundaries, first ≤ pair.1.val
  unique : ∀ left ∈ functions.flatMap (·.table.reads), ∀ right ∈ functions.flatMap (·.table.reads),
    left.reason = right.reason → left = right
  separate : ∀ site ∈ functions.flatMap (·.table.reads), ∀ pair ∈ functions.flatMap boundaries,
    site.reason ≠ pair.1

private theorem ProgramIssuance.inventory {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) : ProgramReadInventory first functions := by
  induction receipt with
  | nil => constructor <;> simp
  | @cons first row rows own functions issued remaining ih =>
    obtain ⟨ownReads, ownBoundaries, ownUnique⟩ := issued.ranges
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro site member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact (ownReads site member).1
      · have bound := ih.readsBelow site member; omega
    · intro pair member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · have bound := ownBoundaries pair member; omega
      · have bound := ih.boundariesBelow pair member; omega
    · intro left leftMember right rightMember same
      simp only [List.flatMap_cons, List.mem_append] at leftMember rightMember
      rcases leftMember with leftMember | leftMember
      · rcases rightMember with rightMember | rightMember
        · exact ownUnique left leftMember right rightMember same
        · have leftBound := ownReads left leftMember
          have rightBound := ih.readsBelow right rightMember
          have equal := congrArg Fin.val same; omega
      · rcases rightMember with rightMember | rightMember
        · have rightBound := ownReads right rightMember
          have leftBound := ih.readsBelow left leftMember
          have equal := congrArg Fin.val same; omega
        · exact ih.unique left leftMember right rightMember same
    · intro site siteMember pair pairMember same
      simp only [List.flatMap_cons, List.mem_append] at siteMember pairMember
      rcases siteMember with siteMember | siteMember
      · have readBound := ownReads site siteMember
        rcases pairMember with pairMember | pairMember
        · have bound := ownBoundaries pair pairMember
          have equal := congrArg Fin.val same; omega
        · have bound := ih.boundariesBelow pair pairMember
          have equal := congrArg Fin.val same; omega
      · have readBound := ih.readsBelow site siteMember
        rcases pairMember with pairMember | pairMember
        · have bound := ownBoundaries pair pairMember
          have equal := congrArg Fin.val same; omega
        · exact ih.separate site siteMember pair pairMember same

private theorem program_find_read_unique {α : Type} [DecidableEq α]
    {sites : List SourceCoreFaultSites.ReadSite} {site : SourceCoreFaultSites.ReadSite}
    (key : SourceCoreFaultSites.ReadSite → α) (member : site ∈ sites)
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

/-- Actual program preparation prevents every read token from being shadowed
by another read, assignment, function fallthrough or escaped-control row. -/
theorem prepare_read_diagnostic {plan : Plan} {root : Key} {diagnostics : Program}
    (accepted : prepare plan root = .ok diagnostics)
    {site : SourceCoreFaultSites.ReadSite} (member : site ∈ diagnostics.rootTable.reads) :
    site.reason ≠ Core.Word.zero ∧ site.reason ≠ diagnostics.rootTable.escapedReason ∧
    diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none ∧
    diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site ∧
    diagnostics.rootTable.diagnostic? site.reason = some {
      error := SourceTypedRuntime.RuntimeError.uninitializedLocal site.binder
      site := SourceCoreElaboration.ErrorSite.occurrence site.expression.occurrence
      span := some site.span } := by
  obtain ⟨selected, collection, found, table⟩ := prepare_issuance accepted
  have reads : diagnostics.rootTable.reads = diagnostics.functions.flatMap (·.table.reads) := congrArg (·.reads) table
  have additional : diagnostics.rootTable.additional = diagnostics.functions.flatMap boundaries := congrArg (·.additional) table
  have escaped : diagnostics.rootTable.escapedReason = selected.table.escapedReason := congrArg (·.escapedReason) table
  have inventory := collection.inventory
  have belongs : site ∈ diagnostics.functions.flatMap (·.table.reads) := reads ▸ member
  have positive : site.reason ≠ Core.Word.zero := by
    intro same
    have bound := inventory.readsBelow site belongs
    have number := congrArg Fin.val same
    change site.reason.val = 0 at number
    omega
  have selectedMember : selected ∈ diagnostics.functions := List.mem_of_find?_eq_some found
  have escapedMember : (selected.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration selected.table.owner
      span := none }) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨selected, selectedMember, by simp [boundaries]⟩
  have ordinary : site.reason ≠ diagnostics.rootTable.escapedReason := by
    rw [escaped]
    exact inventory.separate site belongs _ escapedMember
  have noAdditional : diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none := by
    rw [additional]
    simp only [List.find?_eq_none]
    intro candidate candidateMember same
    exact inventory.separate site belongs candidate candidateMember (of_decide_eq_true same).symm
  have byReason : diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site :=
    program_find_read_unique (·.reason) member (fun candidate candidateMember same =>
      inventory.unique candidate (reads ▸ candidateMember) site belongs same)
  exact ⟨positive, ordinary, noAdditional, byReason,
    SourceCoreFaultSites.Table.read_diagnostic positive ordinary noAdditional byReason⟩

/-- A genuine Source local-read occurrence selects its actual globally
retokened row and restores the same binder, occurrence and span. -/
theorem prepare_local_read {plan : Plan} {root key : Key} {diagnostics : Program}
    {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (accepted : prepare plan root = .ok diagnostics)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row)
    (found : diagnostics.find? key = some own)
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (member : .expression node ∈ row.function.typedBody.nodes)
    (form : node.form = .reference name (.local binder)) :
    ∃ site,
      own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) = some site ∧
      site.expression = node.id ∧ site.binder = binder ∧ site.span = node.span ∧
      own.table.reasonAt node.id = site.reason ∧
      site ∈ diagnostics.rootTable.reads ∧
      site.reason ≠ Core.Word.zero ∧ site.reason ≠ diagnostics.rootTable.escapedReason ∧
      diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = site.reason)) = none ∧
      diagnostics.rootTable.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site ∧
      diagnostics.rootTable.diagnostic? site.reason = some {
        error := SourceTypedRuntime.RuntimeError.uninitializedLocal binder
        site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
        span := some node.span } := by
  obtain ⟨first, _positive, issuance⟩ := prepare_function_issuance accepted record found
  cases issuance with
  | @intro parameter result base _key _functionType prepared retokened _assignments _fell _escaped _owner _result _additional =>
    obtain ⟨original, originalFound, originalExpression, originalBinder, originalSpan, _reason, _positive, _ordinary, _byReason, _diagnostic⟩ :=
      SourceCoreFaultSites.prepare_local_read prepared member form
    have originalMember : original ∈ base.reads := List.mem_of_find?_eq_some originalFound
    have zipped : original ∈ base.reads.zipIdx.map Prod.fst := by
      rw [List.zipIdx_map_fst]; exact originalMember
    obtain ⟨pair, pairMember, pairEq⟩ := List.mem_map.mp zipped
    rcases pair with ⟨before, index⟩
    dsimp only at pairEq
    subst before
    obtain ⟨reached, reachedMember, reachedExpression, _binder, _span, _issued⟩ := retokened.covers original index pairMember
    have existsFound : ∃ site, own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) = some site := by
      cases selected : own.table.reads.find? (fun candidate => decide (candidate.expression = node.id)) with
      | some site => exact ⟨site, rfl⟩
      | none =>
        have absent := List.find?_eq_none.mp selected reached reachedMember
        exact (absent (by simp only [reachedExpression, originalExpression, decide_true])).elim
    obtain ⟨site, selected⟩ := existsFound
    have selectedMember : site ∈ own.table.reads := List.mem_of_find?_eq_some selected
    have expression : site.expression = node.id := of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreFaultSites.ReadSite => decide (candidate.expression = node.id)) selected)
    obtain ⟨before, index, belongs, beforeExpression, beforeBinder, beforeSpan, _issued⟩ := retokened.origin site selectedMember
    have beforeMember := List.fst_mem_of_mem_zipIdx belongs
    have same : before = original := SourceCoreFaultSites.prepare_read_occurrences_unique prepared
      before beforeMember original originalMember (beforeExpression.symm.trans (expression.trans originalExpression.symm))
    subst before
    have binderEq := beforeBinder.trans originalBinder
    have spanEq := beforeSpan.trans originalSpan
    obtain ⟨_root, _collection, _selectedRoot, table⟩ := prepare_issuance accepted
    have ownMember : own ∈ diagnostics.functions := List.mem_of_find?_eq_some found
    have reads : diagnostics.rootTable.reads = diagnostics.functions.flatMap (·.table.reads) := congrArg (·.reads) table
    have rootMember : site ∈ diagnostics.rootTable.reads := by
      rw [reads]; exact List.mem_flatMap.mpr ⟨own, ownMember, selectedMember⟩
    obtain ⟨positive, ordinary, noAdditional, byReason, diagnostic⟩ := prepare_read_diagnostic accepted rootMember
    refine ⟨site, selected, expression, binderEq, spanEq, ?_, rootMember, positive, ordinary, noAdditional, byReason, ?_⟩
    · unfold SourceCoreFaultSites.Table.reasonAt; rw [selected]
    · simpa only [expression, binderEq, spanEq] using diagnostic

end Solcore.Frontend.SourceCoreProgramFaultSites
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataFaultSites
/-! Missing mapping defaults have distinct program-wide tokens. This metadata
pass preserves the current public error (`typeMismatch valueType none`) and
the exact expression occurrence and span. It performs no source evaluation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataFaultSites

open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure IndexSite where
  owner : Key
  expression : ExpressionId
  reason : Core.Word
  diagnostic : SourceCoreFaultSites.Diagnostic
  deriving Repr, DecidableEq

structure Program where
  base : SourceCoreProgramFaultSites.Program
  indices : List IndexSite
  rootTable : SourceCoreFaultSites.Table
  deriving Repr

inductive Error where
  | base (error : SourceCoreProgramFaultSites.Error)
  | reasonSpaceExhausted
  | ownerMismatch (expression : ExpressionId)
  | duplicateOccurrence (expression : ExpressionId)
  deriving Repr, DecidableEq

def prepare (plan : Plan) (root : Key) : Except Error Program := do
  let base ← (SourceCoreProgramFaultSites.prepare plan root).mapError Error.base
  let used := base.rootTable.reads.map (·.reason.val) ++
    base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val]
  let start := used.foldl max 0 + 1
  let mut indices : List IndexSite := []
  for specialized in plan.specializations do
    for node in specialized.function.typedBody.nodes do
      match node with
      | .expression node =>
          match node.form with
          | .index _ _ =>
              if node.id.occurrence.owner ≠ specialized.function.typedBody.owner then
                throw (.ownerMismatch node.id)
              if indices.any (fun entry => decide (entry.owner = specialized.key ∧ entry.expression = node.id)) then
                throw (.duplicateOccurrence node.id)
              let reason ← match Core.Word.ofNat? (start + indices.length) with
                | some reason => pure reason
                | none => throw .reasonSpaceExhausted
              let diagnostic : SourceCoreFaultSites.Diagnostic := {
                error := .typeMismatch node.type none
                site := .occurrence node.id.occurrence
                span := some node.span
              }
              indices := indices ++ [⟨specialized.key, node.id, reason, diagnostic⟩]
          | _ => pure ()
      | _ => pure ()
  let rootTable := { base.rootTable with
    additional := base.rootTable.additional ++ indices.map (fun site => (site.reason, site.diagnostic)) }
  pure { base, indices, rootTable }

def Program.reasonAt (program : Program) (owner : Key) (id : ExpressionId) : Core.Word :=
  match program.indices.find? (fun site => decide (site.owner = owner ∧ site.expression = id)) with
  | some site => site.reason
  | none => match program.base.find? owner with
      | some function => function.table.reasonAt id
      | none => Core.Word.zero

end Solcore.Frontend.SourceCoreDataFaultSites
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreRuntimeFaultSites
/-! Assemble single-function read, assignment and boundary diagnostics without
introducing an import cycle in the ordinary read-site table. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRuntimeFaultSites

structure Prepared where
  table : SourceCoreFaultSites.Table
  assignments : SourceCoreAssignmentFaultSites.Table
  deriving Repr

inductive Error where
  | sites (error : SourceCoreFaultSites.Error)
  | assignments (error : SourceCoreAssignmentFaultSites.Error)
  deriving Repr, DecidableEq

def prepare (source : SourceInference.TypedSource) (resultType : TypeSystem.Ty) : Except Error Prepared := do
  let table ← (SourceCoreFaultSites.prepare source resultType).mapError Error.sites
  let assignments ← (SourceCoreAssignmentFaultSites.prepare source (table.reads.length + 2)).mapError Error.assignments
  pure { table := { table with additional := assignments.diagnostics }, assignments }

end Solcore.Frontend.SourceCoreRuntimeFaultSites
end
