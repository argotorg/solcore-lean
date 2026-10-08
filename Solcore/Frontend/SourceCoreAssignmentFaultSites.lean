import Solcore.Frontend.SourceCoreFaultSites

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
