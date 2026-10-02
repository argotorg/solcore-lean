import Solcore.Frontend.SourceCoreAssignmentFaultSites

/-! Certificates for the actual diagnostic-table fold. A repeated key retains
its first complete entry. Raw target eligibility is explicit; normalized type
equality cannot supply it. A retained entry need not have the metadata of a
later same-key occurrence. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAssignmentFaultSites.Certificates
open SourceInference Core

abbrev Matches (location : SourceCoreElaboration.ErrorSite) (binder : Resolved.LocalId) (kind : Kind) (site : Site) : Bool :=
  decide (site.site = location ∧ site.binder = binder ∧ site.kind = kind)

def Numbered (first : Nat) (sites : List Site) : Prop :=
  ∀ index site, sites[index]? = some site → site.reason.val = first + index

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem find_append {sites suffix : List Site} {test : Site → Bool} {site : Site}
    (found : sites.find? test = some site) : (sites ++ suffix).find? test = some site := by
  simp only [List.find?_append, found, Option.or]

private theorem add_shape {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (accepted : add owner first sites location span assignment kind = .ok next) :
    next = sites ∨ ∃ reason,
      Word.ofNat? (first + sites.length) = some reason ∧
      next = sites ++ [{site := location, binder := assignment.target.root, kind := kind, span := span, reason := reason, rhsType := assignment.target.type}] := by
  by_cases owned : assignment.target.root.owner = owner
  · simp only [add, owned, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · exact .inl (Except.ok.inj accepted).symm
    · split at accepted
      · exact .inl (Except.ok.inj accepted).symm
      · split at accepted
        · rename_i reason generated
          exact .inr ⟨reason, generated, (Except.ok.inj accepted).symm⟩
        · cases accepted
  · simp [add, owned, throw, bind, Except.bind] at accepted

theorem add_preserves_found {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind} {test : Site → Bool} {site : Site}
    (accepted : add owner first sites location span assignment kind = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  rcases add_shape accepted with rfl | ⟨reason, _, rfl⟩
  · exact found
  · exact find_append found

theorem add_lookup {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer)
    (accepted : add owner first sites location span assignment kind = .ok next) :
    ∃ site, next.find? (Matches location assignment.target.root kind) = some site := by
  by_cases owned : assignment.target.root.owner = owner
  · have eligible : ¬ (assignment.target.type ≠ .word ∧ assignment.target.type ≠ .integer) := by
      intro excluded
      exact rawScalar.elim excluded.1 excluded.2
    simp only [add, owned, ne_eq, not_true_eq_false, eligible, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · rename_i present
      obtain ⟨site, member, matched⟩ := List.any_eq_true.mp present
      have hasEntry := (List.find?_isSome (p := Matches location assignment.target.root kind)).mpr ⟨site, member, matched⟩
      cases found : sites.find? (Matches location assignment.target.root kind) with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at hasEntry
      | some result => exact ⟨result, Except.ok.inj accepted ▸ found⟩
    · split at accepted
      · rename_i reason generated
        have nextEq := (Except.ok.inj accepted).symm
        subst next
        cases found : sites.find? (Matches location assignment.target.root kind) with
        | none => exact ⟨{site := location, binder := assignment.target.root, kind := kind, span := span, reason := reason, rhsType := assignment.target.type}, by simp [List.find?_append, found, Matches]⟩
        | some site => exact ⟨site, find_append found⟩
      · cases accepted
  · simp [add, owned, throw, bind, Except.bind] at accepted

private theorem numbered_append {first : Nat} {sites : List Site} {site : Site}
    (numbered : Numbered first sites) (reason : site.reason.val = first + sites.length) :
    Numbered first (sites ++ [site]) := by
  intro index entry found
  by_cases before : index < sites.length
  · have previous : sites[index]? = some entry := by simpa only [List.getElem?_append, before, ↓reduceIte] using found
    exact numbered index entry previous
  · have suffix : [site][index - sites.length]? = some entry := by
      simpa only [List.getElem?_append, before, ↓reduceIte] using found
    have valid : index - sites.length < 1 := by simpa using (List.getElem?_eq_some_iff.mp suffix).1
    have same : index = sites.length := by omega
    subst index
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at suffix
    exact suffix ▸ reason

theorem add_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {assignment : AssignmentResolution} {kind : Kind}
    (numbered : Numbered first sites)
    (accepted : add owner first sites location span assignment kind = .ok next) : Numbered first next := by
  rcases add_shape accepted with rfl | ⟨reason, generated, rfl⟩
  · exact numbered
  · apply numbered_append numbered
    unfold Word.ofNat? at generated
    split at generated
    · cases generated; rfl
    · cases generated

private theorem fold_invariant {α : Type} {step : List Site → α → Except Error (List Site)}
    {property : List Site → Prop}
    (each : ∀ sites item next, property sites → step sites item = .ok next → property next)
    {items : List α} {sites next : List Site} (initial : property sites)
    (accepted : items.foldlM step sites = .ok next) : property next := by
  induction items generalizing sites with
  | nil => exact Except.ok.inj accepted ▸ initial
  | cons item rest ih =>
    obtain ⟨middle, first, remaining⟩ := bind_ok accepted
    exact ih (each sites item middle initial first) remaining

private theorem fold_contains {α : Type} {step : List Site → α → Except Error (List Site)}
    {property : List Site → Prop}
    (preserve : ∀ sites item next, property sites → step sites item = .ok next → property next)
    {items : List α} {selected : α}
    (obtains : ∀ sites next, step sites selected = .ok next → property next)
    (member : selected ∈ items) {sites next : List Site}
    (accepted : items.foldlM step sites = .ok next) : property next := by
  induction items generalizing sites with
  | nil => cases member
  | cons item rest ih =>
    obtain ⟨middle, first, remaining⟩ := bind_ok accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact fold_invariant preserve (obtains _ _ first) remaining
    · exact ih member remaining

private theorem item_preserves {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan} {item : ForItemForm}
    {test : Site → Bool} {site : Site}
    (accepted : addItem owner first location span sites item = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  cases item with
  | letDecl | expression => exact Except.ok.inj accepted ▸ found
  | assignBitNot => exact add_preserves_found accepted found
  | assignValue assignment operator rhs =>
    simp only [addItem] at accepted
    split at accepted
    · exact Except.ok.inj accepted ▸ found
    · exact add_preserves_found accepted found

private theorem item_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan} {item : ForItemForm}
    (numbered : Numbered first sites)
    (accepted : addItem owner first location span sites item = .ok next) : Numbered first next := by
  cases item with
  | letDecl | expression => exact Except.ok.inj accepted ▸ numbered
  | assignBitNot => exact add_numbered numbered accepted
  | assignValue assignment operator rhs =>
    simp only [addItem] at accepted
    split at accepted
    · exact Except.ok.inj accepted ▸ numbered
    · exact add_numbered numbered accepted

private theorem statement_preserves {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} {test : Site → Bool} {site : Site}
    (accepted : addStatement owner first sites node = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases form : node.form <;> simp only [form] at accepted
    all_goals first | exact Except.ok.inj accepted ▸ found | exact add_preserves_found accepted found | skip
    · split at accepted
      · exact Except.ok.inj accepted ▸ found
      · exact add_preserves_found accepted found
    · exact fold_invariant (fun _ _ _ previous step => item_preserves step previous) found accepted

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

private theorem statement_numbered {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} (numbered : Numbered first sites)
    (accepted : addStatement owner first sites node = .ok next) : Numbered first next := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases form : node.form <;> simp only [form] at accepted
    all_goals first | exact Except.ok.inj accepted ▸ numbered | exact add_numbered numbered accepted | skip
    · split at accepted
      · exact Except.ok.inj accepted ▸ numbered
      · exact add_numbered numbered accepted
    · exact fold_invariant (fun _ _ _ previous step => item_numbered previous step) numbered accepted

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

/-- An operand operation at a statement or inside either ordered for header. -/
inductive OperandAt (node : StatementNode) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) : Prop where
  | statement {rhs} : node.form = .assignValue assignment operator rhs → OperandAt node assignment operator
  | header {initializer condition post body rhs} : node.form = .forLoop initializer condition post body →
      .assignValue assignment operator rhs ∈ initializer ++ post → OperandAt node assignment operator

private theorem statement_lookup {owner : Resolved.DeclarationId} {first : Nat} {sites next : List Site}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer)
    (accepted : addStatement owner first sites node = .ok next) :
    ∃ site, next.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site := by
  by_cases owned : node.id.occurrence.owner = owner
  · simp only [addStatement, owned, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at accepted
    cases occurs with
    | statement form =>
      simp only [form, different, ↓reduceIte] at accepted
      exact add_lookup rawScalar accepted
    | header form member =>
      simp only [form] at accepted
      apply fold_contains (selected := ForItemForm.assignValue assignment operator _) (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site) ?_ ?_ member accepted
      · intro sites item next ⟨site, found⟩ step
        exact ⟨site, item_preserves step found⟩
      · intro sites next step
        simp only [addItem, different, ↓reduceIte] at step
        exact add_lookup rawScalar step

  · simp [addStatement, owned, throw, bind, Except.bind] at accepted

/-- The production fold enumerates successful insertions without wrapping. -/
theorem prepare_numbered {source : TypedSource} {first : Nat} {table : Table}
    (accepted : prepare source first = .ok table) : Numbered first table.sites := by
  unfold prepare at accepted
  obtain ⟨sites, folded, returned⟩ := bind_ok accepted
  cases returned
  exact fold_invariant (fun _ _ _ previous step => statement_numbered previous step)
    (by intro index site found; cases found) folded

/-- Actual eligible occurrences have a lookup after the complete ordered fold.
The result keeps the first entry's metadata, including across header repeats. -/
theorem prepare_lookup {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (accepted : prepare source first = .ok table)
    (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer) :
    ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site := by
  unfold prepare at accepted
  obtain ⟨sites, folded, returned⟩ := bind_ok accepted
  cases returned
  apply fold_contains (selected := node) (property := fun sites => ∃ site, sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site) ?_ ?_ ?_ folded
  · intro sites item next ⟨site, found⟩ step
    exact ⟨site, statement_preserves step found⟩
  · intro sites next step
    exact statement_lookup occurs different rawScalar step
  · apply List.mem_mergeSort.mpr
    exact List.mem_filterMap.mpr ⟨.statement node, member, rfl⟩

/-- A successful later header fold preserves the exact first record, including
its span and raw RHS type, even if a later request reuses the lookup key. -/
theorem items_preserve_found {owner : Resolved.DeclarationId} {first : Nat}
    {location : SourceCoreElaboration.ErrorSite} {span : Syntax.SourceSpan}
    {items : List ForItemForm} {sites next : List Site} {test : Site → Bool} {site : Site}
    (accepted : items.foldlM (addItem owner first location span) sites = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site :=
  fold_invariant (fun _ _ _ previous step => item_preserves step previous) found accepted

theorem statements_preserve_found {owner : Resolved.DeclarationId} {first : Nat}
    {nodes : List StatementNode} {sites next : List Site} {test : Site → Bool} {site : Site}
    (accepted : nodes.foldlM (addStatement owner first) sites = .ok next)
    (found : sites.find? test = some site) : next.find? test = some site :=
  fold_invariant (fun _ _ _ previous step => statement_preserves step previous) found accepted

theorem Numbered.reason_unique {first : Nat} {sites : List Site}
    (numbered : Numbered first sites) {left right : Site}
    (leftMem : left ∈ sites) (rightMem : right ∈ sites) (same : left.reason = right.reason) : left = right := by
  obtain ⟨i, leftFound⟩ := List.mem_iff_getElem?.mp leftMem
  obtain ⟨j, rightFound⟩ := List.mem_iff_getElem?.mp rightMem
  have leftIndex := numbered i left leftFound
  have rightIndex := numbered j right rightFound
  have indexEq : i = j := by rw [same] at leftIndex; omega
  subst j
  exact Option.some.inj (leftFound.symm.trans rightFound)

theorem Numbered.diagnostic {first : Nat} {table : Table} {site : Site}
    (numbered : Numbered first table.sites) (member : site ∈ table.sites) :
    table.diagnostic? site.reason = some site.diagnostic := by
  have existsEntry := (List.find?_isSome (p := fun candidate : Site => decide (candidate.reason = site.reason))).mpr
    ⟨site, member, by simp⟩
  cases found : table.sites.find? (fun candidate => decide (candidate.reason = site.reason)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at existsEntry
  | some entry =>
    have same : entry.reason = site.reason := by simpa using List.find?_some found
    have identical := numbered.reason_unique (List.mem_of_find?_eq_some found) member same
    subst entry
    exact Table.diagnostic_found found

/-- Lookup and diagnostic decoding agree on the actual first eligible entry.
No equality with a later occurrence's raw metadata is inferred. -/
theorem prepare_operand {source : TypedSource} {first : Nat} {table : Table}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    (accepted : prepare source first = .ok table) (member : Node.statement node ∈ source.nodes)
    (occurs : OperandAt node assignment operator) (different : operator ≠ .equal)
    (rawScalar : assignment.target.type = .word ∨ assignment.target.type = .integer) :
    ∃ site, table.sites.find? (Matches (.occurrence node.id.occurrence) assignment.target.root (.value operator)) = some site ∧
      site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .value operator ∧
      table.reasonAt (.occurrence node.id.occurrence) assignment.target.root (.value operator) = site.reason ∧
      table.diagnostic? site.reason = some site.diagnostic := by
  obtain ⟨site, found⟩ := prepare_lookup accepted member occurs different rawScalar
  have matched : site.site = .occurrence node.id.occurrence ∧ site.binder = assignment.target.root ∧ site.kind = .value operator :=
    by simpa [Matches] using List.find?_some found
  exact ⟨site, found, matched.1, matched.2.1, matched.2.2,
    Table.reasonAt_found found, (prepare_numbered accepted).diagnostic (List.mem_of_find?_eq_some found)⟩

end Solcore.Frontend.SourceCoreAssignmentFaultSites.Certificates
