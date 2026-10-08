import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexSourceReceipts

/-! Actual expression and place suffixes retain their literal missing rows.
Ownership uses the checked fresh reason and the real selected key; Source views
and receiving metadata remain independent query receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMissingSourceReceipts
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaceFaultSites
abbrev Key := SourceSpecialization.SpecializationKey
abbrev IndexSite := SourceCoreDataFaultSites.IndexSite
abbrev PlaceSite := SourceCoreDataPlaceFaultSites.Site

/-- This is the accepted expression suffix at its actual Source node. -/
def ExpressionAt (indices : List IndexSite) (owner : Key) (source : TypedSource)
    (node : ExpressionNode) (row : MissingSite) : Prop :=
  ∃ mapping key baseNode keyType valueType selected,
    node.form = .index mapping key ∧ source.lookupExpression? mapping = some baseNode ∧
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping keyType valueType ∧
    SourceCoreRawMetadata.runtimeType node.type = valueType ∧
    indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected ∧
    row = ⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, selected.reason⟩

/-- The actual place and key lookup fix the appended route row. -/
def PlaceAt (places : List PlaceSite) (owner : Key) (source : TypedSource)
    (node : StatementNode) (assignment : AssignmentResolution) (row : MissingSite) : Prop :=
  ∃ place key keyNode valueType,
    place ∈ places ∧ place.owner = owner ∧ place.location = .occurrence node.id.occurrence ∧
    place.binder = assignment.target.root ∧ place.missingType = some valueType ∧
    source.lookupExpression? key = some keyNode ∧
    row = ⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
      keyNode.type, valueType, node.span, place.reason⟩

def Origin (sources : List (Key × TypedSource)) (indices : List IndexSite)
    (places : List PlaceSite) (row : MissingSite) : Prop :=
  (∃ owner source node, (owner, source) ∈ sources ∧ source.owner = owner.declaration ∧
    SourceSemantics.ContainsExpression source node.id node ∧ ExpressionAt indices owner source node row) ∨
  (∃ owner source node assignment, (owner, source) ∈ sources ∧ source.owner = owner.declaration ∧
    SourceSemantics.ContainsStatement source node.id node ∧ PlaceAt places owner source node assignment row)

structure Ownership (indices : List IndexSite) (places : List PlaceSite) : Prop where
  index : ∀ left, left ∈ indices → ∀ right, right ∈ indices → left.reason = right.reason →
    left.owner = right.owner ∧ left.expression = right.expression
  separate : ∀ index, index ∈ indices → ∀ place, place ∈ places →
    ∀ type, place.missingType = some type → index.reason ≠ place.reason

def NodesCovered (owner : Key) (source : TypedSource) (nodes : List Node)
    (indices : List IndexSite) (missing : List MissingSite) : Prop :=
  ∀ node, Node.expression node ∈ nodes → ∀ mapping key, node.form = .index mapping key →
    ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row

def SourcesCovered (sources : List (Key × TypedSource)) (indices : List IndexSite)
    (missing : List MissingSite) : Prop :=
  ∀ owner source, (owner, source) ∈ sources → NodesCovered owner source source.nodes indices missing

structure Inventory (sources visited : List (Key × TypedSource)) (indices : List IndexSite)
    (places : List PlaceSite) (missing : List MissingSite) : Prop where
  origins : ∀ row, row ∈ missing → Origin sources indices places row
  ownership : Ownership indices places
  covered : SourcesCovered visited indices missing

structure NodeInventory (sources visited : List (Key × TypedSource)) (owner : Key)
    (source : TypedSource) (seen : List Node) (indices : List IndexSite)
    (places : List PlaceSite) (missing : List MissingSite) : Prop where
  inventory : Inventory sources visited indices places missing
  covered : NodesCovered owner source seen indices missing

/-- Route changes are independent of any global Source inventory. -/
structure RouteChanges (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (start : Nat) (beforePlaces afterPlaces : List PlaceSite)
    (beforeMissing afterMissing : List MissingSite) : Prop where
  places : ∃ added, afterPlaces = beforePlaces ++ added ∧
    ∀ place, place ∈ added → start ≤ place.reason.val
  missing : ∃ added, afterMissing = beforeMissing ++ added ∧
    ∀ row, row ∈ added → PlaceAt afterPlaces owner source node assignment row

theorem ExpressionAt.append {indices : List IndexSite} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {row : MissingSite} (receipt : ExpressionAt indices owner source node row)
    (later : List IndexSite) : ExpressionAt (indices ++ later) owner source node row := by
  obtain ⟨mapping, key, base, keyType, valueType, selected, form, found, mappingView, valueView, chosen, same⟩ := receipt
  exact ⟨mapping, key, base, keyType, valueType, selected, form, found, mappingView, valueView,
    by simp only [List.find?_append, chosen]; rfl, same⟩

theorem PlaceAt.mono {places later : List PlaceSite} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {row : MissingSite}
    (receipt : PlaceAt places owner source node assignment row)
    (includes : ∀ place, place ∈ places → place ∈ later) : PlaceAt later owner source node assignment row := by
  obtain ⟨place, key, keyNode, valueType, member, owns, location, binder, kind, found, same⟩ := receipt
  exact ⟨place, key, keyNode, valueType, includes place member, owns, location, binder, kind, found, same⟩

theorem Origin.mono {sources : List (Key × TypedSource)} {indices : List IndexSite}
    {places laterPlaces : List PlaceSite} {row : MissingSite}
    (origin : Origin sources indices places row) (laterIndices : List IndexSite)
    (includes : ∀ place, place ∈ places → place ∈ laterPlaces) :
    Origin sources (indices ++ laterIndices) laterPlaces row := by
  rcases origin with ⟨owner, source, node, member, owns, contains, receipt⟩ |
    ⟨owner, source, node, assignment, member, owns, contains, receipt⟩
  · exact .inl ⟨owner, source, node, member, owns, contains, receipt.append laterIndices⟩
  · exact .inr ⟨owner, source, node, assignment, member, owns, contains, receipt.mono includes⟩

theorem NodesCovered.mono {owner : Key} {source : TypedSource} {nodes : List Node}
    {indices : List IndexSite} {missing laterMissing : List MissingSite}
    (covered : NodesCovered owner source nodes indices missing) (laterIndices : List IndexSite)
    (includes : ∀ row, row ∈ missing → row ∈ laterMissing) :
    NodesCovered owner source nodes (indices ++ laterIndices) laterMissing := by
  intro node member mapping key form
  obtain ⟨row, present, receipt⟩ := covered node member mapping key form
  exact ⟨row, includes row present, receipt.append laterIndices⟩

theorem Inventory.empty (sources : List (Key × TypedSource)) : Inventory sources [] [] [] [] := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro item member; cases member
  · intro item member; cases member
  · intro item member; cases member
  · intro owner source member; cases member

theorem Ownership.append_index {indices : List IndexSite} {places : List PlaceSite}
    (ownership : Ownership indices places) (site : IndexSite)
    (freshIndex : ∀ old, old ∈ indices → old.reason ≠ site.reason)
    (freshPlace : ∀ old, old ∈ places → ∀ type, old.missingType = some type → old.reason ≠ site.reason) :
    Ownership (indices ++ [site]) places := by
  refine ⟨?_, ?_⟩
  · intro left leftMember right rightMember same
    rcases List.mem_append.mp leftMember with leftOld | leftNew
    · rcases List.mem_append.mp rightMember with rightOld | rightNew
      · exact ownership.index left leftOld right rightOld same
      · cases List.mem_singleton.mp rightNew
        exact False.elim (freshIndex left leftOld same)
    · cases List.mem_singleton.mp leftNew
      rcases List.mem_append.mp rightMember with rightOld | rightNew
      · exact False.elim (freshIndex right rightOld same.symm)
      · cases List.mem_singleton.mp rightNew
        exact ⟨rfl, rfl⟩
  · intro index member place placeMember type kind same
    rcases List.mem_append.mp member with old | new
    · exact ownership.separate index old place placeMember type kind same
    · cases List.mem_singleton.mp new
      exact freshPlace place placeMember type kind same.symm

theorem Inventory.append_index {sources visited : List (Key × TypedSource)}
    {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (inventory : Inventory sources visited indices places missing) (site : IndexSite)
    (freshIndex : ∀ old, old ∈ indices → old.reason ≠ site.reason)
    (freshPlace : ∀ old, old ∈ places → ∀ type, old.missingType = some type → old.reason ≠ site.reason) :
    Inventory sources visited (indices ++ [site]) places missing := by
  refine ⟨?_, inventory.ownership.append_index site freshIndex freshPlace, ?_⟩
  · intro row member
    exact (inventory.origins row member).mono [site] (fun _ member => member)
  · intro owner source member
    exact (inventory.covered owner source member).mono [site] (fun _ member => member)

theorem Inventory.fixed_place {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    (place : PlaceSite) (kind : place.missingType = none) :
    Inventory sources visited indices (places ++ [place]) missing := by
  refine ⟨?_, ⟨inventory.ownership.index, ?_⟩, inventory.covered⟩
  · intro row member
    simpa only [List.append_nil] using (inventory.origins row member).mono []
      (fun _ member => List.mem_append_left _ member)
  · intro index indexMember current member type currentKind
    rcases List.mem_append.mp member with old | new
    · exact inventory.ownership.separate index indexMember current old type currentKind
    · cases List.mem_singleton.mp new
      rw [kind] at currentKind
      cases currentKind

theorem Inventory.append_expression {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {row : MissingSite}
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node)
    (receipt : ExpressionAt indices owner source node row) :
    Inventory sources visited indices places (missing ++ [row]) := by
  refine ⟨?_, inventory.ownership, ?_⟩
  · intro current currentMember
    rcases List.mem_append.mp currentMember with old | new
    · exact inventory.origins current old
    · cases List.mem_singleton.mp new
      exact .inl ⟨owner, source, node, member, owns, contains, receipt⟩
  · intro owner source member
    simpa only [List.append_nil] using (inventory.covered owner source member).mono []
      (fun _ member => List.mem_append_left _ member)

theorem RouteChanges.refl (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (start : Nat) (places : List PlaceSite) (missing : List MissingSite) :
    RouteChanges owner source node assignment start places places missing missing := by
  refine ⟨⟨[], by simp, ?_⟩, ⟨[], by simp, ?_⟩⟩
  all_goals intro item member; cases member

theorem RouteChanges.trans {owner : Key} {source : TypedSource} {node : StatementNode}
    {assignment : AssignmentResolution} {start middle : Nat} {beforePlaces currentPlaces afterPlaces : List PlaceSite}
    {beforeMissing currentMissing afterMissing : List MissingSite}
    (first : RouteChanges owner source node assignment start beforePlaces currentPlaces beforeMissing currentMissing)
    (second : RouteChanges owner source node assignment middle currentPlaces afterPlaces currentMissing afterMissing)
    (grows : start ≤ middle) :
    RouteChanges owner source node assignment start beforePlaces afterPlaces beforeMissing afterMissing := by
  obtain ⟨firstPlaces, placesEq, placesBound⟩ := first.places
  obtain ⟨laterPlaces, laterEq, laterBound⟩ := second.places
  obtain ⟨firstMissing, missingEq, missingAt⟩ := first.missing
  obtain ⟨laterMissing, laterMissingEq, laterAt⟩ := second.missing
  refine ⟨⟨firstPlaces ++ laterPlaces, by rw [laterEq, placesEq, List.append_assoc], ?_⟩,
    ⟨firstMissing ++ laterMissing, by rw [laterMissingEq, missingEq, List.append_assoc], ?_⟩⟩
  · intro place member
    rcases List.mem_append.mp member with old | new
    · exact placesBound place old
    · exact Nat.le_trans grows (laterBound place new)
  · intro row member
    rcases List.mem_append.mp member with old | new
    · exact (missingAt row old).mono (fun _ member => laterEq ▸ List.mem_append_left _ member)
    · exact laterAt row new

theorem RouteChanges.apply {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {beforePlaces afterPlaces : List PlaceSite} {beforeMissing afterMissing : List MissingSite}
    {owner : Key} {source : TypedSource} {node : StatementNode} {assignment : AssignmentResolution} {start : Nat}
    (changes : RouteChanges owner source node assignment start beforePlaces afterPlaces beforeMissing afterMissing)
    (inventory : Inventory sources visited indices beforePlaces beforeMissing)
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsStatement source node.id node)
    (below : ∀ index, index ∈ indices → index.reason.val < start) :
    Inventory sources visited indices afterPlaces afterMissing := by
  obtain ⟨addedPlaces, placesEq, placesBound⟩ := changes.places
  obtain ⟨addedMissing, missingEq, missingAt⟩ := changes.missing
  refine ⟨?_, ⟨inventory.ownership.index, ?_⟩, ?_⟩
  · intro row rowMember
    rw [missingEq] at rowMember
    rcases List.mem_append.mp rowMember with old | new
    · simpa only [List.append_nil] using (inventory.origins row old).mono []
        (fun _ member => placesEq ▸ List.mem_append_left _ member)
    · exact .inr ⟨owner, source, node, assignment, member, owns, contains, missingAt row new⟩
  · intro index indexMember place placeMember type kind same
    rw [placesEq] at placeMember
    rcases List.mem_append.mp placeMember with old | new
    · exact inventory.ownership.separate index indexMember place old type kind same
    · have oldBound := below index indexMember
      have newBound := placesBound place new
      have number := congrArg Fin.val same
      omega
  · intro owner source member
    simpa only [List.append_nil] using (inventory.covered owner source member).mono []
      (fun _ member => missingEq ▸ List.mem_append_left _ member)

theorem NodeInventory.start {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    (owner : Key) (source : TypedSource) : NodeInventory sources visited owner source [] indices places missing := by
  refine ⟨inventory, ?_⟩
  intro node member; cases member

theorem NodeInventory.step {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {seen : List Node} {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite} {retained : Node}
    (inventory : NodeInventory sources visited owner source seen indices places missing)
    (selected : ∀ node, retained = .expression node → ∀ mapping key, node.form = .index mapping key →
      ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row) :
    NodeInventory sources visited owner source (seen ++ [retained]) indices places missing := by
  refine ⟨inventory.inventory, ?_⟩
  intro node member mapping key form
  rcases List.mem_append.mp member with old | new
  · exact inventory.covered node old mapping key form
  · exact selected node (List.mem_singleton.mp new).symm mapping key form

theorem NodeInventory.finish {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (inventory : NodeInventory sources visited owner source source.nodes indices places missing) :
    Inventory sources (visited ++ [(owner, source)]) indices places missing := by
  refine ⟨inventory.inventory.origins, inventory.inventory.ownership, ?_⟩
  intro key actual member
  rcases List.mem_append.mp member with old | new
  · exact inventory.inventory.covered key actual old
  · cases List.mem_singleton.mp new
    exact inventory.covered

theorem NodeInventory.replace {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {seen : List Node} {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (previous : NodeInventory sources visited owner source seen indices places missing)
    (laterIndices : List IndexSite) {laterPlaces : List PlaceSite} {laterMissing : List MissingSite}
    (inventory : Inventory sources visited (indices ++ laterIndices) laterPlaces laterMissing)
    (includes : ∀ row, row ∈ missing → row ∈ laterMissing) :
    NodeInventory sources visited owner source seen (indices ++ laterIndices) laterPlaces laterMissing :=
  ⟨inventory, previous.covered.mono laterIndices includes⟩

/-- The finite accepted suffix fields do not require global membership. -/
def ExpressionSuffix (source : TypedSource) (node : ExpressionNode) (mapping : ExpressionId)
    (reason : Word) (row : MissingSite) (owner : Key) : Prop :=
  ∃ baseNode keyType valueType, source.lookupExpression? mapping = some baseNode ∧
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping keyType valueType ∧
    SourceCoreRawMetadata.runtimeType node.type = valueType ∧
    row = ⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩

theorem ExpressionSuffix.at_index {source : TypedSource} {node : ExpressionNode} {mapping key : ExpressionId}
    {reason : Word} {row : MissingSite} {owner : Key} (suffix : ExpressionSuffix source node mapping reason row owner)
    (indices : List IndexSite) (form : node.form = .index mapping key) {selected : IndexSite}
    (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected)
    (same : selected.reason = reason) : ExpressionAt indices owner source node row := by
  obtain ⟨base, keyType, valueType, lookup, mappingView, valueView, rowEq⟩ := suffix
  exact ⟨mapping, key, base, keyType, valueType, selected, form, lookup, mappingView, valueView, found,
    by rw [rowEq, same]⟩

def Receipt {context : SourceCoreCompatibleDataPlaceFaultSites.Context} (plan : SourceSpecializationWorklist.Plan)
    (root : Key) (sources : List (Key × TypedSource)) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  CompatibleExpressionIndexSourceReceipts.Receipt plan root sources program ∧
    Inventory (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      program.program.expressions.indices program.program.places program.missing

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMissingSourceReceipts
