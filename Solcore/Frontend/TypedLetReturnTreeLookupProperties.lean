import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorProperties

/-! Raw recursive results depend on composed first-match values, not the
identity or layout of the intermediate keys. Owners and fresh IDs may differ.
These laws do not establish whole checking or equality of Core checkpoints. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem lookup_bind_fresh (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment)
    (binder spelling : String) (value : Core.Value) :
    (LocalNameTable.lookup? ((binder, Resolved.freshLocalId owner (table.map Prod.snd)) :: table) spelling).bind
        (Resolved.LocalScope.lookup? ((Resolved.freshLocalId owner (table.map Prod.snd), value) :: environment)) =
      if binder = spelling then some value else (table.lookup? spelling).bind environment.lookup? := by
  by_cases same : binder = spelling
  · simp only [LocalNameTable.lookup?, if_pos same, Option.bind_some, Resolved.LocalScope.lookup?, ↓reduceIte]
  · simp only [LocalNameTable.lookup?, if_neg same]
    cases found : table.lookup? spelling with
    | none => rfl
    | some id =>
        have different : Resolved.freshLocalId owner (table.map Prod.snd) ≠ id := by
          intro equal
          apply Resolved.freshLocalId_not_mem owner (table.map Prod.snd)
          rw [equal]
          exact List.mem_map_of_mem (f := Prod.snd) (LocalNameTable.lookup?_iff.mp found).mem
        simp only [Option.bind_some, Resolved.LocalScope.lookup?, if_neg different]

private theorem lookup_fresh_congr
    (leftOwner rightOwner : Resolved.DeclarationId) (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (binder : String) (value : Core.Value) :
    ∀ name,
      (LocalNameTable.lookup? ((binder, Resolved.freshLocalId leftOwner (leftTable.map Prod.snd)) :: leftTable) name).bind
          (Resolved.LocalScope.lookup? ((Resolved.freshLocalId leftOwner (leftTable.map Prod.snd), value) :: leftEnvironment)) =
        (LocalNameTable.lookup? ((binder, Resolved.freshLocalId rightOwner (rightTable.map Prod.snd)) :: rightTable) name).bind
          (Resolved.LocalScope.lookup? ((Resolved.freshLocalId rightOwner (rightTable.map Prod.snd), value) :: rightEnvironment)) := by
  intro name
  rw [lookup_bind_fresh, lookup_bind_fresh, sameLookup name]

/-- Equal composed actual-value lookups preserve full raw results even when
owners, scope lengths and independently allocated fresh identities differ. -/
theorem evaluateTypedLetReturnTreeWithCost?_congr_lookup
    (leftOwner rightOwner : Resolved.DeclarationId) (leftTable rightTable : LocalNameTable)
    (leftEnvironment rightEnvironment : Resolved.Environment)
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?) (body : Syntax.Block) :
    evaluateTypedLetReturnTreeWithCost? leftOwner leftTable leftEnvironment body =
      evaluateTypedLetReturnTreeWithCost? rightOwner rightTable rightEnvironment body := by
  cases body with
  | mk blockSpan statements =>
      cases statements with
      | nil => simp only [evaluateTypedLetReturnTreeWithCost?]
      | cons statement rest =>
          cases statement with
          | mk statementSpan payload =>
              cases payload <;> try simp only [evaluateTypedLetReturnTreeWithCost?]
              case returnStmt returned =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases returned with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some source =>
                        simpa only [evaluateTypedLetReturnTreeWithCost?] using
                          evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup source
              case block inner =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    simpa only [evaluateTypedLetReturnTreeWithCost?] using
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                        leftEnvironment rightEnvironment sameLookup ⟨statementSpan, inner⟩
              case letDecl name optionalType optionalInitializer =>
                cases optionalInitializer with
                | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                | some initializer =>
                    have tailSame (boundValue : Core.Value) :
                        evaluateTypedLetReturnTreeWithCost? leftOwner
                          ((name.value, Resolved.freshLocalId leftOwner (leftTable.map Prod.snd)) :: leftTable)
                          ((Resolved.freshLocalId leftOwner (leftTable.map Prod.snd), boundValue) :: leftEnvironment) ⟨blockSpan, rest⟩ =
                        evaluateTypedLetReturnTreeWithCost? rightOwner
                          ((name.value, Resolved.freshLocalId rightOwner (rightTable.map Prod.snd)) :: rightTable)
                          ((Resolved.freshLocalId rightOwner (rightTable.map Prod.snd), boundValue) :: rightEnvironment) ⟨blockSpan, rest⟩ :=
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner _ _ _ _
                        (lookup_fresh_congr leftOwner rightOwner leftTable rightTable leftEnvironment rightEnvironment
                          sameLookup name.value boundValue) ⟨blockSpan, rest⟩
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup]
                    simp only [tailSame]
              case expression source terminated =>
                cases terminated with
                | false => simp only [evaluateTypedLetReturnTreeWithCost?]
                | true =>
                    rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                      evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup,
                      evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                        leftEnvironment rightEnvironment sameLookup ⟨blockSpan, rest⟩]
              case ifThen condition thenBody optionalElse =>
                cases rest with
                | cons _ _ => simp only [evaluateTypedLetReturnTreeWithCost?]
                | nil =>
                    cases optionalElse with
                    | none => simp only [evaluateTypedLetReturnTreeWithCost?]
                    | some elseBody =>
                        rw [evaluateTypedLetReturnTreeWithCost?, evaluateTypedLetReturnTreeWithCost?,
                          evaluateLocalExpressionWithCost?_congr_lookup leftTable rightTable leftEnvironment rightEnvironment sameLookup,
                          evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup thenBody,
                          evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
                            leftEnvironment rightEnvironment sameLookup elseBody]
termination_by sizeOf body

/-- The relation still records both stores: observational equality cannot
replace a successful path's final store by an unrelated store. -/
theorem typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff
    {leftOwner rightOwner : Resolved.DeclarationId} {leftTable rightTable : LocalNameTable}
    {leftEnvironment rightEnvironment : Resolved.Environment}
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?)
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost leftOwner leftTable leftEnvironment initialStore body value finalStore cost ↔
      TypedLetReturnTreeEvaluatesWithCost rightOwner rightTable rightEnvironment initialStore body value finalStore cost := by
  rw [typedLetReturnTreeEvaluatesWithCost_iff_evaluate, typedLetReturnTreeEvaluatesWithCost_iff_evaluate,
    evaluateTypedLetReturnTreeWithCost?_congr_lookup leftOwner rightOwner leftTable rightTable
      leftEnvironment rightEnvironment sameLookup]

theorem typedLetReturnTreeEvaluates_congr_lookup_iff
    {leftOwner rightOwner : Resolved.DeclarationId} {leftTable rightTable : LocalNameTable}
    {leftEnvironment rightEnvironment : Resolved.Environment}
    (sameLookup : ∀ name, (leftTable.lookup? name).bind leftEnvironment.lookup? =
      (rightTable.lookup? name).bind rightEnvironment.lookup?)
    {body : Syntax.Block} {initialStore finalStore : Core.Store} {value : Core.Value} :
    TypedLetReturnTreeEvaluates leftOwner leftTable leftEnvironment initialStore body value finalStore ↔
      TypedLetReturnTreeEvaluates rightOwner rightTable rightEnvironment initialStore body value finalStore := by
  rw [typedLetReturnTreeEvaluates_iff_exists_cost, typedLetReturnTreeEvaluates_iff_exists_cost]
  exact exists_congr fun _ => typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff sameLookup

end Solcore.Frontend
