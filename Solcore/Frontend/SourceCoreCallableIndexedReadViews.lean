import Solcore.Frontend.SourceCoreCallableIndexedCaptures

/-! Exact emitted generalized-read wrappers. The wrapper's original carrier
is retained in saved slot one, after the exact read-time caller snapshot,
with the same anonymous identity and contract ID. It is authenticated against actual snapshot templates before its captures
are joined to source allocation rows.

The cached read's parent/principal, own substitution/witnesses and cumulative
native instance remain separate. This unit never collapses an instantiated
source value to a ground closure. Dynamic principal headers must additionally be selected from the lexical
creation snapshot. Own substitutions and witnesses must come from the
separate read caller snapshot, through the prepared paired recipe table.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedReadViews
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Templates {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedTemplates.Cache prepared
abbrev Instance := SourceCoreLocalPolymorphism.Instance
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger

inductive Error where
  | exhausted
  | malformedWrapper
  | unknownView (id : Word)
  | monomorphicView (id : Word)
  | missingInstance (id : Word)
  | missingDescriptor (id : Word)
  | foreignOrigin (id : Word)
  | typeMismatch
  | closureMismatch
  | originalCarrierMismatch
  | contextReferenceMismatch
  | underlying (error : SourceCoreCallableIndexedTemplates.Error)
  | caller (error : SourceCoreCallableIndexedTemplates.Error)
  | captures (error : SourceCoreCallableIndexedCaptures.Error)
  deriving Repr

private def bodyHeader? : Expr → Option (Nat × ConstructorId × Word × Word)
  | .letE (.loadCell (.var index)) (.letE (.storeCell _
      (.matchData _ _ _ [_ ,
        .construct constructor (.pair (.word id) (.pair (.word target) _)), _, _])) _) =>
    some (index, constructor, id, target)
  | _ => none

structure Template {checked : Checked} (prepared : Prepared checked) where private mk ::
  entry : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan
  found : prepared.ancestry.views.entryAt? entry.id = some entry
  wrapsPrincipal : entry.view.wrapsPrincipal = true
  candidate : Instance
  selected : entry.view.selectedInstance = some candidate
  target : Word
  targetFound : (prepared.base.callableContext >>= fun native => native.table.idAt?
    (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)) = some target
  parameter : Ty
  result : Ty
  parameterExact : parameter = candidate.parameterType
  resultExact : result = candidate.resultType
  /-- Index before the successful-read binder; installed syntax can rename it. -/
  referenceIndex : Nat
  body : Expr
  carrier : Expr
  bodyExact : body = SourceCoreCallableIndexedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex
  carrierExact : carrier = SourceCoreCallableIndexedAncestry.viewRepack prepared.ancestry.layout.frame
    parameter result entry.id target referenceIndex

def decode {checked : Checked} (prepared : Prepared checked) (carrier : Expr) : Except Error (Template prepared) := do
  let .pair (.pair _ (.lambda parameter (.sum .word result) body)) _ := carrier | throw .malformedWrapper
  let (index, constructor, id, target) ← match bodyHeader? body with
    | some header => pure header | none => throw .malformedWrapper
  if index < 3 || constructor != prepared.ancestry.layout.frame.view then throw .malformedWrapper
  match found : prepared.ancestry.views.entryAt? id with
  | none => throw (.unknownView id)
  | some entry =>
    have entryId : entry.id = id := by
      have matched := found
      unfold SourceCoreCallableViews.Table.entryAt? at matched
      have selected : decide (entry.id = id) = true :=
        List.find?_some (p := fun (candidate : SourceCoreCallableViews.Entry prepared.base.sourceProgram prepared.base.plan) =>
          decide (candidate.id = id)) matched
      exact of_decide_eq_true selected
    have ownedFound : prepared.ancestry.views.entryAt? entry.id = some entry := by simpa only [entryId] using found
    if wraps : entry.view.wrapsPrincipal = true then
      match selected : entry.view.selectedInstance with
      | none => throw (.missingInstance id)
      | some candidate =>
        if targetFound : (prepared.base.callableContext >>= fun native => native.table.idAt?
            (.lambda candidate.origin.caller candidate.origin.initializer candidate.origin.substitution)) = some target then
          if types : parameter = candidate.parameterType ∧ result = candidate.resultType then
            let referenceIndex := index - 3
            if bodyExact : body = SourceCoreCallableIndexedAncestry.viewBody prepared.ancestry.layout.frame entry.id target referenceIndex then
              if carrierExact : carrier = SourceCoreCallableIndexedAncestry.viewRepack prepared.ancestry.layout.frame parameter result entry.id target referenceIndex then
                pure ⟨entry, ownedFound, wraps, candidate, selected, target, targetFound, parameter, result,
                  types.1, types.2, referenceIndex, body, carrier, bodyExact, carrierExact⟩
              else throw .malformedWrapper
            else throw .malformedWrapper
          else throw .typeMismatch
        else throw (.missingDescriptor id)
    else throw (.monomorphicView id)

mutual
  def scan {checked : Checked} (prepared : Prepared checked) : Nat → Expr → Except Error (List (Template prepared))
    | 0, _ => .error .exhausted
    | fuel + 1, expression => do
      match expression with
      | .pair (.pair identity (.lambda parameter result body)) descriptor =>
        if (bodyHeader? body).isSome then
          let template ← decode prepared expression
          pure (template :: (← scan prepared fuel body))
        else pure ((← scan prepared fuel (.pair identity (.lambda parameter result body))) ++ (← scan prepared fuel descriptor))
      | .pair left right | .apply left right | .storeCell left right | .binary _ left right | .letE left right =>
        pure ((← scan prepared fuel left) ++ (← scan prepared fuel right))
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure []
      | .lambda _ _ body =>
        if (bodyHeader? body).isSome then throw .malformedWrapper
        scan prepared fuel body
      | .first operand | .second operand | .loadCell operand | .inLeft _ operand | .inRight _ operand |
        .newCell _ operand | .construct _ operand | .unary _ operand => scan prepared fuel operand
      | .caseE first second third | .ifE first second third | .ternary _ first second third =>
        pure ((← scan prepared fuel first) ++ (← scan prepared fuel second) ++ (← scan prepared fuel third))
      | .matchData _ _ scrutinee branches => pure ((← scan prepared fuel scrutinee) ++ (← scanBranches prepared fuel branches))
  def scanBranches {checked : Checked} (prepared : Prepared checked) : Nat → List Expr → Except Error (List (Template prepared))
    | _, [] => .ok []
    | 0, _ :: _ => .error .exhausted
    | fuel + 1, head :: tail => do pure ((← scan prepared fuel head) ++ (← scanBranches prepared fuel tail))
end

structure Cache {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) where private mk ::
  groups : List (List (Template prepared))
  scanned : (prepared.secondPass.closures.zipIdx.mapM fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) = .ok groups

def Cache.wrappers {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) : List (Template prepared) := cache.groups.flatten

/-- Compilation provenance remains the actual snapshot cache's second pass. -/
theorem Cache.compiled {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (_cache : Cache templates) : SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := templates.compiled

def prepare {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) : Except Error (Cache templates) :=
  match scanned : prepared.secondPass.closures.zipIdx.mapM (fun (closure, index) =>
    scan prepared (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreLambdaTemplates.installedTemplate index closure))
      (SourceCoreLambdaTemplates.installedTemplate index closure)) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups, scanned⟩

private theorem original_typed {definitions : DataEnvironment} {world : StoreTyping}
    {identity callerSnapshot original : Value} {outer : Environment} {body : Expr}
    {descriptor : Word} {parameter result : Ty}
    (typed : RuntimeValueHasType world (.pair (.pair identity
      (.closure parameter (LanguageResult.resultType result) body (callerSnapshot :: original :: outer))) (.word descriptor))
      (CallableContract.functionType parameter result) definitions) :
    RuntimeValueHasType world original original.type definitions := by
  cases typed with
  | pair tagged _ =>
    cases tagged with
    | pair _ payload => exact SourceCoreCallableNativeSlots.saved_slot_typed (index := 1) payload rfl

private theorem caller_typed {definitions : DataEnvironment} {world : StoreTyping}
    {identity callerSnapshot original : Value} {outer : Environment} {body : Expr}
    {descriptor : Word} {parameter result : Ty}
    (typed : RuntimeValueHasType world (.pair (.pair identity
      (.closure parameter (LanguageResult.resultType result) body (callerSnapshot :: original :: outer))) (.word descriptor))
      (CallableContract.functionType parameter result) definitions) :
    RuntimeValueHasType world callerSnapshot callerSnapshot.type definitions := by
  cases typed with
  | pair tagged _ =>
    cases tagged with
    | pair _ payload => exact SourceCoreCallableNativeSlots.saved_slot_typed (index := 0) payload rfl

private theorem snapshot_type {checked : Checked} {prepared : Prepared checked} {value : Value}
    (snapshot : SourceCoreCallableIndexedTemplates.Snapshot prepared value) : value.type = prepared.ancestry.layout.frame.type := by
  rw [snapshot.exact]
  cases snapshot.frame <;> rfl

structure Authenticated {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  wrapper : Template prepared
  member : wrapper ∈ cache.wrappers
  callerSnapshot : Value
  caller : SourceCoreCallableIndexedTemplates.Snapshot prepared callerSnapshot
  callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions
  original : Value
  outer : Environment
  exact : value = .pair (.pair (.inLeft .word .unit)
    (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (callerSnapshot :: original :: outer))) (.word wrapper.target)
  typed : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions
  underlying : SourceCoreCallableIndexedTemplates.Authenticated templates world store original
  targetExact : underlying.template.source.lambda.descriptor = wrapper.target
  originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
    underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
    underlying.template.source.lambda.active = wrapper.entry.view.cumulative
  contextSlot : (callerSnapshot :: original :: outer)[wrapper.referenceIndex + 2]? =
    some (.cellRef prepared.ancestry.layout.frame.type 0)

def authenticate {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) {world : StoreTyping} {store : Store}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions) (value : Value) (parameter result : Ty)
    (typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) prepared.layouts.definitions) :
    Except Error (Authenticated cache world store value) := do
  let .pair (.pair (.inLeft .word .unit) (.closure _ _ body (callerSnapshot :: original :: outer))) (.word descriptor) := value
    | throw .closureMismatch
  let chosen ← match cache.wrappers.attach.find? (fun wrapper => decide
      (wrapper.val.body = body ∧ wrapper.val.parameter = parameter ∧ wrapper.val.result = result ∧ wrapper.val.target = descriptor)) with
    | none => throw .closureMismatch | some wrapper => pure wrapper
  let wrapper := chosen.val
  if types : wrapper.parameter = parameter ∧ wrapper.result = result then
    if exact : value = .pair (.pair (.inLeft .word .unit)
        (.closure wrapper.parameter (LanguageResult.resultType wrapper.result) wrapper.body (callerSnapshot :: original :: outer))) (.word wrapper.target) then
      have typedWrapper : RuntimeValueHasType world value (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions := by
        simpa only [types.1, types.2] using typed
      let caller ← (SourceCoreCallableIndexedTemplates.decodeSnapshot prepared callerSnapshot).mapError Error.caller
      have callerTyped : RuntimeValueHasType world callerSnapshot prepared.ancestry.layout.frame.type prepared.layouts.definitions := by
        have own := caller_typed (exact ▸ typedWrapper)
        rw [snapshot_type caller] at own
        exact own
      have originalOwn : RuntimeValueHasType world original original.type prepared.layouts.definitions :=
        original_typed (exact ▸ typedWrapper)
      if originalType : original.type = CallableContract.functionType wrapper.parameter wrapper.result then
        have originalTyped : RuntimeValueHasType world original (CallableContract.functionType wrapper.parameter wrapper.result) prepared.layouts.definitions :=
          originalType ▸ originalOwn
        let underlying ← (SourceCoreCallableIndexedTemplates.authenticate templates stored original wrapper.parameter wrapper.result originalTyped)
          |>.mapError Error.underlying
        if targetExact : underlying.template.source.lambda.descriptor = wrapper.target then
          if originExact : underlying.template.source.lambda.owner = wrapper.entry.view.owner ∧
              underlying.template.source.lambda.id = wrapper.entry.view.binding.initializer ∧
              underlying.template.source.lambda.active = wrapper.entry.view.cumulative then
            if contextSlot : (callerSnapshot :: original :: outer)[wrapper.referenceIndex + 2]? = some (.cellRef prepared.ancestry.layout.frame.type 0) then
              pure ⟨wrapper, chosen.property, callerSnapshot, caller, callerTyped, original, outer, exact, typedWrapper, originalTyped,
                underlying, targetExact, originExact, contextSlot⟩
            else throw .contextReferenceMismatch
          else throw (.foreignOrigin wrapper.entry.id)
        else throw .originalCarrierMismatch
      else throw .originalCarrierMismatch
    else throw .closureMismatch
  else throw .typeMismatch

structure Produced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared) where private mk ::
  result : Value
  observation : completion.result.native.observation = .succeeded result store
  subvalue : SourceCoreCallableIndexedCaptures.Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value result : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : SourceCoreCallableIndexedCaptures.Subvalue value result) : Produced authenticated completion :=
  ⟨result, observation, subvalue⟩

structure Stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) (completion : Completion prepared)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  observation : SourceCoreCallableIndexedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : SourceCoreCallableIndexedCaptures.Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value payload : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (observation : SourceCoreCallableIndexedLedger.store completion = store) (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : SourceCoreCallableIndexedCaptures.Subvalue value payload) : Stored authenticated completion ledger :=
  ⟨observation, ordinal, payload, payloadFound, subvalue⟩

structure JoinedProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger

structure JoinedStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) where private mk ::
  captures : SourceCoreCallableIndexedCaptures.Captured authenticated.underlying ledger

def joinProduced {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    (produced : Produced authenticated completion) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (JoinedProduced produced ledger) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored authenticated completion ledger) : Except Error (JoinedStored stored) := do
  let captures ← (SourceCoreCallableIndexedCaptures.joinAuthenticated authenticated.underlying ledger).mapError Error.captures
  pure ⟨captures⟩

theorem JoinedProduced.capture_order {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {produced : Produced authenticated completion} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} (joined : JoinedProduced produced ledger) :
    joined.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst :=
  joined.captures.binders

theorem JoinedStored.capture_order {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {completion : Completion prepared}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    {stored : Stored authenticated completion ledger} (joined : JoinedStored stored) :
    joined.captures.environment.map Prod.fst = authenticated.underlying.template.source.scope.map Prod.fst :=
  joined.captures.binders

/-- Canonical read metadata remains separate from dynamic principal headers.
Occurrence witnesses for a dynamically rewritten parent source must be supplied
by its prepared graph transition, rather than assumed equal to these rows. -/
def Authenticated.canonicalOwnSubstitution {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.ownSubstitution

def Authenticated.canonicalOwnWitnesses {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : List SourceCoreLocalEvidence.Witness :=
  authenticated.wrapper.entry.view.ownWitnesses

def Authenticated.parentActive {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.parentActive

def Authenticated.cumulative {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypeSystem.Substitution :=
  authenticated.wrapper.entry.view.cumulative

def Authenticated.canonicalPrincipalSource {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) : TypedSource :=
  authenticated.wrapper.entry.view.principal.source

end Solcore.Frontend.SourceCoreCallableIndexedReadViews
