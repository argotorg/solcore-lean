import Solcore.Frontend.SourceCoreDataValues
import Std.Sync.Mutex

/-! One public source value carrier. Callable handles carry no Core code or
references. Their artifact, session, export generation and slot fields are
sealed; numeric identities cannot be supplied by a caller. Ownership issuers
are retained privately by the execution adapters that mint handles. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicValues
open SourceInference TypeSystem

private initialize identityCounter : Std.Mutex Nat ← Std.Mutex.new 0
private def fresh : IO Nat := identityCounter.atomically do
  let index ← get
  set (index + 1)
  pure index

structure ArtifactAuthority where private mk ::
  private identity : Nat
  deriving Repr, DecidableEq
structure SessionAuthority where private mk ::
  private artifact : ArtifactAuthority
  private identity : Nat
  deriving Repr, DecidableEq
structure ExportGeneration where private mk ::
  private identity : Nat
  deriving Repr, DecidableEq

def ArtifactAuthority.mint : IO ArtifactAuthority := return ⟨← fresh⟩
def ArtifactAuthority.newSession (artifact : ArtifactAuthority) : IO SessionAuthority :=
  return ⟨artifact, ← fresh⟩
def ExportGeneration.mint : IO ExportGeneration := return ⟨← fresh⟩

structure Handle where private mk ::
  private artifact : ArtifactAuthority
  private session : SessionAuthority
  private generation : ExportGeneration
  private slot : Nat
  private rawType : Ty
  deriving Repr, DecidableEq

/-- Requires the private issuer retained by a session. A newly minted foreign
issuer cannot issue a handle belonging to an existing artifact/session. -/
def SessionAuthority.issue (session : SessionAuthority) (generation : ExportGeneration)
    (slot : Nat) (sourceType : Ty) : Handle :=
  ⟨session.artifact, session, generation, slot, sourceType⟩
def Handle.sourceType (handle : Handle) : Ty := handle.rawType
def Handle.belongsToArtifact (handle : Handle) (artifact : ArtifactAuthority) : Bool :=
  decide (handle.artifact = artifact)
def Handle.belongsToSession (handle : Handle) (session : SessionAuthority) : Bool :=
  decide (handle.session = session)

inductive Value where
  | unit | bool (value : Bool) | word (value : Core.Word) | integer (value : Int)
  | product (left right : Value)
  | constructed (instantiation : DataConstructorInstantiation) (payloads : List Value)
  | mapping (keyType valueType : Ty) (entries : List (Value × Value))
  | proxy (inner : Ty)
  | function (handle : Handle)
  deriving Repr

mutual
  def Value.decEq (left right : Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case unit.unit => exact isTrue rfl
    case bool.bool left right => exact decidable_of_iff (left = right) (by simp)
    case word.word left right => exact decidable_of_iff (left = right) (by simp)
    case integer.integer left right => exact decidable_of_iff (left = right) (by simp)
    case proxy.proxy left right => exact decidable_of_iff (left = right) (by simp)
    case function.function left right => exact decidable_of_iff (left = right) (by simp)
    case product.product leftA leftB rightA rightB =>
      letI := Value.decEq leftA rightA
      letI := Value.decEq leftB rightB
      exact decidable_of_iff (leftA = rightA ∧ leftB = rightB) (by simp)
    case constructed.constructed leftMetadata leftPayloads rightMetadata rightPayloads =>
      letI := Value.listDecEq leftPayloads rightPayloads
      exact decidable_of_iff (leftMetadata = rightMetadata ∧ leftPayloads = rightPayloads) (by simp)
    case mapping.mapping leftKey leftValue leftEntries rightKey rightValue rightEntries =>
      letI := Value.entriesDecEq leftEntries rightEntries
      exact decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue ∧ leftEntries = rightEntries) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.listDecEq (left right : List Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      letI := Value.decEq leftHead rightHead
      letI := Value.listDecEq leftTail rightTail
      exact decidable_of_iff (leftHead = rightHead ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.entriesDecEq (left right : List (Value × Value)) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      rcases leftHead with ⟨leftKey, leftValue⟩
      rcases rightHead with ⟨rightKey, rightValue⟩
      letI := Value.decEq leftKey rightKey
      letI := Value.decEq leftValue rightValue
      letI := Value.entriesDecEq leftTail rightTail
      letI : Decidable ((leftKey, leftValue) = (rightKey, rightValue)) :=
        decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue) (by simp)
      exact decidable_of_iff ((leftKey, leftValue) = (rightKey, rightValue) ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega
end

instance : DecidableEq Value := Value.decEq
instance : BEq Value := ⟨fun left right => decide (left = right)⟩
instance : LawfulBEq Value where
  eq_of_beq := of_decide_eq_true
  rfl := by intro value; exact decide_eq_true rfl

def Value.type : Value → Ty
  | .unit => .unit | .bool _ => .bool | .word _ => .word | .integer _ => .integer
  | .product left right => .product left.type right.type
  | .constructed instantiation _ => instantiation.resultType
  | .mapping key value _ => .mapping key value
  | .proxy inner => .proxy inner
  | .function handle => handle.sourceType


end Solcore.Frontend.SourceCorePublicValues
