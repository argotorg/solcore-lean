import Solcore.Frontend.RuntimeCapturedOwnerProperties
import Solcore.Frontend.RuntimeValueOwnerProperties
import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.ClosedSourceEvaluatorOwnerStepProperties

/- Direct joint budget induction keeps complete successes and failures.
All stored owners and payloads are relabeled; source syntax and depth are literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

private def endpoint (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (result : RuntimeValue × List RuntimeValue) : RuntimeValue × List RuntimeValue :=
  (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))

private theorem creation (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    (do let _ ← sourceUnaryLambdaShape? source
        pure (RuntimeValue.sourceClosure source (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured),
          store.map (RuntimeValue.mapOwners mapping))) =
      (do let _ ← sourceUnaryLambdaShape? source
          pure (RuntimeValue.sourceClosure source owner names captured,store)).map (endpoint mapping) := by
  cases shape : sourceUnaryLambdaShape? source <;>
    simp only [bind,Option.bind_none,Option.bind_some,pure,Option.map_none,Option.map_some,
      endpoint,RuntimeValue.mapOwners_sourceClosure]

private theorem pair_tail (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (left : RuntimeValue) (tail : Option (RuntimeValue × List RuntimeValue)) :
    ((tail.map (endpoint mapping)).bind fun result => pure (.pair (left.mapOwners mapping) result.1,result.2)) =
      (tail.bind fun result => pure (RuntimeValue.pair left result.1,result.2)).map (endpoint mapping) := by
  cases tail with
  | none => rfl
  | some result =>
    rcases result with ⟨right,store⟩
    simp only [Option.map_some,Option.bind_some,pure,endpoint,RuntimeValue.mapOwners]

private theorem strict_tail (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (operator : Syntax.BinaryOp) (left : Core.Word) (tail : Option (RuntimeValue × List RuntimeValue)) :
    ((tail.map (endpoint mapping)).bind fun result => match result with
      | (.word right,store) => (evaluateStrictWordBinary? operator left right).bind fun value =>
          pure (RuntimeValue.ofCore value,store)
      | _ => none) =
    (tail.bind fun result => match result with
      | (.word right,store) => (evaluateStrictWordBinary? operator left right).bind fun value =>
          pure (RuntimeValue.ofCore value,store)
      | _ => none).map (endpoint mapping) := by
  cases tail with
  | none => rfl
  | some result =>
    rcases result with ⟨value,store⟩
    cases value <;> simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners,Option.map_none]
    rename_i right
    cases meaning : evaluateStrictWordBinary? operator left right <;>
      simp only [Option.bind_none,Option.bind_some,pure,Option.map_none,Option.map_some,endpoint,
        RuntimeValue.mapOwners_ofCore]

section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

private theorem simultaneous (budget : Nat) :
    (∀ owner names captured store source,
      evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceExpression? budget owner names captured store source).map (endpoint mapping)) ∧
    (∀ owner names captured store source,
      evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
      (evaluateClosedSourceBody? budget owner names captured store source).map (endpoint mapping)) := by
  induction budget with
  | zero =>
    constructor <;> intro owner names captured store source
    · simp only [evaluateClosedSourceExpression?,Option.map_none]
    · simp only [evaluateClosedSourceBody?,Option.map_none]
  | succ n ih =>
    constructor
    · intro owner names captured store source
      rcases source with ⟨span,payload⟩
      cases payload <;> try (solve |
        simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _)
      case identifier name =>
        simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_mapIds]
        cases named : names.lookup? name.value with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some id =>
          simp only [Option.map_some,bind,Option.bind_some,
            lookup?_mapRuntimeCapturedOwners mapping injective]
          cases found : captured.lookup? id <;>
            simp only [Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,pure,endpoint]
      case literal literal =>
        simp only [evaluateClosedSourceExpression?]
        cases interpreted : interpretWordLiteral? literal <;>
          simp only [bind,Option.bind_none,Option.bind_some,pure,
            Option.map_none,Option.map_some,endpoint,RuntimeValue.mapOwners]
      case group inner =>
        simpa only [evaluateClosedSourceExpression?] using ih.1 owner names captured store inner
      case tuple elements =>
        rcases elements with ⟨tupleSpan,children⟩
        cases children with
        | nil => simp only [evaluateClosedSourceExpression?,Option.map_some,endpoint,RuntimeValue.mapOwners]
        | cons left remaining =>
          cases remaining with
          | nil => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
          | cons right tail =>
            cases tail <;>
              simp only [evaluateClosedSourceExpression?,ih.1]
            all_goals
              cases first : evaluateClosedSourceExpression? n owner names captured store left with
              | none => simp only [Option.map_none,bind,Option.bind_none]
              | some result =>
                rcases result with ⟨value,middle⟩
                simp only [Option.map_some,bind,Option.bind_some,endpoint,ih.1]
                exact pair_tail mapping value _
      case conditional condition question thenBranch colon elseBranch =>
        simp only [evaluateClosedSourceExpression?,ih.1]
        cases first : evaluateClosedSourceExpression? n owner names captured store condition with
        | none => simp only [Option.map_none,bind,Option.bind_none]
        | some result =>
          rcases result with ⟨value,middle⟩
          cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,RuntimeValue.mapOwners,ih.1,
            Option.map_none]
      case unary operator operand =>
        rcases operator with ⟨operatorSpan,operator⟩
        cases operator <;> simp only [evaluateClosedSourceExpression?,ih.1]
        all_goals
          cases first : evaluateClosedSourceExpression? n owner names captured store operand with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,final⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,
              RuntimeValue.mapOwners,pure,Option.map_none]
      case binary left operator right =>
        rcases operator with ⟨operatorSpan,operator⟩
        cases operator <;> simp only [evaluateClosedSourceExpression?,ih.1]
        all_goals
          cases first : evaluateClosedSourceExpression? n owner names captured store left with
          | none => simp only [Option.map_none,bind,Option.bind_none]
          | some result =>
            rcases result with ⟨value,middle⟩
            cases value <;> simp only [Option.map_some,bind,Option.bind_some,endpoint,
              RuntimeValue.mapOwners,Option.map_none,ih.1]
            all_goals first
              | exact strict_tail mapping _ _ _
              | rename_i choice
                cases choice <;> simp only [Bool.false_eq_true,↓reduceIte,pure,Option.map_some,endpoint,
                  RuntimeValue.mapOwners]
      case call callee arguments =>
        rcases arguments with ⟨argumentsSpan,arguments⟩
        cases arguments with
        | nil => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
        | cons argument rest =>
          cases rest with
          | cons _ _ => simpa only [evaluateClosedSourceExpression?] using creation mapping owner names captured store _
          | nil =>
            simp only [evaluateClosedSourceExpression?,ih.1]
            cases first : evaluateClosedSourceExpression? n owner names captured store callee with
            | none => simp only [Option.map_none,bind,Option.bind_none]
            | some result =>
              rcases result with ⟨function,middle⟩
              simp only [Option.map_some,bind,Option.bind_some,endpoint,ih.1]
              cases second : evaluateClosedSourceExpression? n owner names captured middle argument with
              | none => simp only [Option.map_none,Option.bind_none]
              | some result =>
                rcases result with ⟨value,final⟩
                cases function <;> try (solve |
                  simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners,Option.map_none])
                case sourceClosure saved savedOwner savedNames savedCaptured =>
                  simp only [Option.map_some,Option.bind_some,endpoint,RuntimeValue.mapOwners_sourceClosure]
                  cases shape : sourceUnaryLambdaShape? saved with
                  | none => simp only [Option.bind_none,Option.map_none]
                  | some bodyInfo =>
                    rcases bodyInfo with ⟨name,body⟩
                    simp only [Option.bind_some]
                    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
                    simpa only [LocalNameTable.mapIds,mapRuntimeCapturedOwners,List.map_cons] using
                      ih.2 savedOwner ((name.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
                        ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),value)::savedCaptured) final body
    · intro owner names captured store source
      exact evaluateClosedSourceBody?_mapOwners_step mapping injective n
        ih.1 ih.2
        owner names captured store source

/-- Exact owner covariance of every finite expression outcome, including absence. -/
theorem evaluateClosedSourceExpression?_mapOwners
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceExpression? budget owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) :=
  (simultaneous mapping injective budget).1 owner names captured store source

/-- Exact body covariance retains the same budget, selected syntax and complete endpoint. -/
theorem evaluateClosedSourceBody?_mapOwners
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
    (evaluateClosedSourceBody? budget owner names captured store source).map
      (fun result => (result.1.mapOwners mapping,result.2.map (RuntimeValue.mapOwners mapping))) :=
  (simultaneous mapping injective budget).2 owner names captured store source

end
end Solcore.Frontend
