import Solcore.Frontend.SourceRuntimeProperties
import Solcore.Frontend.SourceRuntimeStaticInversionProperties
import Solcore.Frontend.SourceRuntimeStaticOperatorProperties

/-! Deep typing bridges for values in the finite graph runtime. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- The graph relation extends Core deep typing without losing the original
Core closure and cell-world evidence. -/
theorem Value.GraphHasType.ofCore
    {program : Program} {world : Core.StoreTyping}
    {core : Core.Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Core.RuntimeValueHasType world core expected definitions) :
    Value.GraphHasType program world (Value.ofCore core) expected definitions := by
  apply Value.GraphHasType.core (Value.toCore?_ofCore core) typing
  have shallow := Value.hasType_of_toCore? program (Value.ofCore core) core
    (Value.toCore?_ofCore core)
  simpa [typing.type_eq] using shallow

/-- A successful Core projection of a deeply typed graph value is itself
deeply typed, including pairs and sums assembled by graph evaluation. -/
theorem Value.GraphHasType.toCore
    {program : Program} {world : Core.StoreTyping}
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program world value expected definitions) :
    ∀ {core : Core.Value}, value.toCore? = some core →
      Core.RuntimeValueHasType world core expected definitions := by
  induction typing using Value.GraphHasType.rec
      (motive_2 := fun _ _ _ _ => True) with
  | core projection coreTyping _ =>
      intro core projected
      rw [projection] at projected
      cases projected
      exact coreTyping
  | pair leftTyping rightTyping leftIH rightIH =>
      rename_i leftValue rightValue leftType rightType
      intro core projected
      cases leftProjection : leftValue.toCore? with
      | none => simp [Value.toCore?, leftProjection] at projected
      | some coreLeft =>
          cases rightProjection : rightValue.toCore? with
          | none =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
          | some coreRight =>
              simp [Value.toCore?, leftProjection, rightProjection] at projected
              cases projected
              exact .pair (leftIH leftProjection) (rightIH rightProjection)
  | inLeft payloadTyping payloadIH =>
      rename_i payloadValue leftType rightType
      intro core projected
      cases payloadProjection : payloadValue.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          exact .inLeft (payloadIH payloadProjection)
  | inRight payloadTyping payloadIH =>
      rename_i payloadValue leftType rightType
      intro core projected
      cases payloadProjection : payloadValue.toCore? with
      | none => simp [Value.toCore?, payloadProjection] at projected
      | some corePayload =>
          simp [Value.toCore?, payloadProjection] at projected
          cases projected
          exact .inRight (payloadIH payloadProjection)
  | sourceClosure =>
      intro core projected
      simp [Value.toCore?] at projected
  | global =>
      intro core projected
      simp [Value.toCore?] at projected
  | nil => trivial
  | cons => trivial

/-- Deep typing of a graph pair can always be inverted, even when the pair
entered through a single Core projection rather than the graph constructor. -/
theorem Value.GraphHasType.pairComponents
    {program : Program} {world : Core.StoreTyping}
    {left right : Value} {leftType rightType : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program world (.pair left right)
      (.product leftType rightType) definitions) :
    Value.GraphHasType program world left leftType definitions ∧
    Value.GraphHasType program world right rightType definitions := by
  cases typing with
  | pair leftTyping rightTyping =>
      exact ⟨leftTyping, rightTyping⟩
  | core projection coreTyping _ =>
      cases leftProjection : left.toCore? with
      | none => simp [Value.toCore?, leftProjection] at projection
      | some coreLeft =>
          cases rightProjection : right.toCore? with
          | none =>
              simp [Value.toCore?, leftProjection, rightProjection]
                at projection
          | some coreRight =>
              simp [Value.toCore?, leftProjection, rightProjection]
                at projection
              cases projection
              cases coreTyping with
              | pair coreLeftTyping coreRightTyping =>
                  have leftShallow := Value.hasType_of_toCore? program left
                    coreLeft leftProjection
                  have rightShallow := Value.hasType_of_toCore? program right
                    coreRight rightProjection
                  exact ⟨.core leftProjection coreLeftTyping
                    (by simpa [coreLeftTyping.type_eq] using leftShallow),
                    .core rightProjection coreRightTyping
                    (by simpa [coreRightTyping.type_eq] using rightShallow)⟩

/-- Projecting a graph value accepted through the Core boundary recovers the
same deep Core judgement. -/
theorem Value.GraphHasType.coreProjection
    {program : Program} {world : Core.StoreTyping}
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (projected : value.RuntimeHasType world expected definitions) :
    value.GraphHasType program world expected definitions := by
  obtain ⟨core, projection, coreTyping⟩ := projected
  exact .core projection coreTyping
    (Value.RuntimeHasType.hasType ⟨core, projection, coreTyping⟩ program)

inductive EnvironmentShallowMatches (program : Program) :
    Environment → StaticContext → Prop where
  | nil : EnvironmentShallowMatches program [] []
  | cons {id : Resolved.LocalId} {value : Value}
      {staticType : StaticType} {environment : Environment}
      {context : StaticContext} :
      Value.HasType program value staticType.erase →
      EnvironmentShallowMatches program environment context →
      EnvironmentShallowMatches program ((id, value) :: environment)
        ((id, staticType) :: context)

/-- Deep lexical-environment typing implies a pointwise shallow context
agreement, including the identity of every captured local. -/
theorem EnvironmentGraphHasTypes.shallow
    {program : Program} {world : Core.StoreTyping}
    {environment : Environment} {context : StaticContext}
    {definitions : Core.DataEnvironment}
    (typing : EnvironmentGraphHasTypes program world environment context
      definitions) :
    EnvironmentShallowMatches program environment context := by
  induction typing using EnvironmentGraphHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) with
  | core | pair | inLeft | inRight | sourceClosure | global => trivial
  | nil => exact .nil
  | cons head _ _ tailIH =>
      exact .cons head.hasType tailIH

/-- Extending a well-typed heap cannot invalidate a graph value, including a
source closure with captured cell references. -/
theorem Value.GraphHasType.weaken
    {program : Program} {initial future : Core.StoreTyping}
    (extension : Core.WorldExtends initial future)
    {value : Value} {expected : Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : Value.GraphHasType program initial value expected definitions) :
    Value.GraphHasType program future value expected definitions := by
  apply Value.GraphHasType.rec
      (motive_1 := fun value expected definitions _ =>
        Value.GraphHasType program future value expected definitions)
      (motive_2 := fun environment context definitions _ =>
        EnvironmentGraphHasTypes program future environment context definitions)
      (t := typing)
  case core =>
    intro _ _ _ _ projection coreTyping shallow
    exact .core projection (coreTyping.weaken extension) shallow
  case pair =>
    intro _ _ _ _ _ _ _ leftIH rightIH
    exact .pair leftIH rightIH
  case inLeft =>
    intro _ _ _ _ _ payloadIH
    exact .inLeft payloadIH
  case inRight =>
    intro _ _ _ _ _ payloadIH
    exact .inRight payloadIH
  case sourceClosure =>
    intro _ _ _ _ _ _ _ bodyTyping environmentIH
    exact .sourceClosure environmentIH bodyTyping
  case global =>
    intro _ _ _ wellTyped found
    exact .global wellTyped found
  case nil =>
    intro _
    exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ _ headIH tailIH
    exact .cons headIH tailIH

/-- Lexical environments captured by source closures remain valid when the
heap world grows during later evaluation. -/
theorem EnvironmentGraphHasTypes.weaken
    {program : Program} {initial future : Core.StoreTyping}
    (extension : Core.WorldExtends initial future)
    {environment : Environment} {context : StaticContext}
    {definitions : Core.DataEnvironment}
    (typing : EnvironmentGraphHasTypes program initial environment context
      definitions) :
    EnvironmentGraphHasTypes program future environment context definitions := by
  induction environment generalizing context with
  | nil =>
      cases typing
      exact .nil
  | cons entry rest ih =>
      cases typing with
      | cons head tail =>
          exact .cons (head.weaken extension) (ih tail)

theorem Value.GraphHasType.unit
    (program : Program) (world : Core.StoreTyping)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world .unit .unit definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.unit

theorem Value.GraphHasType.bool
    (program : Program) (world : Core.StoreTyping) (value : Bool)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world (.bool value) .bool definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.bool

theorem Value.GraphHasType.word
    (program : Program) (world : Core.StoreTyping) (value : Core.Word)
    (definitions : Core.DataEnvironment := []) :
    Value.GraphHasType program world (.word value) .word definitions :=
  Value.GraphHasType.ofCore Core.RuntimeValueHasType.word

/-- Primitive Core unary operations return deep primitive values, not just
values with matching shallow tags. -/
theorem unary_apply_result_graph_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {op : Core.UnaryOp} {operand result : Core.Value}
    (applied : op.apply operand = some result) :
    Value.GraphHasType program world (Value.ofCore result) op.resultType
      definitions := by
  have resultTyping : Core.RuntimeValueHasType world result op.resultType
      definitions := by
    have resultType := Core.UnaryOp.apply_result_type applied
    clear applied operand
    cases op <;> cases result <;>
      simp [Core.Value.type, Core.UnaryOp.resultType] at resultType
    all_goals constructor
  exact Value.GraphHasType.ofCore resultTyping

/-- Primitive Core binary operations likewise return deep primitive values. -/
theorem binary_apply_result_graph_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {op : Core.BinaryOp} {left right result : Core.Value}
    (applied : op.apply left right = some result) :
    Value.GraphHasType program world (Value.ofCore result) op.resultType
      definitions := by
  have resultTyping : Core.RuntimeValueHasType world result op.resultType
      definitions := by
    have resultType := Core.BinaryOp.apply_result_type applied
    clear applied left right
    cases op <;> cases result <;>
      simp [Core.Value.type, Core.BinaryOp.resultType] at resultType
    all_goals constructor
  exact Value.GraphHasType.ofCore resultTyping

/-- A deeply typed embedded Core closure runs in a typed Core state.  On
success both its result and the final heap re-enter the graph relation.  This
is the Core-callback branch needed by the graph evaluator preservation proof. -/
theorem Value.coreClosure_application_preserves_result_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameterType resultType : Core.Ty}
    {body : Core.Expr} {captured : Core.Environment}
    {argument value : Core.Value}
    {initialStore finalStore : Core.Store} {fuel : Nat}
    (closureTyping : Core.RuntimeValueHasType world
      (.closure parameterType resultType body captured)
      (.function parameterType resultType) definitions)
    (argumentTyping : Core.RuntimeValueHasType world argument parameterType
      definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : Core.runStateful fuel
      (Core.State.initial body (argument :: captured) initialStore) =
        .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld (Value.ofCore value) resultType
        definitions := by
  cases closureTyping with
  | closure capturedTyping bodyTyping =>
      have evaluation := Core.runStateful_evaluation_sound completed
      obtain ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩ :=
        Core.evaluation_preserves_type evaluation bodyTyping
          (Core.RuntimeEnvironmentHasTypes.cons argumentTyping capturedTyping)
          storeTyping
      exact ⟨finalWorld, extension, finalStoreTyping,
        Value.GraphHasType.ofCore resultTyping⟩

/-- Preservation for the actual `applyValue` Core-closure branch: a graph
argument assembled from deeply typed pieces can cross into Core, and a
successful callback returns a deeply typed graph value and final heap. -/
theorem applyValue_coreClosure_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameterType resultType : Core.Ty}
    {body : Core.Expr} {captured : Core.Environment}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (functionTyping : Value.GraphHasType program world
      (.coreClosure parameterType resultType body captured)
      (.function parameterType resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) parameterType definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel
      (.coreClosure parameterType resultType body captured)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  cases functionTyping with
  | core projection coreTyping _ =>
      simp [Value.toCore?] at projection
      cases projection
      have argumentTag := argumentTyping.hasType
      simp only [Value.HasType] at argumentTag
      cases argumentProjection : (packValues arguments).toCore? with
      | none =>
          simp [applyValue, argumentTag, argumentProjection] at completed
          split at completed <;> contradiction
      | some coreArgument =>
          have coreArgumentTyping :=
            argumentTyping.toCore argumentProjection
          cases coreRun : Core.runStateful coreFuel
              (Core.State.initial body (coreArgument :: captured)
                initialStore) with
          | outOfFuel state =>
              simp [applyValue, argumentTag, argumentProjection, coreRun]
                at completed
              split at completed <;> contradiction
          | fault error state =>
              simp [applyValue, argumentTag, argumentProjection, coreRun]
                at completed
              split at completed <;> contradiction
          | done coreValue coreStore =>
              have coreClosureTyping : Core.RuntimeValueHasType world
                  (.closure parameterType resultType body captured)
                  (.function parameterType resultType) definitions :=
                coreTyping
              obtain ⟨finalWorld, extension, finalStoreTyping,
                resultTyping⟩ :=
                Value.coreClosure_application_preserves_result_type
                  (program := program) coreClosureTyping coreArgumentTyping
                  storeTyping coreRun
              have coreResultTyping := resultTyping.toCore
                (Value.toCore?_ofCore coreValue)
              have resultTag : coreValue.type = resultType :=
                coreResultTyping.type_eq
              simp [applyValue, argumentTag, argumentProjection, coreRun,
                resultTag] at completed
              split at completed
              · contradiction
              cases completed
              exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- Deep Core argument typing transfers to the source runtime's named binder
environment when the selected definition's parameter types agree. -/
theorem EnvironmentGraphHasTypes.ofCoreParameters
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {arguments : List Core.Value} {types : List Core.Ty}
    (typing : Core.RuntimeEnvironmentHasTypes world arguments types
      definitions) :
    ∀ (parameters : List Parameter),
      parameters.map Prod.snd = types →
      EnvironmentGraphHasTypes program world
        (List.zip (parameters.map Prod.fst) (arguments.map Value.ofCore))
        (parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)) definitions := by
  apply Core.RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun environment context relationDefinitions _ =>
        ∀ parameters : List Parameter,
          parameters.map Prod.snd = context →
          EnvironmentGraphHasTypes program world
            (List.zip (parameters.map Prod.fst)
              (environment.map Value.ofCore))
            (parameters.map fun parameter =>
              (parameter.1, StaticType.value parameter.2))
            relationDefinitions)
      (t := typing)
  case unit => intros; trivial
  case bool => intros; trivial
  case word => intros; trivial
  case pair => intros; trivial
  case inLeft => intros; trivial
  case inRight => intros; trivial
  case closure => intros; trivial
  case cellRef => intros; trivial
  case constructed => intros; trivial
  case nil =>
      intro _ parameters parameterTypesEqual
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters => simp at parameterTypesEqual
  case cons =>
      intro _ _ expectedType _ tailContext head _ _ tailIH
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => simp at parameterTypesEqual
      | cons parameter parameters =>
          have headMatch : parameter.2 = expectedType := by
            exact (List.cons.inj parameterTypesEqual).1
          have tailMatch : parameters.map Prod.snd = tailContext :=
            (List.cons.inj parameterTypesEqual).2
          cases parameter with
          | mk id parameterType =>
              cases headMatch
              simpa only [List.map_cons, List.zip_cons_cons] using
                (EnvironmentGraphHasTypes.cons
                  (Value.GraphHasType.ofCore head)
                  (tailIH parameters tailMatch))

/-- The existing deep entry-input certificate supplies the graph evaluator's
named, deeply typed initial parameter environment. -/
theorem CheckedProgram.RuntimeInputsHaveType.boundArgumentsGraph
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions) :
    EnvironmentGraphHasTypes checked.program world
      (List.zip (definition.parameters.map Prod.fst)
        (arguments.map Value.ofCore))
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2)) definitions := by
  exact EnvironmentGraphHasTypes.ofCoreParameters
    typing.argumentsTyping definition.parameters rfl

/-- For an honestly checked program, the same selected definition has a
checked body under the parameter context supplied by the deep input bridge. -/
theorem CheckedProgram.RuntimeInputsHaveType.selectedBodyHasType
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions)
    (checkedBy : checked.program.check = .ok checked) :
    Expr.InfersType checked.program
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2))
      definition.body definition.resultType :=
  Program.IsWellTyped.foundDefinition_hasType
    ⟨checked, checkedBy⟩ typing.found

/-- Ordered deep argument typing before the graph runtime's structural
argument bundling. -/
inductive GraphArgumentsHaveTypes
    (program : Program) (world : Core.StoreTyping) :
    List Value → List Core.Ty →
    (definitions : Core.DataEnvironment := []) → Prop where
  | nil {definitions : Core.DataEnvironment} :
      GraphArgumentsHaveTypes program world [] [] definitions
  | cons {definitions : Core.DataEnvironment}
      {value : Value} {type : Core.Ty}
      {values : List Value} {types : List Core.Ty} :
      Value.GraphHasType program world value type definitions →
      GraphArgumentsHaveTypes program world values types definitions →
      GraphArgumentsHaveTypes program world (value :: values)
        (type :: types) definitions

/-- Packing individually deep arguments preserves their structural bundle
type, including the zero- and one-argument conventions. -/
theorem GraphArgumentsHaveTypes.packValues
    {program : Program} {world : Core.StoreTyping}
    {values : List Value} {types : List Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : GraphArgumentsHaveTypes program world values types
      definitions) :
    Value.GraphHasType program world (packValues values)
      (bundleType types) definitions := by
  induction typing with
  | nil =>
      rename_i relationDefinitions
      simpa [SourceRuntime.packValues, bundleType] using
        (Value.GraphHasType.unit program world relationDefinitions)
  | cons head tail tailIH =>
      cases tail with
      | nil =>
          simpa [SourceRuntime.packValues, bundleType] using head
      | cons next rest =>
          simpa [SourceRuntime.packValues, bundleType] using
            (Value.GraphHasType.pair head tailIH)

/-- Repartitioning a deeply typed structural argument bundle according to a
callee's source binder list preserves deep typing of every extracted value.
This covers the runtime's intentional zero/unit and product/arity erasure. -/
theorem GraphArgumentsHaveTypes.ofUnpackValues
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (parameters : List Parameter) (bundle : Value) (values : List Value)
    (typing : Value.GraphHasType program world bundle
      (parameterType parameters) definitions)
    (unpacked : unpackValues? parameters bundle = some values) :
    GraphArgumentsHaveTypes program world values
      (parameters.map Prod.snd) definitions := by
  induction parameters generalizing bundle values with
  | nil =>
      cases bundle <;> simp [unpackValues?] at unpacked
      cases unpacked
      exact .nil
  | cons parameter parameters ih =>
      cases parameters with
      | nil =>
          simp [unpackValues?] at unpacked
          cases unpacked
          exact .cons (by simpa [parameterType] using typing) .nil
      | cons next rest =>
          cases bundle <;> simp [unpackValues?] at unpacked
          rename_i first remaining
          cases remainingResult : unpackValues? (next :: rest) remaining with
          | none => simp [remainingResult] at unpacked
          | some remainingValues =>
              simp [remainingResult] at unpacked
              cases unpacked
              have pairTyping : Value.GraphHasType program world
                  (.pair first remaining)
                  (.product parameter.2
                    (parameterType (next :: rest))) definitions := by
                simpa [parameterType] using typing
              obtain ⟨firstTyping, remainingTyping⟩ :=
                pairTyping.pairComponents
              exact .cons firstTyping
                (ih remaining remainingValues remainingTyping remainingResult)

/-- Deeply typed normalized arguments supply the callee's named parameter
environment; their source-local identities are recovered from the binder
list. -/
theorem GraphArgumentsHaveTypes.toNamedEnvironment
    {program : Program} {world : Core.StoreTyping}
    {values : List Value} {types : List Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : GraphArgumentsHaveTypes program world values types
      definitions) :
    ∀ (parameters : List Parameter),
      parameters.map Prod.snd = types →
      EnvironmentGraphHasTypes program world
        (List.zip (parameters.map Prod.fst) values)
        (parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)) definitions := by
  induction typing with
  | nil =>
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters => simp at parameterTypesEqual
  | cons head tail tailIH =>
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => simp at parameterTypesEqual
      | cons parameter parameters =>
          have headMatch : parameter.2 = _ :=
            (List.cons.inj parameterTypesEqual).1
          have tailMatch : parameters.map Prod.snd = _ :=
            (List.cons.inj parameterTypesEqual).2
          cases parameter with
          | mk id parameterType =>
              cases headMatch
              simpa only [List.map_cons, List.zip_cons_cons] using
                (EnvironmentGraphHasTypes.cons head
                  (tailIH parameters tailMatch))

/-- A freshly bound parameter prefix can be added to the closure's already
deeply typed lexical environment. -/
theorem EnvironmentGraphHasTypes.append
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {front : Environment} {frontContext : StaticContext}
    (frontTyping : EnvironmentGraphHasTypes program world front
      frontContext definitions) :
    ∀ {back : Environment} {backContext : StaticContext},
      EnvironmentGraphHasTypes program world back backContext definitions →
      EnvironmentGraphHasTypes program world (front ++ back)
        (frontContext ++ backContext) definitions := by
  induction front generalizing frontContext with
  | nil =>
      cases frontTyping
      intro _ _ backTyping
      exact backTyping
  | cons entry rest ih =>
      cases frontTyping with
      | cons head tail =>
          intro _ _ backTyping
          exact .cons head (ih tail backTyping)

/-- The complete lexical environment used by a successful source-closure
call is deeply typed after structural unpacking and parameter binding. -/
theorem EnvironmentGraphHasTypes.ofUnpackedCall
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameters : List Parameter} {bundle : Value}
    {values : List Value} {captured : Environment}
    {context : StaticContext}
    (bundleTyping : Value.GraphHasType program world bundle
      (parameterType parameters) definitions)
    (unpacked : unpackValues? parameters bundle = some values)
    (capturedTyping : EnvironmentGraphHasTypes program world captured
      context definitions) :
    EnvironmentGraphHasTypes program world
      (List.zip (parameters.map Prod.fst) values ++ captured)
      ((parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2)) ++ context)
      definitions := by
  have argumentsTyping := GraphArgumentsHaveTypes.ofUnpackValues
    parameters bundle values bundleTyping unpacked
  have boundTyping := argumentsTyping.toNamedEnvironment parameters rfl
  exact EnvironmentGraphHasTypes.append boundTyping capturedTyping

/-- Looking up a statically typed local in a deeply typed lexical
environment returns a deeply typed runtime value at the erased type. -/
theorem EnvironmentGraphHasTypes.lookup
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    (typing : EnvironmentGraphHasTypes program world environment context
      definitions)
    {id : Resolved.LocalId} {staticType : StaticType}
    (found : lookupStatic? context id = some staticType) :
    ∃ value,
      lookupValue? environment id = some value ∧
      Value.GraphHasType program world value staticType.erase definitions := by
  induction environment generalizing context with
  | nil =>
      cases typing
      simp [lookupStatic?] at found
  | cons entry rest ih =>
      cases typing with
      | cons head tail =>
          rename_i headId headValue headType tailContext
          by_cases same : headId = id
          · subst id
            simp [lookupStatic?] at found
            cases found
            exact ⟨headValue, by simp [lookupValue?], head⟩
          · have tailFound : lookupStatic? tailContext id =
                some staticType := by
              simpa [lookupStatic?, same] using found
            obtain ⟨value, valueFound, valueTyping⟩ :=
              ih tail tailFound
            exact ⟨value,
              by simpa [lookupValue?, same] using valueFound,
              valueTyping⟩

/-- The evaluator induction hypothesis required at a source body call.  It is
separate from the application dispatcher so the closure and global cases can
be proved once and reused by the eventual whole-evaluator induction. -/
def BodyPreservesGraphTyping
    (program : Program)
    (evaluateBody : Environment → Core.Store → Expr → RunResult) : Prop :=
  ∀ {world : Core.StoreTyping} {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store : Core.Store} {expression : Expr} {expected : Core.Ty}
    {value : Value} {finalStore : Core.Store},
    EnvironmentGraphHasTypes program world environment context definitions →
    Expr.InfersType program context expression expected →
    Core.StoreHasTypes world store →
    evaluateBody environment store expression = .done value finalStore →
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions

/-- Pointwise static typing for an ordered expression list, used by the
argument evaluator's sequential preservation proof. -/
inductive ExpressionsHaveTypes (program : Program) (context : StaticContext) :
    List Expr → List Core.Ty → Prop where
  | nil : ExpressionsHaveTypes program context [] []
  | cons {expression : Expr} {type : Core.Ty}
      {expressions : List Expr} {types : List Core.Ty} :
      Expr.InfersType program context expression type →
      ExpressionsHaveTypes program context expressions types →
      ExpressionsHaveTypes program context
        (expression :: expressions) (type :: types)

/-- The executable checker returns precisely the ordered per-expression
certificates consumed by sequential argument preservation. -/
theorem ExpressionsHaveTypes.ofInferList
    (program : Program) (context : StaticContext) :
    ∀ (expressions : List Expr) (staticTypes : List StaticType),
      inferList program context expressions = .ok staticTypes →
      ExpressionsHaveTypes program context expressions
        (staticTypes.map StaticType.erase) := by
  intro expressions
  induction expressions with
  | nil =>
      intro staticTypes success
      simp [inferList] at success
      cases success
      exact .nil
  | cons expression expressions ih =>
      intro staticTypes success
      obtain ⟨head, tail, headOk, tailOk, typesEq⟩ :=
        inferList_cons_ok program context expression expressions
          staticTypes success
      subst staticTypes
      exact .cons ⟨head, headOk, rfl⟩ (ih tail tailOk)

/-- Sequential argument evaluation preserves every deep argument type and
threads a monotone typed heap through each successful expression. -/
theorem ExpressionsHaveTypes.evaluateArguments_done_deep
    {program : Program} {context : StaticContext}
    {expressions : List Expr} {types : List Core.Ty}
    (typing : ExpressionsHaveTypes program context expressions types)
    (evaluateOne : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateOne) :
    ∀ {world : Core.StoreTyping}
      {definitions : Core.DataEnvironment}
      {environment : Environment} {store : Core.Store}
      {values : List Value} {finalStore : Core.Store},
      EnvironmentGraphHasTypes program world environment context definitions →
      Core.StoreHasTypes world store →
      evaluateArguments (evaluateOne environment) store expressions =
        .done values finalStore →
      ∃ finalWorld,
        Core.WorldExtends world finalWorld ∧
        Core.StoreHasTypes finalWorld finalStore ∧
        GraphArgumentsHaveTypes program finalWorld values types definitions := by
  induction typing with
  | nil =>
      intro world definitions environment store values finalStore
        environmentTyping storeTyping completed
      have completed' : ArgumentsResult.done [] store =
          .done values finalStore := by
        simpa [evaluateArguments] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping, .nil⟩
  | cons expressionTyping tailTyping tailIH =>
      intro world definitions environment store values finalStore
        environmentTyping storeTyping completed
      rename_i headExpression headType tailExpressions tailTypes
      cases headRun : evaluateOne environment store headExpression with
      | outOfFuel nextStore =>
          unfold evaluateArguments at completed
          rw [headRun] at completed
          cases completed
      | fault error nextStore =>
          unfold evaluateArguments at completed
          rw [headRun] at completed
          cases completed
      | done headValue nextStore =>
          obtain ⟨middleWorld, firstExtension, nextStoreTyping,
            headTyping⟩ :=
            bodyPreservation environmentTyping expressionTyping
              storeTyping headRun
          have nextEnvironmentTyping :=
            EnvironmentGraphHasTypes.weaken firstExtension
              environmentTyping
          cases tailRun : evaluateArguments (evaluateOne environment)
              nextStore tailExpressions with
          | outOfFuel doneStore =>
              unfold evaluateArguments at completed
              rw [headRun] at completed
              dsimp at completed
              rw [tailRun] at completed
              cases completed
          | fault error doneStore =>
              unfold evaluateArguments at completed
              rw [headRun] at completed
              dsimp at completed
              rw [tailRun] at completed
              cases completed
          | done tailValues doneStore =>
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                tailValuesTyping⟩ :=
                tailIH nextEnvironmentTyping nextStoreTyping tailRun
              have completed' : ArgumentsResult.done
                  (headValue :: tailValues) doneStore =
                  .done values finalStore := by
                simpa only [evaluateArguments, headRun, tailRun]
                  using completed
              cases completed'
              exact ⟨finalWorld, firstExtension.trans secondExtension,
                finalStoreTyping,
                .cons (headTyping.weaken secondExtension) tailValuesTyping⟩

/-- Source-closure application preserves deep result and heap typing assuming
the recursive body evaluator satisfies its induction contract. -/
theorem applyValue_sourceClosure_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameters : List Parameter} {resultType : Core.Ty}
    {body : Expr} {captured : Environment}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (functionTyping : Value.GraphHasType program world
      (.closure parameters resultType body captured)
      (.function (parameterType parameters) resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) (parameterType parameters) definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel
      (.closure parameters resultType body captured)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  cases functionTyping with
  | core projection _ _ =>
      simp [Value.toCore?] at projection
  | sourceClosure capturedTyping bodyTyping =>
      rename_i context
      have argumentTag := argumentTyping.hasType
      simp only [Value.HasType] at argumentTag
      cases unpacked : unpackValues? parameters (packValues arguments) with
      | none =>
          simp [applyValue, argumentTag, unpacked] at completed
          split at completed <;> contradiction
      | some normalized =>
          have environmentTyping : EnvironmentGraphHasTypes program world
              (bindParameters parameters normalized captured)
              ((parameters.map fun parameter =>
                (parameter.1, StaticType.value parameter.2)) ++ context)
              definitions := by
            simpa [bindParameters] using
              (EnvironmentGraphHasTypes.ofUnpackedCall argumentTyping
                unpacked capturedTyping)
          cases bodyRun : evaluateBody
              (bindParameters parameters normalized captured)
              initialStore body with
          | outOfFuel store =>
              simp [applyValue, argumentTag, unpacked, bodyRun]
                at completed
              split at completed <;> contradiction
          | fault error store =>
              simp [applyValue, argumentTag, unpacked, bodyRun]
                at completed
              split at completed <;> contradiction
          | done bodyValue bodyStore =>
              obtain ⟨finalWorld, extension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation environmentTyping bodyTyping storeTyping
                  bodyRun
              have resultTag := resultTyping.hasType
              simp only [Value.HasType] at resultTag
              simp [applyValue, argumentTag, unpacked, bodyRun,
                resultTag] at completed
              split at completed
              · contradiction
              cases completed
              exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- The named-global application branch uses the checker-certified selected
body and a deeply typed fresh parameter environment. -/
theorem applyValue_global_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {key : Key} {definition : Definition}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (wellTyped : program.IsWellTyped)
    (found : program.findDefinition? key = some definition)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) (parameterType definition.parameters)
      definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel (.global key)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value definition.resultType
        definitions := by
  have bodyTyping := wellTyped.foundDefinition_hasType found
  have argumentTag := argumentTyping.hasType
  simp only [Value.HasType] at argumentTag
  cases unpacked : unpackValues? definition.parameters
      (packValues arguments) with
  | none =>
      simp [applyValue, found, argumentTag, unpacked] at completed
      split at completed <;> contradiction
  | some normalized =>
      have environmentTyping : EnvironmentGraphHasTypes program world
          (bindParameters definition.parameters normalized [])
          (definition.parameters.map fun parameter =>
            (parameter.1, StaticType.value parameter.2)) definitions := by
        simpa [bindParameters] using
          (EnvironmentGraphHasTypes.ofUnpackedCall argumentTyping
            unpacked (EnvironmentGraphHasTypes.nil
              (program := program) (world := world)))
      cases bodyRun : evaluateBody
          (bindParameters definition.parameters normalized [])
          initialStore definition.body with
      | outOfFuel store =>
          simp [applyValue, found, argumentTag, unpacked, bodyRun]
            at completed
          split at completed <;> contradiction
      | fault error store =>
          simp [applyValue, found, argumentTag, unpacked, bodyRun]
            at completed
          split at completed <;> contradiction
      | done bodyValue bodyStore =>
          obtain ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩ :=
            bodyPreservation environmentTyping bodyTyping storeTyping bodyRun
          have resultTag := resultTyping.hasType
          simp only [Value.HasType] at resultTag
          simp [applyValue, found, argumentTag, unpacked, bodyRun,
            resultTag] at completed
          split at completed
          · contradiction
          cases completed
          exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- All successful graph application dispatch branches preserve deep typing.
The source-body contract is used only for source closures and named globals;
embedded Core closures use Core's own preservation theorem. -/
theorem applyValue_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {functionValue : Value} {argumentType resultType : Core.Ty}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (wellTyped : program.IsWellTyped)
    (functionTyping : Value.GraphHasType program world functionValue
      (.function argumentType resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) argumentType definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel functionValue
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  have functionTag := functionTyping.hasType
  simp only [Value.HasType] at functionTag
  cases functionValue with
  | closure parameters declaredResult body captured =>
      change some (Core.Ty.function (parameterType parameters)
        declaredResult) =
        some (Core.Ty.function argumentType resultType) at functionTag
      have functionEq := Option.some.inj functionTag
      cases functionEq
      exact applyValue_sourceClosure_done_deep evaluateBody
        bodyPreservation functionTyping argumentTyping storeTyping completed
  | global key =>
      cases found : program.findDefinition? key with
      | none => simp [applyValue, found] at completed
      | some definition =>
          change (program.findSignature? key).map Signature.toCoreType =
            some (.function argumentType resultType) at functionTag
          rw [Program.findSignature?, found] at functionTag
          simp only [Option.map_some] at functionTag
          have functionEq := Option.some.inj functionTag
          have functionEq' : Core.Ty.function
              (bundleType (definition.parameters.map Prod.snd))
              definition.resultType =
              .function argumentType resultType := by
            simpa [Definition.signature, Signature.toCoreType] using
              functionEq
          injection functionEq' with inputEq outputEq
          have parameterEq : parameterType definition.parameters =
              argumentType := by
            rw [parameterType_eq_bundleType_map]
            exact inputEq
          have resultEq : definition.resultType = resultType := by
            exact outputEq
          cases parameterEq
          cases resultEq
          exact applyValue_global_done_deep evaluateBody
            bodyPreservation wellTyped found argumentTyping storeTyping
            completed
  | coreClosure parameter declaredResult body captured =>
      change some (Core.Ty.function parameter declaredResult) =
        some (Core.Ty.function argumentType resultType) at functionTag
      have functionEq := Option.some.inj functionTag
      cases functionEq
      exact applyValue_coreClosure_done_deep evaluateBody functionTyping
        argumentTyping storeTyping completed
  | unit => simp [applyValue] at completed
  | bool _ => simp [applyValue] at completed
  | word _ => simp [applyValue] at completed
  | hostFunction _ => simp [applyValue] at completed
  | pair _ _ => simp [applyValue] at completed
  | inLeft _ _ => simp [applyValue] at completed
  | inRight _ _ => simp [applyValue] at completed
  | cellRef _ _ => simp [applyValue] at completed
  | constructed _ _ => simp [applyValue] at completed

/-- The local-variable evaluator case uses the same keyed lookup certified by
the static context, so it cannot return an untyped captured value. -/
theorem evaluate_local_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {id : Resolved.LocalId}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.local id) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.local id) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  cases staticFound : lookupStatic? context id with
  | none => simp [infer, staticFound] at inferredAt
  | some staticType =>
      simp [infer, staticFound] at inferredAt
      cases inferredAt
      obtain ⟨foundValue, valueFound, valueTyping⟩ :=
        environmentTyping.lookup staticFound
      cases fuel with
      | zero => simp [evaluate] at completed
      | succ remaining =>
          have completed' : RunResult.done foundValue store =
              .done value finalStore := by
            simpa [evaluate, valueFound] using completed
          cases completed'
          exact ⟨world, .refl world, storeTyping,
            by simpa [resultType] using valueTyping⟩

theorem evaluate_unit_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context .unit expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store .unit =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .unit := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done .unit store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.unit program world definitions⟩

theorem evaluate_bool_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {literal : Bool}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.bool literal) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.bool literal) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .bool := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done (.bool literal) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.bool program world literal definitions⟩

theorem evaluate_word_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {literal : Core.Word}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.word literal) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.word literal) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .word := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done (.word literal) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.word program world literal definitions⟩

/-- A successfully resolved global evaluates to a deeply typed finite-graph
reference, provided the entire table was genuinely checked. -/
theorem evaluate_global_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {key : Key}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (wellTyped : program.IsWellTyped)
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.global key) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.global key) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  cases signatureFound : program.findSignature? key with
  | none => simp [infer, signatureFound] at inferredAt
  | some signature =>
      simp [infer, signatureFound] at inferredAt
      cases inferredAt
      have expectedEq : expected = signature.toCoreType := by
        simpa [StaticType.erase, Signature.toCoreType] using resultType.symm
      subst expected
      cases fuel with
      | zero => simp [evaluate] at completed
      | succ remaining =>
          cases found : program.findDefinition? key with
          | none =>
              simp [Program.findSignature?, found] at signatureFound
          | some definition =>
              have completed' : RunResult.done (.global key) store =
                  .done value finalStore := by
                simpa [evaluate, found] using completed
              cases completed'
              exact ⟨world, .refl world, storeTyping,
                Value.GraphHasType.global wellTyped signatureFound⟩

/-- Evaluating a statically checked source lambda builds a deeply typed
closure with its checked body and deeply typed lexical capture. -/
theorem evaluate_lambda_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {parameters : List Parameter} {resultType : Core.Ty}
    {body : Expr} {expected : Core.Ty}
    {value : Value} {fuel : Nat}
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context
      (.lambda parameters resultType body) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store
      (.lambda parameters resultType body) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨bodyTyping, expectedEq⟩ := staticTyping.lambda_body
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done
          (.closure parameters resultType body environment) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.sourceClosure environmentTyping bodyTyping⟩

/-- The actual `let` evaluator branch composes two recursive preservation
steps while carrying the heap-world extension and weakening the captured
environment between them. -/
theorem evaluate_let_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {binder : Resolved.LocalId} {boundExpression body : Expr}
    {inferred : StaticType} {expected : Core.Ty}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (boundTyping : Expr.InfersType program context boundExpression
      inferred.erase)
    (bodyTyping : Expr.InfersType program ((binder, inferred) :: context)
      body expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.letE binder boundExpression body) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  cases boundRun : evaluate fuel program environment store boundExpression with
  | outOfFuel nextStore =>
      simp [evaluate, boundRun] at completed
  | fault error nextStore =>
      simp [evaluate, boundRun] at completed
  | done boundValue bodyStore =>
      obtain ⟨bodyWorld, firstExtension, bodyStoreTyping,
        boundValueTyping⟩ :=
        bodyPreservation environmentTyping boundTyping storeTyping boundRun
      have capturedTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      have extendedTyping : EnvironmentGraphHasTypes program bodyWorld
          ((binder, boundValue) :: environment)
          ((binder, inferred) :: context) definitions :=
        .cons boundValueTyping capturedTyping
      have bodyRun : evaluate fuel program
          ((binder, boundValue) :: environment) bodyStore body =
          .done value finalStore := by
        simpa [evaluate, boundRun] using completed
      obtain ⟨finalWorld, secondExtension, finalStoreTyping,
        resultTyping⟩ :=
        bodyPreservation extendedTyping bodyTyping bodyStoreTyping bodyRun
      exact ⟨finalWorld, firstExtension.trans secondExtension,
        finalStoreTyping, resultTyping⟩

/-- Pair evaluation preserves deep typing across its left-to-right store
threading, including heap references captured by the left component. -/
theorem evaluate_pair_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {left right : Expr} {leftType rightType : Core.Ty}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left leftType)
    (rightTyping : Expr.InfersType program context right rightType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.pair left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value
        (.product leftType rightType) definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases rightRun : evaluate fuel program environment rightStore right with
      | outOfFuel nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | fault error nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | done rightValue pairStore =>
          obtain ⟨finalWorld, secondExtension, pairStoreTyping,
            rightValueTyping⟩ :=
            bodyPreservation nextEnvironmentTyping rightTyping
              rightStoreTyping rightRun
          have completed' : RunResult.done (.pair leftValue rightValue)
              pairStore = .done value finalStore := by
            simpa [evaluate, leftRun, rightRun] using completed
          cases completed'
          exact ⟨finalWorld, firstExtension.trans secondExtension,
            pairStoreTyping,
            .pair (leftValueTyping.weaken secondExtension)
              rightValueTyping⟩

/-- The actual graph `apply` evaluator branch composes deep function
evaluation, ordered argument evaluation, structural argument bundling, and
the three typed application-dispatch branches. -/
theorem evaluate_apply_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {function : Expr} {arguments : List Expr}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (wellTyped : program.IsWellTyped)
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context
      (.apply function arguments) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.apply function arguments) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨functionType, argumentTypes, parameterType, resultType,
    functionInferred, argumentsInferred, functionErased, bundleEqual,
    resultEqual⟩ := staticTyping.apply_components
  have functionStatic : Expr.InfersType program context function
      (.function parameterType resultType) :=
    ⟨functionType, functionInferred, functionErased⟩
  have argumentsStatic := ExpressionsHaveTypes.ofInferList program context
    arguments argumentTypes argumentsInferred
  cases functionRun : evaluate fuel program environment store function with
  | outOfFuel nextStore =>
      simp [evaluate, functionRun] at completed
  | fault error nextStore =>
      simp [evaluate, functionRun] at completed
  | done functionValue argumentsStore =>
      obtain ⟨functionWorld, firstExtension, argumentsStoreTyping,
        functionValueTyping⟩ :=
        bodyPreservation environmentTyping functionStatic storeTyping
          functionRun
      have argumentsEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases argumentsRun : evaluateArguments
          (evaluate fuel program environment) argumentsStore arguments with
      | outOfFuel nextStore =>
          simp [evaluate, functionRun, argumentsRun] at completed
      | fault error nextStore =>
          simp [evaluate, functionRun, argumentsRun] at completed
      | done argumentValues callStore =>
          obtain ⟨argumentsWorld, secondExtension, callStoreTyping,
            argumentValuesTyping⟩ :=
            argumentsStatic.evaluateArguments_done_deep
              (evaluate fuel program) bodyPreservation
              argumentsEnvironmentTyping argumentsStoreTyping argumentsRun
          have callableTyping := functionValueTyping.weaken secondExtension
          have bundledTyping : Value.GraphHasType program argumentsWorld
              (packValues argumentValues) parameterType definitions := by
            simpa [bundleEqual] using argumentValuesTyping.packValues
          have applied : applyValue program (evaluate fuel program) fuel
              functionValue argumentValues callStore =
              .done value finalStore := by
            simpa [evaluate, functionRun, argumentsRun] using completed
          obtain ⟨finalWorld, thirdExtension, finalStoreTyping,
            resultTyping⟩ :=
            applyValue_done_deep (evaluate fuel program) bodyPreservation
              wellTyped callableTyping bundledTyping callStoreTyping applied
          exact ⟨finalWorld,
            firstExtension.trans (secondExtension.trans thirdExtension),
            finalStoreTyping, by simpa [resultEqual] using resultTyping⟩

/-- Unary evaluation preserves deep typing after a successful Core
projection and primitive operation. -/
theorem evaluate_unary_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {op : Core.UnaryOp} {operand : Expr}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (operandTyping : Expr.InfersType program context operand op.operandType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.unary op operand) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value op.resultType definitions := by
  cases operandRun : evaluate fuel program environment store operand with
  | outOfFuel nextStore =>
      simp [evaluate, operandRun] at completed
  | fault error nextStore =>
      simp [evaluate, operandRun] at completed
  | done operandValue operandStore =>
      obtain ⟨finalWorld, extension, finalStoreTyping,
        operandValueTyping⟩ :=
        bodyPreservation environmentTyping operandTyping storeTyping
          operandRun
      cases projected : operandValue.toCore? with
      | none =>
          simp [evaluate, operandRun, projected] at completed
      | some coreOperand =>
          have coreOperandTyping := operandValueTyping.toCore projected
          cases applied : op.apply coreOperand with
          | none =>
              simp [evaluate, operandRun, projected, applied] at completed
          | some coreResult =>
              have completed' : RunResult.done (Value.ofCore coreResult)
                  operandStore = .done value finalStore := by
                simpa [evaluate, operandRun, projected, applied] using
                  completed
              cases completed'
              exact ⟨finalWorld, extension, finalStoreTyping,
                unary_apply_result_graph_type applied⟩

/-- Binary evaluation preserves deep typing while threading the store and
heap-world extension through both operand evaluations. -/
theorem evaluate_binary_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {op : Core.BinaryOp} {left right : Expr}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left op.leftType)
    (rightTyping : Expr.InfersType program context right op.rightType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.binary op left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value op.resultType definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases rightRun : evaluate fuel program environment rightStore right with
      | outOfFuel nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | fault error nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | done rightValue binaryStore =>
          obtain ⟨finalWorld, secondExtension, binaryStoreTyping,
            rightValueTyping⟩ :=
            bodyPreservation nextEnvironmentTyping rightTyping
              rightStoreTyping rightRun
          cases leftProjection : leftValue.toCore? with
          | none =>
              simp [evaluate, leftRun, rightRun, leftProjection] at completed
          | some coreLeft =>
              have coreLeftTyping :=
                (leftValueTyping.weaken secondExtension).toCore leftProjection
              cases rightProjection : rightValue.toCore? with
              | none =>
                  simp [evaluate, leftRun, rightRun, leftProjection,
                    rightProjection] at completed
              | some coreRight =>
                  have coreRightTyping := rightValueTyping.toCore rightProjection
                  cases applied : op.apply coreLeft coreRight with
                  | none =>
                      simp [evaluate, leftRun, rightRun, leftProjection,
                        rightProjection, applied] at completed
                  | some coreResult =>
                      have completed' : RunResult.done (Value.ofCore coreResult)
                          binaryStore = .done value finalStore := by
                        simpa [evaluate, leftRun, rightRun, leftProjection,
                          rightProjection, applied] using completed
                      cases completed'
                      exact ⟨finalWorld,
                        firstExtension.trans secondExtension,
                        binaryStoreTyping,
                        binary_apply_result_graph_type applied⟩

/-- The word-comparison branch preserves the deep result and the sequential
store invariant. -/
theorem evaluate_wordLt_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {left right : Expr} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left .word)
    (rightTyping : Expr.InfersType program context right .word)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.wordLt left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value .bool definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases leftValue with
      | word leftWord =>
          cases rightRun : evaluate fuel program environment rightStore right with
          | outOfFuel nextStore =>
              simp [evaluate, leftRun, rightRun] at completed
          | fault error nextStore =>
              simp [evaluate, leftRun, rightRun] at completed
          | done rightValue comparisonStore =>
              obtain ⟨finalWorld, secondExtension,
                comparisonStoreTyping, rightValueTyping⟩ :=
                bodyPreservation nextEnvironmentTyping rightTyping
                  rightStoreTyping rightRun
              cases rightValue with
              | word rightWord =>
                  have completed' : RunResult.done
                      (.bool (decide (leftWord < rightWord)))
                      comparisonStore = .done value finalStore := by
                    simpa [evaluate, leftRun, rightRun] using completed
                  cases completed'
                  exact ⟨finalWorld, firstExtension.trans secondExtension,
                    comparisonStoreTyping,
                    Value.GraphHasType.bool program finalWorld _ definitions⟩
              | _ => simp [evaluate, leftRun, rightRun] at completed
      | _ => simp [evaluate, leftRun] at completed

/-- A well-typed conditional selects a well-typed branch, preserving the
store/world invariant established while evaluating its condition. -/
theorem evaluate_ifE_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {condition thenBranch elseBranch : Expr}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (conditionTyping : Expr.InfersType program context condition .bool)
    (thenTyping : Expr.InfersType program context thenBranch expected)
    (elseTyping : Expr.InfersType program context elseBranch expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.ifE condition thenBranch elseBranch) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  cases conditionRun : evaluate fuel program environment store condition with
  | outOfFuel nextStore =>
      simp [evaluate, conditionRun] at completed
  | fault error nextStore =>
      simp [evaluate, conditionRun] at completed
  | done conditionValue branchStore =>
      obtain ⟨branchWorld, extension, branchStoreTyping,
        conditionValueTyping⟩ :=
        bodyPreservation environmentTyping conditionTyping storeTyping
          conditionRun
      have branchEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken extension environmentTyping
      cases conditionValue with
      | bool selected =>
          cases selected with
          | false =>
              have branchRun : evaluate fuel program environment branchStore
                  elseBranch = .done value finalStore := by
                simpa [evaluate, conditionRun] using completed
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation branchEnvironmentTyping elseTyping
                  branchStoreTyping branchRun
              exact ⟨finalWorld, extension.trans secondExtension,
                finalStoreTyping, resultTyping⟩
          | true =>
              have branchRun : evaluate fuel program environment branchStore
                  thenBranch = .done value finalStore := by
                simpa [evaluate, conditionRun] using completed
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation branchEnvironmentTyping thenTyping
                  branchStoreTyping branchRun
              exact ⟨finalWorld, extension.trans secondExtension,
                finalStoreTyping, resultTyping⟩
      | _ => simp [evaluate, conditionRun] at completed

/-- Every successful finite-fuel graph evaluation of a statically checked
expression preserves deep value typing and final-store typing.  The proof is
by fuel induction; source closures and globals use the same induction
hypothesis when their bodies are invoked through `applyValue`. -/
theorem evaluate_preserves_graph_type
    (program : Program) (wellTyped : program.IsWellTyped) :
    ∀ fuel, BodyPreservesGraphTyping program (evaluate fuel program) := by
  intro fuel
  induction fuel with
  | zero =>
      intro world definitions environment context store expression expected
        value finalStore environmentTyping staticTyping storeTyping completed
      simp [evaluate] at completed
  | succ remaining ih =>
      intro world definitions environment context store expression expected
        value finalStore environmentTyping staticTyping storeTyping completed
      cases expression with
      | unit =>
          exact evaluate_unit_done_deep environmentTyping staticTyping
            storeTyping completed
      | bool literal =>
          exact evaluate_bool_done_deep environmentTyping staticTyping
            storeTyping completed
      | word literal =>
          exact evaluate_word_done_deep environmentTyping staticTyping
            storeTyping completed
      | «local» id =>
          exact evaluate_local_done_deep environmentTyping staticTyping
            storeTyping completed
      | pair left right =>
          obtain ⟨leftType, rightType, leftTyping, rightTyping,
            expectedEq⟩ := staticTyping.pair_components
          subst expected
          exact evaluate_pair_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | unary op operand =>
          obtain ⟨operandTyping, expectedEq⟩ :=
            staticTyping.unary_components
          subst expected
          exact evaluate_unary_done_deep ih environmentTyping operandTyping
            storeTyping completed
      | binary op left right =>
          obtain ⟨leftTyping, rightTyping, expectedEq⟩ :=
            staticTyping.binary_components
          subst expected
          exact evaluate_binary_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | wordLt left right =>
          obtain ⟨leftTyping, rightTyping, expectedEq⟩ :=
            staticTyping.wordLt_components
          subst expected
          exact evaluate_wordLt_done_deep ih environmentTyping leftTyping
            rightTyping storeTyping completed
      | letE binder bound body =>
          obtain ⟨boundType, boundTyping, bodyTyping⟩ :=
            staticTyping.letE_components
          exact evaluate_let_done_deep ih environmentTyping boundTyping
            bodyTyping storeTyping completed
      | ifE condition thenBranch elseBranch =>
          obtain ⟨conditionTyping, thenTyping, elseTyping⟩ :=
            staticTyping.ifE_components
          exact evaluate_ifE_done_deep ih environmentTyping conditionTyping
            thenTyping elseTyping storeTyping completed
      | global key =>
          exact evaluate_global_done_deep wellTyped environmentTyping
            staticTyping storeTyping completed
      | lambda parameters resultType body =>
          exact evaluate_lambda_done_deep environmentTyping staticTyping
            storeTyping completed
      | apply function arguments =>
          exact evaluate_apply_done_deep ih wellTyped environmentTyping
            staticTyping storeTyping completed

end Solcore.Frontend.SourceRuntime
