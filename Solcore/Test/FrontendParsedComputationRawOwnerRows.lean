import Solcore.Syntax.Parser.Term
import Solcore.Frontend.ComputationReturnTreeRawOwnerProperties
import Solcore.Frontend.ComputationReturnTreeEvaluationProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationEvaluationRenamingProperties
import Solcore.Frontend.LocalTypeInputs

/-! Raw names and actual rows are deliberately not aligned or repaired.
Original annotations and exposed then bindings do not constrain raw paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRawOwnerRows
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RawOwnerRows",by decide⟩],by decide⟩⟩,132⟩
private def lid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 902},999999⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+20}
private theorem injective : Function.Injective shift := by rintro ⟨a,n⟩ ⟨b,m⟩ same; simpa [shift] using same
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def checkedInputs : LocalTypeInputs := ⟨[⟨"x",lid 7,.word⟩,⟨"c",foreign,.bool⟩,⟨"x",lid 2,.bool⟩],by decide⟩
private def names (duplicate : Bool) : LocalNameTable := checkedInputs.names ++ if duplicate then [("x",lid 7)] else []
private def oldEight : Core.Value := .bool false
private def oldNine : Core.Value := .cellRef .word 700
private def env (reordered : Bool) (c : Bool) (v : Core.Value) : Resolved.Environment :=
  let rows := [(lid 8,oldEight),(foreign,.bool c),(lid 7,v),(lid 7,.word (Core.Word.ofNatModulo 99)),(lid 9,oldNine)]
  if reordered then rows.reverse else rows
private def payloads : List Core.Value := [.word (Core.Word.ofNatModulo 14),.bool true,.cellRef .word 701,
  .closure .word .word (.var 0) [.cellRef .word 702,.bool false]]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-raw-owner-rows.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok b next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "parser")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (b.span=⟨file.id,0,text.utf8ByteSize⟩)) "original full source range"
  return b
private structure Atom (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, RecursiveLocalComputationEvaluatesWithCost table environment store s value store 1
private def atom (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Expr) : IO (Atom table environment s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : environment.lookup? id with
      | some v => return ⟨v,fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "missing actual row")
    | none => throw (IO.userError "missing name")
  | _ => throw (IO.userError "original raw atom")
private structure Raw (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Block) where
  value : Core.Value
  cost : Nat
  introduced : List (Resolved.LocalId × Core.Value)
  evidence : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost owner table environment store s value store cost
private def raw (table : LocalNameTable) (environment : Resolved.Environment) (s : Syntax.Block) : IO (Raw table environment s) := do
  check (s.value.all fun st => s.span.contains st.span) "original statement spans"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let a ← atom table environment e; return ⟨a.value,1,[],fun st => by rw [shape]; exact .expression (a.evidence st)⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← raw table environment ⟨span,statements⟩; return ⟨r.value,r.cost,r.introduced,fun st => by rw [shape]; exact .block (r.evidence st)⟩
  | ⟨span,⟨ls,.letDecl name annotation (some e)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains e.span && decide (name.span.endByte≤e.span.startByte)) "original initializer order"
      let a ← atom table environment e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let next : Resolved.Environment := (id,a.value)::environment
      check (decide (next.tail=environment ∧ next.lookup? id=some a.value)) "new row prepended without removing old collision"
      let r ← raw ((name.value,id)::table) next ⟨span,rest⟩
      return ⟨r.value,1+r.cost+2,(id,a.value)::r.introduced,fun st => by
        rw [shape]; cases annotation with
        | none => exact .inferred (a.evidence st) (r.evidence st)
        | some _ => exact .binding (a.evidence st) (r.evidence st)⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← atom table environment c
      match cv : a.value with
      | .bool true => let r ← raw table environment yes; return ⟨r.value,1+r.cost+2,r.introduced,fun st => by rw [shape]; exact .ifTrue (cv ▸ a.evidence st) (r.evidence st)⟩
      | .bool false => let r ← raw table environment no; return ⟨r.value,1+r.cost+2,r.introduced,fun st => by rw [shape]; exact .ifFalse (cv ▸ a.evidence st) (r.evidence st)⟩
      | _ => throw (IO.userError "raw actual condition")
  | _ => throw (IO.userError "original raw body")
termination_by sizeOf s
private def exercise (s : Syntax.Block) (duplicate reordered c : Bool) (v : Core.Value) : IO Unit := do
  let table := names duplicate; let e := env reordered c v
  let expected := if reordered then Core.Value.word (Core.Word.ofNatModulo 99) else v
  let cost := if c then 13 else 10
  check (decide (table.lookup? "x"=some (lid 7) ∧ e.lookup? (lid 7)=some expected ∧
    e.lookup? (lid 8)=some oldEight ∧ e.lookup? (lid 9)=some oldNine ∧ e.lookup? (lid 2)=none ∧
    Resolved.freshLocalId owner (table.map Prod.snd)=lid 8)) "first duplicate, missing unused row and environment-only fresh collisions"
  check (decide (table.map Prod.snd ≠ e.map Prod.fst ∧
    (LocalNameTable.mapIds relabel table).map Prod.fst=table.map Prod.fst ∧
    (Resolved.LocalScope.mapIds relabel e).values=e.values)) "no row alignment or value reconstruction"
  let r ← raw table e s
  if fixed : r.value=expected ∧ r.cost=cost ∧ r.introduced=[(lid 8,expected),(lid 9,expected)]++(if c then [(lid 10,expected)] else []) then
    for store in [[],[Core.Value.bool false,.cellRef .word 999],payloads] do
      have original : RecursiveComputationReturnTreeEvaluatesWithCost owner table e store s expected store cost := by simpa only [fixed.1,fixed.2.1] using r.evidence store
      have mapped := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mpr original
      have reflected := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp mapped
      have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        (fun left right => left.deterministic right) original reflected
      have ordinary := (computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨cost,original⟩
      have mappedOrdinary := (computationReturnTreeEvaluates_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mpr ordinary
      have _ := (computationReturnTreeEvaluates_mapOwner_iff shift injective
        (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp mappedOrdinary
      have existsExact : ∃ result final count, RecursiveComputationReturnTreeEvaluatesWithCost (shift owner)
          (LocalNameTable.mapIds relabel table) (Resolved.LocalScope.mapIds relabel e) store s result final count ∧
          result=expected ∧ final=store ∧ count=cost := ⟨expected,store,cost,mapped,rfl,rfl,rfl⟩
      have _ := existsExact
      check (decide ((Resolved.LocalScope.mapIds relabel ((lid 8,expected)::(lid 9,expected)::e)).values=
        expected::expected::e.values)) "all old actual rows retained behind new heads"
  else throw (IO.userError "independent original raw value/cost/fresh sequence")
private def naivePositionIsNotRawLookup : IO Unit := do
  let b ← parsed "{return x;}"; let e := env false true (.word (Core.Word.ofNatModulo 14))
  let r ← raw (names true) e b
  check (decide (r.value=.word (Core.Word.ofNatModulo 14) ∧ r.cost=1 ∧
    Core.runStateful 1 (.initial (.var 0) e.values [])=.done oldEight [] ∧ oldEight≠r.value)) "raw ID lookup is not positional Core execution on unaligned rows"
private def missingSelectedRow : IO Unit := do
  let s ← parsed "{return x;}"
  match shape : s with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier _⟩)⟩]⟩ =>
      for store in [[],payloads] do
        have absent : ¬ ∃ value final cost, RecursiveComputationReturnTreeEvaluatesWithCost owner (names true) [] store s value final cost := by
          rintro ⟨value,final,cost,evaluation⟩
          rw [shape] at evaluation
          cases evaluation with
          | expression child => cases child with
            | pure leaf => cases leaf with
              | identifier _ found => cases found
        have noMappedCost : ¬ ∃ value final cost, RecursiveComputationReturnTreeEvaluatesWithCost (shift owner)
            (LocalNameTable.mapIds relabel (names true)) [] store s value final cost := by
          rintro ⟨value,final,cost,evaluation⟩
          exact absent ⟨value,final,cost,(computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective
            (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp evaluation⟩
        have noMappedRaw : ¬ ∃ value final, RecursiveComputationReturnTreeEvaluates (shift owner)
            (LocalNameTable.mapIds relabel (names true)) [] store s value final := by
          rintro ⟨value,final,evaluation⟩
          have original : RecursiveComputationReturnTreeEvaluates owner (names true) [] store s value final :=
            (computationReturnTreeEvaluates_mapOwner_iff shift injective
            (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp evaluation
          obtain ⟨cost,counted⟩ := (computationReturnTreeEvaluates_iff_exists_cost recursiveLocalComputationEvaluates_iff_exists_cost).mp original
          exact absent ⟨value,final,cost,counted⟩
        have _ := noMappedCost; have _ := noMappedRaw
        pure ()
  | _ => throw (IO.userError "original missing-row return shape")
end ParsedComputationRawOwnerRows
open ParsedComputationRawOwnerRows in
def frontendParsedComputationRawOwnerRowTests : IO Unit := do
  let s ← parsed "{let x:Missing=x;let x=x;if(c){let x=x;return x;}else{return x;}}"
  check (decide (elaborateRecursiveComputationReturnTree? [] owner checkedInputs s=none)) "unknown annotation still rejects whole source on independent type inputs"
  for duplicate in [false,true] do
    for reordered in [false,true] do
      for c in [false,true] do
        for v in payloads do exercise s duplicate reordered c v
  let guard ← parsed "{let x=x;let x=x;if(c){let x=x;return x;}else{return x;}}"
  check (decide (elaborateRecursiveComputationReturnTree? [] owner checkedInputs guard=none)) "exposed then shadow still rejects without an annotation"
  exercise guard true true true (.bool false)
  exercise guard true false false (.bool true)
  naivePositionIsNotRawLookup
  missingSelectedRow
end Tests
