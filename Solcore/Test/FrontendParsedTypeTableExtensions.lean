import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction

/-! Caller dictionaries preserve exact parsed compilation only when their
first-match meanings persist. Mutual preservation includes rejection; adding
an unknown nominal meaning can instead enable compilation without any value. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def base : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩), (["Bool"], .bool),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Pkg.Token"], .word), (["Word"], .word), (["Opaque"], .bool)]
private def clean : TypeNameTable := [(["Word"], .word), (["Pkg.Token"], .word),
  (["Pkg", "Token"], .namedData ⟨92⟩), (["Bool"], .bool), (["Opaque"], .namedData ⟨91⟩)]
private def extras : TypeNameTable :=
  [(["Opaque"], .bool), (["Unknown"], .namedData ⟨93⟩), (["Pkg", "Extra"], .unit)]
private def owners : List Resolved.DeclarationId :=
  [⟨⟨.main, ⟨[⟨"TypeExtensions", by decide⟩], by decide⟩⟩, 7⟩,
    ⟨⟨.main, ⟨[⟨"OtherTypes", by decide⟩], by decide⟩⟩, 41⟩]
private def rows (inputs : LocalTypeInputs) : List (String × Resolved.LocalId × Core.Ty) :=
  inputs.bindings.map fun row => (row.name, row.id, row.type)
private def projection (compiled : CompiledRuntimeFunction) :
    Core.Expr × Core.Ty × List (String × Resolved.LocalId × Core.Ty) :=
  (compiled.core, compiled.returnType, rows compiled.inputs)

private theorem cleanedLookup (key : List String) :
    TypeNameTable.lookup? base key = TypeNameTable.lookup? clean key := by
  by_cases nominalKey : ["Opaque"] = key
  · subst key; rfl
  by_cases flag : ["Bool"] = key
  · subst key; rfl
  by_cases qualified : ["Pkg", "Token"] = key
  · subst key; rfl
  by_cases flattened : ["Pkg.Token"] = key
  · subst key; rfl
  by_cases word : ["Word"] = key
  · subst key; rfl
  simp [base, clean, TypeNameTable.lookup?, nominalKey, flag, qualified, flattened, word]

private theorem extendsOfLookupEquality {old next : TypeNameTable}
    (same : ∀ key, TypeNameTable.lookup? old key = TypeNameTable.lookup? next key) :
    TypeNameTable.Extends old next := by
  intro key type found
  exact TypeNameTable.lookup?_iff.mp ((same key).symm.trans (TypeNameTable.lookup?_iff.mpr found))

private theorem samePrepend {table : TypeNameTable} {key : List String} {type : Core.Ty}
    (present : TypeNameTable.Lookup table key type) :
    TypeNameTable.Extends table ((key, type) :: table) ∧
      TypeNameTable.Extends ((key, type) :: table) table := by
  constructor
  · intro selected actual found
    by_cases same : key = selected
    · subst selected
      cases found.type_unique present
      exact .head
    · exact .tail same found
  · intro selected actual found
    cases found with
    | head => exact present
    | tail _ original => exact original

private theorem changedMeaning {old next : TypeNameTable} {key : List String}
    {before after : Core.Ty} (original : TypeNameTable.Lookup old key before)
    (changed : TypeNameTable.Lookup next key after) (different : before ≠ after) :
    ¬ TypeNameTable.Extends old next := fun extension => different ((extension original).type_unique changed)

private theorem preserveTail {old next : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom old owner initial parameters final)
    (extension : TypeNameTable.Extends old next) (parameter : Syntax.FunctionParameter)
    (rest : List Syntax.FunctionParameter) (atHead : parameters = parameter :: rest) :
    ∃ extendedInitial, extendedInitial.bindings ≠ [] ∧
      RuntimeParametersDeclareFrom old owner extendedInitial rest final ∧
      RuntimeParametersDeclareFrom next owner extendedInitial rest final := by
  subst parameters
  cases declared with
  | cons meaning unused tail =>
      exact ⟨_, by simp [LocalTypeInputs.bindFresh], tail, tail.extend_types extension⟩

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-type-extensions.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"lexer invariant: {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")

private def annotations (source : Syntax.FunctionDecl) : List Syntax.TypeExpr :=
  source.value.signature.parameters.elements.filterMap (fun parameter => match parameter.value with
    | .typed _ _ annotation => some annotation
    | _ => none) ++ (source.value.signature.returnsClause.map (·.types.elements)).getD []

private def preserveMeaning {old next : TypeNameTable} (extension : TypeNameTable.Extends old next)
    (annotation : Syntax.TypeExpr) : IO Unit := do
  match accepted : interpretTypeName? old annotation with
  | none => pure ()
  | some type =>
      have _ := (interpretTypeName?_sound accepted).extend_types extension
      have _ := interpretTypeName?_some_of_extends extension accepted
      assertTrue (decide (interpretTypeName? next annotation = some type)) "a successful annotation meaning changed"

private def preserve {old next : TypeNameTable} (extension : TypeNameTable.Extends old next)
    (source : Syntax.FunctionDecl) (core : Core.Expr) (type : Core.Ty) (parameterTypes : List Core.Ty) : IO Unit := do
  for annotation in annotations source do preserveMeaning extension annotation
  for owner in owners do
    match accepted : compileRuntimeFunction? old owner source with
    | none => throw (IO.userError "positive source did not compile under its original dictionary")
    | some compiled =>
        let provenance := compileRuntimeFunction?_sound accepted
        have _ := provenance.header.returnsMeaning.extend_types extension
        have _ := provenance.header.extend_types extension
        have _ := RuntimeParametersDeclareFrom.extend_types provenance.parameters extension
        have _ := RuntimeParametersDeclare.extend_types provenance.parameters extension
        have _ := declareRuntimeParameters?_some_of_extends extension provenance.parameters.complete
        match atHead : source.value.signature.parameters.elements with
        | [] => pure ()
        | parameter :: rest =>
            have _ := preserveTail provenance.parameters extension parameter rest atHead
            pure ()
        let transported := provenance.extend_types extension
        have exact := compileRuntimeFunction?_some_of_extends extension accepted
        have _ := transported.complete
        match nextAt : compileRuntimeFunction? next owner source with
        | none => throw (IO.userError "meaning extension lost a successful whole entry")
        | some changed =>
            have _ : changed = compiled := Option.some.inj (nextAt.symm.trans exact)
            assertTrue (decide (projection changed = projection compiled ∧ changed.inputs.ids = compiled.inputs.ids ∧
              changed.core = core ∧ changed.returnType = type ∧
              changed.inputs.context.values = parameterTypes.reverse)) "extension did not retain the complete compiled record"

private def checkMutual {old next : TypeNameTable} (forward : TypeNameTable.Extends old next)
    (backward : TypeNameTable.Extends next old) (source : Syntax.FunctionDecl) : IO Unit := do
  for key in [["Opaque"], ["Bool"], ["Word"], ["Pkg", "Token"], ["Pkg.Token"], ["Token", "Pkg"], ["Unknown"], []] do
    have _ := TypeNameTable.lookup?_eq_of_mutual_extends forward backward key
    assertTrue (decide (TypeNameTable.lookup? old key = TypeNameTable.lookup? next key)) "mutual first-match lookup or absence changed"
  for annotation in annotations source do
    have _ := interpretTypeName?_eq_of_mutual_extends forward backward annotation
    assertTrue (decide (interpretTypeName? old annotation = interpretTypeName? next annotation)) "mutual annotation result changed"
  for owner in owners do
    let parameters := source.value.signature.parameters.elements
    have _ := declareRuntimeParameters?_eq_of_mutual_extends forward backward owner parameters
    have _ := compileRuntimeFunction?_eq_of_mutual_extends forward backward owner source
    assertTrue (decide ((declareRuntimeParameters? old owner parameters).map rows =
      (declareRuntimeParameters? next owner parameters).map rows ∧
      (compileRuntimeFunction? old owner source).map projection = (compileRuntimeFunction? next owner source).map projection))
      "mutual extension failed to preserve a complete optional result"

def frontendParsedTypeTableExtensionTests : IO Unit := do
  let cleaned : TypeNameTable.Extends base clean := extendsOfLookupEquality cleanedLookup
  let restored : TypeNameTable.Extends clean base := extendsOfLookupEquality (fun key => (cleanedLookup key).symm)
  let same := samePrepend (show TypeNameTable.Lookup base ["Opaque"] (.namedData ⟨91⟩) from .head)
  let appended : TypeNameTable.Extends base (base ++ extras) := TypeNameTable.Extends.append_right base extras
  let fresh : TypeNameTable.Extends (base ++ extras) ((["Fresh"], .unit) :: (base ++ extras)) :=
    TypeNameTable.Extends.cons_fresh (base ++ extras) ["Fresh"] Core.Ty.unit (by decide)
  let extensions : List { next : TypeNameTable // TypeNameTable.Extends base next } :=
    [⟨base, TypeNameTable.Extends.refl base⟩, ⟨base ++ extras, appended⟩,
      ⟨(["Fresh"], .unit) :: (base ++ extras), TypeNameTable.Extends.trans appended fresh⟩,
      ⟨(["Opaque"], .namedData ⟨91⟩) :: base, same.1⟩, ⟨clean, cleaned⟩]
  assertTrue (decide (base ≠ clean ∧ base.length = clean.length + 1 ∧ ["Opaque"] ∈ base.map Prod.fst))
    "pruning/reordering or same-key prepend fixture became trivial"
  let fixtures : List (String × Core.Expr × Core.Ty × List Core.Ty) := [
    ("function nominal(x: Opaque,y: Word) returns (Opaque){return x;}", .var 1, .namedData ⟨91⟩, [.namedData ⟨91⟩, .word]),
    ("function qualified(x: Pkg /* exact components */ . Token) returns (Pkg.Token){return x;}", .var 0, .namedData ⟨92⟩, [.namedData ⟨92⟩]),
    ("function nominal(c: Bool,x: Opaque,y: Opaque) returns (Opaque){if(c){return x;}else{return y;}}",
      .ifE (.var 2) (.var 1) (.var 0), .namedData ⟨91⟩, [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩]),
    ("function unused(x: Opaque){return;}", .unit, .unit, [.namedData ⟨91⟩]),
    ("function bare(c: Bool,x: Opaque){if(c){return;}else{return;}}", .ifE (.var 1) .unit .unit, .unit, [.bool, .namedData ⟨91⟩])]
  for (content, core, type, parameterTypes) in fixtures do
    let some source ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "positive function did not completely parse")
    for extension in extensions do preserve extension.property source core type parameterTypes
    checkMutual cleaned restored source
    checkMutual same.1 same.2 source
  for content in ["function unknown(x: Unknown) returns (Unknown){return x;}",
      "function duplicate(x: Opaque,x: Word) returns (Opaque){return x;}",
      "function unsupported(x: Opaque<Word>) returns (Opaque){return x;}",
      "function generic<T>(x: Opaque) returns (Opaque){return x;}",
      "function many(x: Opaque) returns (Opaque,Opaque){return x;}",
      "function wrong(x: Opaque) returns (Word){return x;}",
      "function invalid(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return missing;}}",
      "function extra(x: Opaque) returns (Opaque){return x;return x;}",
      "function missing(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}}"] do
    let some source ← parsed? (Syntax.Parser.functionDecl .module) content
      | throw (IO.userError "semantic failure did not completely parse")
    for owner in owners do assertTrue (compileRuntimeFunction? base owner source).isNone "expected original rejection changed"
    checkMutual cleaned restored source
    checkMutual same.1 same.2 source
  for content in ["Opaque", "Pkg /* components */ . Token", "Unknown", "Opaque<Bool>", "mapping(Word => Bool)"] do
    let some annotation ← parsed? Syntax.Parser.typeExpr content | throw (IO.userError "complete type did not parse")
    for extension in extensions do preserveMeaning extension.property annotation
    have _ := interpretTypeName?_eq_of_mutual_extends cleaned restored annotation
    assertTrue (decide (interpretTypeName? base annotation = interpretTypeName? clean annotation)) "full type Option result changed"
  let some qualified ← parsed? Syntax.Parser.typeExpr "Pkg /* distinguish dotted key */ . Token"
    | throw (IO.userError "qualified type failed to parse")
  let .named name none := qualified.value | throw (IO.userError "qualified named shape changed")
  assertTrue (decide (qualifiedTypeNameKey name = ["Pkg", "Token"] ∧
    interpretTypeName? base qualified = some (.namedData ⟨92⟩) ∧ TypeNameTable.lookup? base ["Pkg.Token"] = some .word))
    "qualified component lists were flattened or reordered"
  let some unknown ← parsed? (Syntax.Parser.functionDecl .module)
      "function enabled(x: Unknown) returns (Unknown){return x;}" | throw (IO.userError "unknown-type entry did not parse")
  for annotation in annotations unknown do
    assertTrue (decide (interpretTypeName? base annotation = none ∧
      interpretTypeName? (base ++ extras) annotation = some (.namedData ⟨93⟩))) "new nominal meaning did not enable unknown annotation"
  for owner in owners do
    assertTrue ((declareRuntimeParameters? base owner unknown.value.signature.parameters.elements).isNone &&
      (compileRuntimeFunction? base owner unknown).isNone) "unknown-name rejection was lost in original table"
    let some compiled := compileRuntimeFunction? (base ++ extras) owner unknown
      | throw (IO.userError "one-way extension failed to enable unknown nominal compilation")
    assertTrue (decide (compiled.core = .var 0 ∧ compiled.returnType = .namedData ⟨93⟩ ∧
      rows compiled.inputs = [("x", ⟨owner, 0⟩, .namedData ⟨93⟩)])) "new nominal compilation fabricated or changed static data"
  let shadow : TypeNameTable := (["Opaque"], .bool) :: base
  have _ : ¬ TypeNameTable.Extends base shadow := changedMeaning (.head) (.head) (by decide)
  let some self ← parsed? (Syntax.Parser.functionDecl .module)
      "function self(x: Opaque) returns (Opaque){return x;}" | throw (IO.userError "shadow contrast did not parse")
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? base owner self).map (·.returnType) = some (.namedData ⟨91⟩) ∧
      (compileRuntimeFunction? shadow owner self).map (·.returnType) = some .bool)) "meaning-changing shadow became exact-record preservation"
  let wrongGuard : TypeNameTable := (["Bool"], .word) :: base
  have _ : ¬ TypeNameTable.Extends base wrongGuard :=
    changedMeaning (.tail (by decide) .head) .head (by decide)
  let some guarded ← parsed? (Syntax.Parser.functionDecl .module)
      "function guard(c: Bool,x: Opaque) returns (Opaque){if(c){return x;}else{return x;}}"
    | throw (IO.userError "guard-shadow contrast did not parse")
  for owner in owners do
    assertTrue ((compileRuntimeFunction? base owner guarded).isSome &&
      (declareRuntimeParameters? wrongGuard owner guarded.value.signature.parameters.elements).isSome &&
      (compileRuntimeFunction? wrongGuard owner guarded).isNone) "changed guard meaning bypassed whole-body typing"
  let dropped : TypeNameTable := [(["Opaque"], .namedData ⟨91⟩)]
  have _ : ¬ TypeNameTable.Extends base dropped := by
    intro extension
    have found : TypeNameTable.Lookup base ["Bool"] .bool := .tail (by decide) .head
    have impossible := TypeNameTable.lookup?_iff.mpr (extension found)
    change none = some Core.Ty.bool at impossible
    cases impossible
  for owner in owners do
    assertTrue (decide ((compileRuntimeFunction? base owner self).map projection =
      (compileRuntimeFunction? dropped owner self).map projection)) "unused live-key deletion changed unrelated source"
  for content in ["function missing(x){return x;}", "function f(x: Opaque){return x;} trailing"] do
    assertTrue (← parsed? (Syntax.Parser.functionDecl .module) content).isNone "dictionary extension affected parser completeness"

end Tests
