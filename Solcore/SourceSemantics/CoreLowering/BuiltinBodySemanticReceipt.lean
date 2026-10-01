import Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyCertificates

/-! Static evidence consumed by the concrete builtin body semantics.
Compiler acceptance is retained by the separate production certificate; the
semantic receipt keeps the exact finished code and independent source syntax.
It contains no body execution or child meaning field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
open Core Frontend SourceInference

structure SemanticReceipt (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (fellThrough escaped : Word) (code : Expr) where private mk ::
  projection : values.checked.catalog.project expected = .ok type
  syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected
  flow : Expr
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope true
    statements expected type flow

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
  {fellThrough escaped : Word} {code flow : Expr}

/-- Every field is independent static evidence for this exact source and code.
This factory does not assert a production compiler equation. -/
def SemanticReceipt.of_tree
    (projection : values.checked.catalog.project expected = .ok type)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context true statements expected)
    (emitted : code = CompatibleStatements.finish type flow fellThrough escaped)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values
      source solved reasonAt context scope true statements expected type flow) :
    SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type fellThrough escaped code :=
  ⟨projection, syntaxTree, flow, emitted, tree⟩

/-- The original production receipt supplies all semantic evidence while
continuing to retain its own accepted compiler equation. -/
def Certificate.semantic {policy : SourceCoreLoops.Policy} {fuel : Nat}
    (certificate : Certificate layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
      statements expected type fellThrough escaped code :=
  SemanticReceipt.of_tree certificate.projection certificate.syntaxTree certificate.emitted certificate.tree

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody
