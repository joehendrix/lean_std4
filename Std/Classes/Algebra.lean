/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Leonardo de Moura
-/

/-!
This module reintroduces the algebraic class in
@Mathlib.Init.Algebra.Classes@.  It is described in detail on [Github
wiki](https://github.com/leanprover/lean/wiki/Refactoring-structures#encoding-the-algebraic-hierarchy-1)
with pros and cons relevant to Lean 3.

These classes index properties by the operation rather than the type as
in Haskell.
-/

namespace Std

/-- A symmetric operation. -/
class SymmetricOp {α : Type u} {β : Sort v} (op : α → α → β) : Prop where
  /-- Symmetric operation -/
  symm_op : ∀ a b, op a b = op b a

instance (priority := 100) isSymmOp_of_isCommutative {α : Type u} (op : α → α → α)
    [Commutative op] : IsSymmOp op where symm_op := Commutative.comm
