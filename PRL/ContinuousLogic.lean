/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Real.NNReal

namespace FirstOrderContinuous

/-! ### Languages and Structures -/


-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint checkUnivs]
structure Language where
  Sorts : ℕ → NNReal → Type u
  Functions : Π n : ℕ, (Fin n → ℕ) → Type v
  Relations : ℕ → Type z


end FirstOrderContinuous
