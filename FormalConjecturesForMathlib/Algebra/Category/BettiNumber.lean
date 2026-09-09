/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import Mathlib

/-!

# The Betti Number of Module

In this file we define Betti number for module over local ring.

# TODO

Define Betti number for graded module (for graded resolution).

-/

universe u

open CategoryTheory Abelian

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

noncomputable instance (M : ModuleCat.{u} R) (i : ℕ) :
    Module (ResidueField R) (Ext M (ModuleCat.of R (ResidueField R)) i) :=
  Module.IsTorsionBySet.module (fun x r ↦ (by sorry))

instance (M : ModuleCat.{u} R) (i : ℕ) :
    IsScalarTower R (ResidueField R) (Ext M (ModuleCat.of R (ResidueField R)) i) :=
  Module.IsTorsionBySet.isScalarTower _

noncomputable def bettiNumber (M : ModuleCat.{u} R) (i : ℕ) : Cardinal.{u} :=
    Module.rank (ResidueField R) (Ext M (ModuleCat.of R (ResidueField R)) i)

lemma bettiNumber_le_rank (M : ModuleCat.{u} R) (P : ProjectiveResolution M) (i : ℕ) :
    bettiNumber M i ≤ Module.rank R (P.complex.X i) := by
  sorry

end IsLocalRing
