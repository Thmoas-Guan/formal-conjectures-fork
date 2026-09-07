/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib

/-!

# The BEH conjecture

-/

universe u

open CategoryTheory

section MinimalResolution

/-!

# The definition of minimal resolution.

-/

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

def IsMinimalResolution (C : ChainComplex (ModuleCat.{u} R) ℕ) : Prop :=
  ∀ i j : ℕ, (C.d i j).hom.range ≤ (maximalIdeal R) • (⊤ : Submodule R (C.X j))

end IsLocalRing

namespace GradedAlgebra

variable  {ι : Type*}  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

def IsMinimalResolution (C : ChainComplex (ModuleCat.{u} A) ℕ) : Prop :=
  ∀ i j : ℕ, (C.d i j).hom.range ≤
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal • (⊤ : Submodule A (C.X j))

end GradedAlgebra

end MinimalResolution

section BettiNumber

open CategoryTheory.Abelian

variable (R : Type u) [CommRing R] (k : Type u) [CommRing k] [Algebra R k]

noncomputable instance (M : ModuleCat.{u} R) (i : ℕ) : SMul k (Ext M (ModuleCat.of R k) i) where
  smul a x := x.comp (Ext.mk₀ (ModuleCat.ofHom (Algebra.lmul R k a))) (add_zero i)

lemma ext_smul_eq (M : ModuleCat.{u} R) (i : ℕ) (r : R) (x : Ext M (ModuleCat.of R k) i) :
    (algebraMap R k r) • x = r • x := by
  rw [Ext.smul_eq_comp_mk₀]
  change x.comp (Ext.mk₀ (ModuleCat.ofHom (Algebra.lmul R k (algebraMap R k r)))) (add_zero i) = _
  congr
  ext
  simp

noncomputable instance (M : ModuleCat.{u} R) (i : ℕ) : Module k (Ext M (ModuleCat.of R k) i) where
  mul_smul a b x := sorry
  one_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

noncomputable instance (M : ModuleCat.{u} R) (i : ℕ) :
    IsScalarTower R k (Ext M (ModuleCat.of R k) i) where
  smul_assoc a b x := by simp [← ext_smul_eq, smul_smul, Algebra.smul_def']

noncomputable def bettiNumber (M : ModuleCat.{u} R) (i : ℕ) : ℕ :=
    Module.finrank k (Ext M (ModuleCat.of R k) i)

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

theorem bettiNumber_le_rank (M : ModuleCat.{u} R)
    (C : ProjectiveResolution M) (i : ℕ) :
    bettiNumber R (ResidueField R) M ≤ Module.finrank R (C.complex.X i) := by
  sorry

theorem isMinimalResolution_iff_rank_eq_bettiNumber (M : ModuleCat.{u} R)
    (C : ProjectiveResolution M) :
    IsMinimalResolution C.complex ↔
      ∀ i, Module.finrank R (C.complex.X i) = bettiNumber R (ResidueField R) M := by
  sorry

end IsLocalRing

namespace GradedAlgebra

variable {R : Type*} {A : Type u} [Field R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (bij : Function.Bijective (algebraMap R (𝒜 0)))

instance : Algebra A (𝒜 0) := RingHom.toAlgebra (GradedRing.projZeroRingHom' 𝒜)

theorem bettiNumber_le_rank (M : ModuleCat.{u} A)
    (C : ProjectiveResolution M) (i : ℕ) :
    bettiNumber A (𝒜 0) M ≤  Module.finrank A (C.complex.X i) := by
  sorry

theorem isMinimalResolution_iff_rank_eq_bettiNumber (M : ModuleCat.{u} A)
    (C : ProjectiveResolution M) :
    IsMinimalResolution 𝒜 C.complex ↔
      ∀ i, Module.finrank A (C.complex.X i) = bettiNumber A (𝒜 0) M := by
  sorry

end GradedAlgebra

end BettiNumber
