/-
CopyRight (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.CategoryTheory.EqualizerCorepresentable
import EllipticCurve.Lemmas
import EllipticCurve.AlgebraicGeometry.OverScheme
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Grassmannian

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module
  `M`. It is defined to be the set of submodules of `M` whose quotient is locally free of rank `k`.
  Note that this indexing is the opposite of some indexing in literature, where this rank would be
  `n-k` instead, where `M=R^n`.

## TODO
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability.

-/

universe u v w

open CategoryTheory Limits TensorProduct Submodule

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

attribute [coe] Grassmannian.toSubmodule
attribute [simp] Grassmannian.rankAtStalk_eq

namespace Grassmannian

variable {R M k}

@[simp] lemma coe_mk (N : Submodule R M) {h₁ h₂ h₃} :
    (⟨N, h₁, h₂, h₃⟩ : G(k, M; R)).toSubmodule = N := rfl

/-- An easier constructor that uses a linear equiv and instances. -/
def mk' (N : Submodule R M) (P : Type*) [AddCommGroup P] [Module R P]
    (e : (M ⧸ N) ≃ₗ[R] P) [Module.Finite R P] [Projective R P]
    (h : ∀ p, rankAtStalk (R := R) P p = k :=
      by intro p; haveI := PrimeSpectrum.nontrivial p; simp) :
    G(k, M; R) where
  toSubmodule := N
  finite_quotient := Module.Finite.equiv e.symm
  projective_quotient := Projective.of_equiv e.symm
  rankAtStalk_eq := fun p ↦ by rw [rankAtStalk_eq_of_equiv e, h]

@[simp] lemma coe_mk' (N : Submodule R M) (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Projective R P] (e : (M ⧸ N) ≃ₗ[R] P)
    (h : ∀ p, rankAtStalk (R := R) P p = k) :
    (mk' N P e h).toSubmodule = N :=
  rfl

variable (N : G(k, M; R))

/-- Copy of an element of the Grassmannian, with a new carrier equal to the old one. Useful to fix
definitional equalities. -/
def copy (N : G(k, M; R)) (N' : Set M) (h : N' = N) : G(k, M; R) :=
  mk' (N.toSubmodule.copy N' h) _ (quotEquivOfEq _ N (N.copy_eq _ _))

/-- Given an isomorphism `M⧸N ↠ R^k`, return an element of `G(k, M; R)`. -/
def ofEquiv (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) : G(k, M; R) :=
  mk' N _ e

@[simp] lemma coe_ofEquiv (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) :
    ofEquiv N e = N :=
  rfl

/-- Given a surjection `M ↠ R^k`, return an element of `G(k, M; R)`. -/
def ofSurjective (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) : G(k, M; R) :=
  ofEquiv _ (f.quotKerEquivOfSurjective hf)

@[simp] lemma coe_ofSurjective (f : M →ₗ[R] (Fin k → R)) (hf : Function.Surjective f) :
    ofSurjective f hf = LinearMap.ker f :=
  rfl

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]

/-- If `M₁` surjects to `M₂`, then there is an induced map `G(k, M₂; R) → G(k, M₁; R)` by
"pulling back" a submodule. -/
def comap (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) (N : G(k, M₂; R)) : G(k, M₁; R) :=
  mk' (N.1.comap f) _ (N.quotientComapLinearEquiv f hf)

@[simp] lemma coe_comap (f : M₁ →ₗ[R] M₂) (hf : Function.Surjective f) (N : G(k, M₂; R)) :
    comap f hf N = N.1.comap f :=
  rfl

/-- If `M₁` and `M₂` are isomorphic, then `G(k, M₁; R) ≃ G(k, M₂; R)`. -/
def congr (e : M₁ ≃ₗ[R] M₂) : G(k, M₁; R) ≃ G(k, M₂; R) where
  toFun N := comap e.symm e.symm.surjective N
  invFun N := comap e e.surjective N
  left_inv N := ext <| by simp [← map_equiv_eq_comap_symm, comap_map_eq]
  right_inv N := ext <| by simp [← map_equiv_eq_comap_symm, map_comap_eq]

@[simp] lemma coe_congr (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) :
    congr e N = N.map e :=
  (map_equiv_eq_comap_symm e N).symm

/-- The quotients of the submodules across `congr` are isomorphic. -/
def quotientCongrLEquiv (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) :
    (M₂ ⧸ (N.congr e : Submodule R M₂)) ≃ₗ[R] M₁ ⧸ (N : Submodule R M₁) :=
  Quotient.equiv _ _ e.symm <| (map_comap_eq _ _).trans <| by simp

@[simp] lemma quotientCongrLEquiv_apply (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) (m : M₂) :
    quotientCongrLEquiv e N (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (e.symm m) := rfl

@[simp] lemma quotientCongrLEquiv_symm_apply (e : M₁ ≃ₗ[R] M₂) (N : G(k, M₁; R)) (m : M₁) :
    (quotientCongrLEquiv e N).symm (Submodule.Quotient.mk m) = Submodule.Quotient.mk (e m) := rfl

variable (R) in
/-- The affine chart corresponding to a chosen `x : R^k → M`, represented by `k` elements in `M`.
It is the quotients `q : M ↠ V` such that the composition `x ∘ q : R^k → V` is an isomorphism. -/
def chart (x : Fin k → M) : Set G(k, M; R) :=
  { N | Function.Bijective (N.mkQ ∘ Fintype.linearCombination R x) }
-- TODO: `chart f` is affine
-- Proof sketch: we have equalizer diagram `chart f → Hom[R-Mod](M,R^k) ⇒ Hom[R-Mod](R^k,R^k)`

section LEquivOfChart

variable {x : Fin k → M} {N : G(k, M; R)} (hn : N ∈ chart R x) (i j : Fin k)

variable (N) in
/-- An element `N ∈ chart R f` produces an isomorphism `M ⧸ N ≃ₗ[R] R^k`. -/
noncomputable def lequivOfChart :
    (M ⧸ (N : Submodule R M)) ≃ₗ[R] (Fin k → R) :=
  (LinearEquiv.ofBijective (N.mkQ ∘ₗ Fintype.linearCombination R x) hn).symm

@[simp] lemma lequivOfChart_symm_apply_single_one :
    (lequivOfChart N hn).symm (Pi.single i 1) = Submodule.Quotient.mk (x i) := by
  simp [lequivOfChart]

@[simp] lemma lequivOfChart_symm_apply_single_one' :
    (lequivOfChart N hn).symm (fun j ↦ Pi.single (M := fun _ ↦ R) i 1 j) =
      Submodule.Quotient.mk (x i) :=
  lequivOfChart_symm_apply_single_one hn i

@[simp] lemma lequivOfChart_apply :
    lequivOfChart N hn (Submodule.Quotient.mk (x i)) = Pi.single i 1 := by
  rw [← lequivOfChart_symm_apply_single_one, LinearEquiv.apply_symm_apply]

@[simp] lemma lequivOfChart_apply_apply :
    lequivOfChart N hn (Submodule.Quotient.mk (x i)) j = if j = i then 1 else 0 := by
  rw [lequivOfChart_apply, Pi.single_apply]

@[simp] lemma ofEquiv_lequivOfChart_eq : ofEquiv N.toSubmodule (lequivOfChart N hn) = N :=
  rfl

end LEquivOfChart

lemma ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R))
    (x : Fin k → M) (hx : ∀ i, e (Submodule.Quotient.mk (x i)) = Pi.single i 1) :
    ofEquiv N e ∈ chart R x := by
  rw [chart, Set.mem_setOf, ← LinearMap.coe_comp]
  convert e.symm.bijective using 1
  refine DFunLike.coe_fn_eq.2 (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| Eq.symm <|
    e.symm_apply_eq.2 ?_)
  simp [hx]

lemma ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q)
    (f : Fin k → M) (hf : ∀ i, q (f i) = Pi.single i 1) :
    ofSurjective q hq ∈ chart R f :=
  ofEquiv_mem_chart _ _ hf

lemma exists_ofEquiv_mem_chart {N : Submodule R M} (e : (M ⧸ N) ≃ₗ[R] (Fin k → R)) :
    ∃ f, ofEquiv N e ∈ chart R f :=
  ⟨_, ofEquiv_mem_chart _ (fun i ↦ (e.symm (Pi.single i 1)).out) fun i ↦ by simp⟩

lemma exists_ofSurjective_mem_chart {q : M →ₗ[R] Fin k → R} (hq : Function.Surjective q) :
    ∃ f, ofSurjective q hq ∈ chart R f :=
  exists_ofEquiv_mem_chart _

lemma congr_mem_chart (x : Fin k → M₁) (N : G(k, M₁; R)) (hn : N ∈ chart R x)
    (e : M₁ ≃ₗ[R] M₂) : N.congr e ∈ chart R (e ∘ x) := by
  convert ofEquiv_mem_chart (quotientCongrLEquiv e N ≪≫ₗ lequivOfChart N hn) (e ∘ x) (by simp)

/-- Given isomorphism `M₁ ≃ₗ[R] M₂`, produce an equivalence of charts. -/
@[simps (isSimp := False)]
def chartCongr (e : M₁ ≃ₗ[R] M₂) (x : Fin k → M₁) (y : Fin k → M₂) (h : e ∘ x = y) :
    chart R x ≃ chart R y where
  toFun N := ⟨N.1.congr e, by simpa [h] using congr_mem_chart _ _ N.2 e⟩
  invFun N := ⟨N.1.congr e.symm, by
    simpa [← h, Function.comp_def] using congr_mem_chart _ _ N.2 e.symm⟩
  left_inv N := by ext; simp
  right_inv N := by ext; simp

@[simp] lemma lequivOfChart_chartCongr (e : M₁ ≃ₗ[R] M₂) (x : Fin k → M₁) (y : Fin k → M₂)
    (h : e ∘ x = y) (N : chart R x) :
    lequivOfChart _ (chartCongr e x y h N).2 =
      quotientCongrLEquiv e N.1 ≪≫ₗ lequivOfChart _ N.2 := by
  refine LinearEquiv.toLinearMap_injective ?_
  rw [lequivOfChart, lequivOfChart, LinearEquiv.coe_trans, LinearEquiv.eq_toLinearMap_symm_comp,
    LinearEquiv.comp_toLinearMap_symm_eq]
  ext
  simp [← h, chartCongr_apply_coe]

variable (A : Type*) [CommRing A] [Algebra R A]

/-- Base change to an `R`-algebra `A`, where `M` is replaced with `A ⊗[R] M`. -/
def baseChange (N : G(k, M; R)) : G(k, A ⊗[R] M; A) :=
  mk' (N.toSubmodule.baseChange A) _ (N.quotientBaseChange A) fun p ↦ by
    rw [rankAtStalk_baseChange, rankAtStalk_eq]

lemma coe_baseChange (N : G(k, M; R)) : baseChange A N = N.toSubmodule.baseChange A := rfl

/-- The quotient of `baseChange` is isomorphic to the base change of the quotient. -/
noncomputable def quotientBaseChangeEquiv (N : G(k, M; R)) :
    (A ⊗[R] M ⧸ (baseChange A N).toSubmodule) ≃ₗ[A] A ⊗[R] (M ⧸ N.toSubmodule) :=
  N.quotientBaseChange A

@[simp] lemma quotientBaseChangeEquiv_apply (N : G(k, M; R)) (a : A) (m : M) :
    quotientBaseChangeEquiv A N (Submodule.Quotient.mk (a ⊗ₜ m)) = a ⊗ₜ Submodule.Quotient.mk m :=
  rfl

@[simp] lemma quotientBaseChangeEquiv_symm_apply (N : G(k, M; R)) (a : A) (m : M) :
    (N.quotientBaseChangeEquiv A).symm (a ⊗ₜ Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (a ⊗ₜ m) :=
  (LinearEquiv.symm_apply_eq _).2 rfl

variable {A} {B : Type*} [CommRing B] [Algebra R B]

/-- Functoriality of Grassmannian in the category of `R`-algebras. Note that given an `R`-algebra
`A`, we replace `M` with `A ⊗[R] M`. The map `f : A →ₐ[R] B` should technically provide an instance
`[Algebra A B]`, but this might cause problems later down the line, so we do not require this
instance in the type signature of the function. Instead, given any instance `[Algebra A B]`, we
later prove that the map is equal to the one induced by `IsScalarTower.toAlgHom R A B : A →ₐ[R] B`.
See `map_val` and `map_eq`.
-/
def map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) : G(k, B ⊗[R] M; B) :=
  letI := f.toAlgebra;
  (baseChange B N).congr (AlgebraTensorModule.cancelBaseChange R A B B M)

lemma coe_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    N.map f = span B (f.toLinearMap.rTensor M '' N) := by
  letI := f.toAlgebra;
  rw [map, coe_congr, coe_baseChange, baseChange_eq_span, map_span, map_coe, ← Set.image_comp,
    AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]
  rfl

lemma coe_map' (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    (N.map f).toSubmodule = .span B ((N.restrictScalars R).map (f.toLinearMap.rTensor M)) :=
  coe_map f N

lemma map_eq [Algebra A B] [IsScalarTower R A B] (N : G(k, A ⊗[R] M; A)) :
    N.map (IsScalarTower.toAlgHom R A B) = (baseChange B N).congr
      (AlgebraTensorModule.cancelBaseChange R A B B M) := by
  ext; rw [coe_map, coe_congr, coe_baseChange, baseChange_eq_span, map_span, map_coe,
    ← Set.image_comp, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one]

lemma map_id (N : G(k, A ⊗[R] M; A)) : N.map (AlgHom.id R A) = N :=
  ext (by rw [coe_map, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_coe, Set.image_id,
    span_coe_eq_restrictScalars, restrictScalars_self])

variable {C : Type*} [CommRing C] [Algebra R C]

lemma map_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (N : G(k, A ⊗[R] M; A)) :
    N.map (g.comp f) = (N.map f).map g := by
  refine letI := f.toAlgebra; letI := g.toAlgebra; ext ?_
  have hg : g = IsScalarTower.toAlgHom R B C := rfl
  rw [coe_map, coe_map', coe_map, hg, ← AlgebraTensorModule.cancelBaseChange_comp_mk_one',
    ← restrictScalars_map, map_span, coe_restrictScalars,
    span_span_of_tower, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, AlgebraTensorModule.coe_cancelBaseChange_comp_mk_one,
    AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.coe_comp, Set.image_comp]

/-- The Grassmannian functor given a ring `R`, an `R`-module `M`, and a natural number `k`.
Given an `R`-algebra `A`, we return the set `G(k, A ⊗[R] M; A)`. -/
@[simps!] def functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) :
    Under R ⥤ Type (max u v) where
  obj A := G(k, A ⊗[R] M; A)
  map f := map (CommRingCat.toAlgHom f)
  map_id _ := funext map_id
  map_comp f g := funext (map_comp (CommRingCat.toAlgHom f) (CommRingCat.toAlgHom g))

open CommRingCat AlgebraicGeometry in
/-- The Grassmannian functor as a `Sheaf`. -/
@[simps!] noncomputable def sheaf (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (k : ℕ) :
    Sheaf (OverScheme.zariskiTopology (Spec R)) (Type (max u v)) where
  val := (overSchemeOpEquivUnder R).functor ⋙ functor R M k
  cond := by
    intro X S 𝒮 hS W hW
    sorry

variable (R A) in
/-- The new collection of `k` elements that defines the chart after base change. -/
def newChart (x : Fin k → M) : Fin k → A ⊗[R] M :=
  TensorProduct.mk R A M 1 ∘ x

@[simp] lemma cancelBaseChange_comp_newChart [Algebra A B] [IsScalarTower R A B] (x : Fin k → M) :
    (AlgebraTensorModule.cancelBaseChange R A B B M) ∘ newChart A B (newChart R A x) =
    newChart R B x := by
  ext i; simp [newChart]

/-- Functoriality of `chart`. -/
lemma baseChange_mem_chart (x : Fin k → M) {N : G(k, M; R)} (hn : N ∈ chart R x) :
    N.baseChange A ∈ chart A (newChart R A x) := by
  convert ofEquiv_mem_chart (N.quotientBaseChange A ≪≫ₗ (lequivOfChart N hn).baseChange R A _ _
    ≪≫ₗ TensorProduct.piScalarRight R A A (Fin k)) ?_ (fun i ↦ ?_) using 1
  simp [newChart, Pi.single_apply_smul]

variable (A)

/-- Bundled version of base change of chart. -/
@[simps (isSimp := False)]
def chartBaseChange (x : Fin k → M) (N : chart R x) : chart A (newChart R A x) :=
  ⟨N.val.baseChange A, baseChange_mem_chart _ N.2⟩

open LinearEquiv in
lemma lequivOfChart_chartBaseChange (x : Fin k → M) (N : chart R x) :
    (quotientBaseChangeEquiv A N.1).symm ≪≫ₗ lequivOfChart _ (chartBaseChange A x N).2 =
    (lequivOfChart _ N.2).baseChange R A _ _ ≪≫ₗ TensorProduct.piScalarRight R A A (Fin k) := by
  refine toLinearMap_injective ?_
  rw [coe_trans, coe_trans, lequivOfChart, lequivOfChart, baseChange_symm, comp_toLinearMap_symm_eq,
    ← symm_symm (quotientBaseChangeEquiv _ _), eq_comp_toLinearMap_symm, eq_comp_toLinearMap_symm,
    LinearMap.comp_assoc, toLinearMap_symm_comp_eq]
  ext i : 4
  simpa [LinearEquiv.baseChange, Pi.single_apply_smul, -eq_self] using rfl

@[simp] lemma lequivOfChart_chartBaseChange_apply (x : Fin k → M) (N : chart R x) (m : M) :
    lequivOfChart _ (chartBaseChange A x N).2 (Submodule.Quotient.mk (1 ⊗ₜ m : A ⊗[R] M)) =
      fun j ↦ lequivOfChart _ N.2 (Submodule.Quotient.mk m) j • 1 := by
  simpa [Algebra.algebraMap_eq_smul_one] using
    congr($(lequivOfChart_chartBaseChange A x N) (1 ⊗ₜ Submodule.Quotient.mk m))

@[simp] lemma lequivOfChart_chartBaseChange_apply' (x : Fin k → M) (N : chart R x) (m : M)
    (h : N.val.baseChange A ∈ chart A (newChart R A x)) :
    lequivOfChart _ h (Submodule.Quotient.mk (1 ⊗ₜ m : A ⊗[R] M)) =
      fun j ↦ lequivOfChart _ N.2 (Submodule.Quotient.mk m) j • 1 :=
  lequivOfChart_chartBaseChange_apply _ _ _ _

/-- Functoriality of `chart`. -/
lemma baseChange_chart_subset (x : Fin k → M) :
    baseChange A '' (chart R x) ⊆ chart A (newChart R A x) :=
  Set.image_subset_iff.2 fun _ ↦ baseChange_mem_chart x

variable {A}

/-- Functoriality of `chart`. -/
lemma map_mem_chart (f : A →ₐ[R] B) (x : Fin k → M) {N : G(k, A ⊗[R] M; A)}
    (hn : N ∈ chart A (newChart R A x)) :
    N.map f ∈ chart B (newChart R B x) := by
  letI := f.toAlgebra
  simpa using congr_mem_chart (newChart A B (newChart R A x)) _ (baseChange_mem_chart
    (newChart R A x) hn) (AlgebraTensorModule.cancelBaseChange R A B B M)

/-- Functoriality of `chart`. -/
lemma map_chart_subset (f : A →ₐ[R] B) (x : Fin k → M) :
    map f '' (chart A (newChart R A x)) ⊆ chart B (newChart R B x) :=
  Set.image_subset_iff.2 fun _ ↦ map_mem_chart f _

/-- Bundled version of map of chart. -/
@[simps (isSimp := False)]
def chartMap (f : A →ₐ[R] B) (x : Fin k → M) (N : chart A (newChart R A x)) :
    chart B (newChart R B x) :=
  ⟨N.val.map f, map_mem_chart f _ N.2⟩

lemma chartMap_eq [Algebra A B] [IsScalarTower R A B] (x : Fin k → M)
    (N : chart A (newChart R A x)) :
    chartMap (IsScalarTower.toAlgHom R A B) x N =
      chartCongr (AlgebraTensorModule.cancelBaseChange R A B B M) _ (newChart R B x) (by simp)
        (chartBaseChange B (newChart R A x) N) := by
  ext : 1; simp [map_eq, chartMap_coe, chartCongr_apply_coe, chartBaseChange_coe]

@[simp] lemma lequivOfChart_chartMap_apply (f : A →ₐ[R] B) (x : Fin k → M)
    (N : chart A (newChart R A x)) (m : M) (i : Fin k) :
    lequivOfChart _ (chartMap f x N).2 (Submodule.Quotient.mk (1 ⊗ₜ m)) i =
    f (lequivOfChart _ N.2 (Submodule.Quotient.mk (1 ⊗ₜ m)) i) := by
  letI := f.toAlgebra
  have hf : f = IsScalarTower.toAlgHom R A B := rfl
  rw [hf, chartMap_eq, lequivOfChart_chartCongr]
  simp [chartBaseChange_coe, chartCongr_apply_coe, Algebra.algebraMap_eq_smul_one]

/-- A subfunctor of the Grassmannian, given an indexing `x : Fin k → M`, `chart x` selects the
elements `N ∈ G(k, A ⊗[R] M; A)` such that the composition `A^k → A ⊗[R] M → (A ⊗[R] M)/N.val` is
an isomorphism. This is called `chart` because it corresponds to an affine open chart in the
Grassmannian. -/
@[simps!] def chartFunctor (R : CommRingCat.{u}) {M : ModuleCat.{v} R} {k : ℕ}
    (x : Fin k → M) :
    Under R ⥤ Type (max u v) where
  obj A := chart A (newChart R A x)
  map f := chartMap (CommRingCat.toAlgHom f) x
  map_id _ := funext fun _ ↦ Subtype.ext <| map_id ..
  map_comp _ _ := funext fun _ ↦ Subtype.ext <|
    map_comp (CommRingCat.toAlgHom _) (CommRingCat.toAlgHom _) _

/-- `chartFunctor R M k x` is a subfunctor of `Grassmannian.functor R M k`. -/
def chartToFunctor (R : CommRingCat.{u}) {M : ModuleCat.{v} R} {k : ℕ}
    (x : Fin k → M) :
    chartFunctor R x ⟶ functor R M k where
  app A := Subtype.val


namespace Corepresentable

/-!
# Corepresentability of chart

We show that `chart x` is the equalizer of `Hom[R](M, R^k) ⥤ Hom[R](R^k, R^k)`.

We call `Hom[R](M, R^k)` "left" and `Hom[R](R^k, R^k)` "right".
-/

section CommRing

variable (R M k) (x : Fin k → M)

/-- The first module in the equaliser diagram. -/
abbrev Left : Type (max u v) :=
  M →ₗ[R] (Fin k → R)

/-- The second module in the equaliser diagram. -/
abbrev Right : Type u :=
  (Fin k → R) →ₗ[R] (Fin k → R)

variable {R k} in
@[ext] lemma Right.ext {f g : Right R k} (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| h i

variable {M k} in
/-- The first map `Left ⟶ right`. -/
@[simp] def compose : Left R M k → Right R k :=
  fun f ↦ f ∘ₗ Fintype.linearCombination R x

variable {M k} in
/-- The second map `Left ⟶ right`. -/
@[simp] def const1 : Left R M k → Right R k :=
  fun _ ↦ LinearMap.id

variable {R M k x} in
lemma surjective_of_compose_eq_const1 {f : Left R M k} (h : compose R x f = const1 R f) :
    Function.Surjective f :=
  fun p ↦ ⟨Fintype.linearCombination R x p, congr($h p)⟩

variable {M k} in
@[simp] noncomputable def toLeft : chart R x → Left R M k :=
  fun N ↦ lequivOfChart _ N.2 ∘ₗ N.1.mkQ

variable {M k} in
/-- The isomorphism between `chart x` and the equaliser of `compose, const1 : Left ⟶ right`. -/
noncomputable def chartEquivEq : chart R x ≃ {f : Left R M k // compose R x f = const1 R f} where
  toFun N := ⟨toLeft R x N, LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring <| by simp⟩
  invFun f := ⟨ofSurjective f.1 <| surjective_of_compose_eq_const1 f.2,
    ofSurjective_mem_chart _ _ fun i ↦ by simpa using congr($(f.2) (Pi.single i 1))⟩
  left_inv N := by ext; simp
  right_inv f := Subtype.ext <| LinearMap.ext fun p ↦ (LinearEquiv.symm_apply_eq _).2 <|
    (LinearMap.quotKerEquivOfSurjective _ (surjective_of_compose_eq_const1 f.2)).injective <| by
      simpa using congr($(f.2.symm) (f.1 p))

variable {R M k} (A) in
/-- Base change of `left` from `R` to `A`. -/
def leftBaseChange (f : Left R M k) : Left A (A ⊗[R] M) k :=
  TensorProduct.piScalarRightHom R A A (Fin k) ∘ₗ f.baseChange A

/-- Base change of `left` from `A` to `B`. -/
def leftMap (φ : A →ₐ[R] B) (f : Left A (A ⊗[R] M) k) : Left B (B ⊗[R] M) k :=
  letI := φ.toAlgebra
  leftBaseChange B f ∘ₗ (AlgebraTensorModule.cancelBaseChange R A B B M).symm

variable {R M k} in
@[simp] lemma leftMap_tmul (φ : A →ₐ[R] B) (f : Left A (A ⊗[R] M) k) (a : A) (m : M) (i : Fin k) :
    leftMap R M k φ f (φ a ⊗ₜ m) i = φ (f (a ⊗ₜ m) i) := by
  letI := φ.toAlgebra
  simp [leftMap, leftBaseChange, tmul_eq_smul_one_tmul a m, ← algebraMap_smul B, mul_comm,
    show algebraMap A B = φ from rfl]

@[simp] lemma leftMap_one_tmul {φ : A →ₐ[R] B} {f : Left A (A ⊗[R] M) k} (m : M) (i : Fin k) :
    leftMap R M k φ f (1 ⊗ₜ m) i = φ (f (1 ⊗ₜ m) i) := by
  simpa only [map_one] using leftMap_tmul φ f 1 m i

@[simp] lemma leftMap_id : leftMap R M k (AlgHom.id R A) = id := by
  ext; simp

@[simp] lemma leftMap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    leftMap R M k (ψ.comp φ) = leftMap R M k ψ ∘ leftMap R M k φ := by
  ext; simp

variable {R k} (A) in
/-- Base change of `right` from `R` to `A`. -/
def rightBaseChange (f : Right R k) : Right A k :=
  (TensorProduct.piScalarRight R A A (Fin k)).conj <| f.baseChange A

/-- Base change of `right` from `A` to `B`. -/
def rightMap (φ : A →ₐ[R] B) (f : Right A k) : Right B k :=
  letI := φ.toAlgebra; rightBaseChange B f

variable {R k} in
@[simp] lemma rightMap_apply_single (φ : A →ₐ[R] B) (f : Right A k) (i : Fin k) :
    rightMap R k φ f (Pi.single i 1) = φ ∘ f (Pi.single i 1) := by
  letI := φ.toAlgebra
  ext j
  simp [rightMap, rightBaseChange, LinearEquiv.conj_apply, ← Algebra.algebraMap_eq_smul_one,
    show algebraMap A B = φ from rfl]

@[simp] lemma rightMap_id :
    rightMap R k (AlgHom.id R A) = id := by
  ext; simp

@[simp] lemma rightMap_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    rightMap R k (ψ.comp φ) = rightMap R k ψ ∘ rightMap R k φ := by
  ext; simp

variable {M k x}

/-- Naturality of `toLeft : chart R x ⟶ left R M k` for base change (`R` to `A`). -/
lemma toLeft_baseChange_naturality (p : chart R x) :
    toLeft A (newChart R A x) (chartBaseChange A x p) =
      leftBaseChange A (toLeft R x p) :=
  TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext_ring <|
    LinearMap.ext fun m ↦ by simp [leftBaseChange]

/-- Naturality of `toLeft : chart R x ⟶ left R M k` for map (`A` to `B`). -/
lemma toLeft_map_naturality (φ : A →ₐ[R] B) (p : chart A (newChart R A x)) :
    toLeft B (newChart R B x) (chartMap φ x p) =
      leftMap R M k φ (toLeft A (newChart R A x) p) := by
  ext; simp

variable (M k A)

/-- We show that `Left` is corepresented by `Sym[R](Mᵏ)`. -/
noncomputable
def corepresentLeft : (SymmetricAlgebra R (Fin k → M) →ₐ[R] A) ≃ Left A (A ⊗[R] M) k := calc
  (SymmetricAlgebra R (Fin k → M) →ₐ[R] A)
    ≃ ((Fin k → M) →ₗ[R] A) := SymmetricAlgebra.lift.symm
  _ ≃ (Fin k → (M →ₗ[R] A)) := (LinearMap.lsum R (fun _ ↦ M) R).symm.toEquiv
  _ ≃ (M →ₗ[R] (Fin k → A)) := LinearMap.piEquiv _ _ _
  _ ≃ ((A ⊗[R] M) →ₗ[A] (Fin k → A)) := (LinearMap.liftBaseChangeEquiv A).toEquiv

/-- `Right A k` is actually isomorphic to `Left A (A ⊗[R] (Fin k → R)) k`. -/
def lequivLeftRight : Left A (A ⊗[R] (Fin k → R)) k ≃ₗ[A] Right A k :=
  LinearEquiv.congrLeft _ _ (TensorProduct.piScalarRight R A A (Fin k))

/-- We show that `Right` is corepresented by `Sym[R](R^(Fin k × Fin k))`. -/
noncomputable
def corepresentRight : (SymmetricAlgebra R (Fin k → Fin k → R) →ₐ[R] A) ≃ Right A k := calc
  (SymmetricAlgebra R (Fin k → Fin k → R) →ₐ[R] A)
    ≃ Left A (A ⊗[R] (Fin k → R)) k := corepresentLeft R (Fin k → R) k A
  _ ≃ Right A k := (lequivLeftRight R k A).toEquiv

@[simp] lemma corepresentLeft_apply (f : SymmetricAlgebra R (Fin k → M) →ₐ[R] A)
    (m : M) (i : Fin k) :
    corepresentLeft R M k A f (1 ⊗ₜ m) i = f (SymmetricAlgebra.ι R _ (Pi.single i m)) := by
  simp [corepresentLeft]

@[simp] lemma corepresentRight_apply (f : SymmetricAlgebra R (Fin k → Fin k → R) →ₐ[R] A)
    (i j : Fin k) :
    corepresentRight R k A f (Pi.single i 1) j =
      f (SymmetricAlgebra.ι R _ <| Pi.single j (Pi.single i 1)) := by
  simp [corepresentRight, lequivLeftRight]

end CommRing


section Category

-- I ain't dealing with no universe issues.
variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (k : ℕ) (x : Fin k → M)

/-- `Left` as a functor, sends `A` to `A ⊗[R] M →ₗ[A] Aᵏ`. -/
@[simps] abbrev leftFunctor : Under R ⥤ Type u where
  obj A := Left A (A ⊗[R] M) k
  map φ := leftMap R M k (CommRingCat.toAlgHom φ)

/-- `Right` as a functor, sends `A` to `Aᵏ →ₗ[A] Aᵏ`. -/
@[simps] abbrev rightFunctor : Under R ⥤ Type u where
  obj A := Right A k
  map φ := rightMap R k (CommRingCat.toAlgHom φ)

variable {M k} in
/-- `compose` as a natural transformation. -/
def composeNat : leftFunctor R M k ⟶ rightFunctor R k where
  app A := compose A (newChart R A x)
  naturality A B φ := by ext; simp [newChart]

/-- `const1` as a natural transformation. -/
def const1Nat : leftFunctor R M k ⟶ rightFunctor R k where
  app A := const1 A

variable {M k}

/-- The map `chartFunctor R x ⟶ leftFunctor R M k` that realises `chart x` as the equaliser. -/
noncomputable def chartToLeft : chartFunctor R x ⟶ leftFunctor R M k where
  app A f := (chartEquivEq A (newChart R A x) f).val
  naturality _ _ φ := funext fun p ↦ toLeft_map_naturality R (CommRingCat.toAlgHom φ) p

/-- `chartToLeft R x` equalizes `composeNat` and `const1Nat`. -/
lemma chartToLeft_equalises :
    chartToLeft R x ≫ composeNat R x = chartToLeft R x ≫ const1Nat R M k :=
  NatTrans.ext <| funext₂ fun A p ↦ ((chartEquivEq A (newChart R A x)).1 p).2

/-- The functor associated to `chart x` is isomorphic to the equaliser of the natural
transformations `composeNat, const1Nat : leftFunctor R M k ⟶ rightFunctor R k`.
This defines firstly the fork (a special type of cone). -/
noncomputable def fork : Fork (composeNat R x) (const1Nat R M k) :=
  .ofι (chartToLeft R x) (chartToLeft_equalises R x)

/-- The equaliser diagram when evaluated at `A : Under R` is an equaliser diagram. -/
def parallelPairCompEvaluationIso (A : Under R) :
    (parallelPair (composeNat R x) (const1Nat R M k)) ⋙ (evaluation _ _).obj A ≅
      parallelPair ((composeNat R x).app A) ((const1Nat R M k).app A) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) rfl rfl

/-- The equaliser cone evaluated at `A : Under R` is isomorphic to the cone explicitly constructed
in `Types`. -/
noncomputable def evaluationForkIso (A : Under R) :
    (Cones.postcompose (parallelPairCompEvaluationIso R x A).hom).obj
      (((evaluation (Under R) (Type u)).obj A).mapCone (fork R x)) ≅
    Types.equalizerLimit.cone :=
  Fork.ext (chartEquivEq A (newChart R A x)).toIso

/-- `fork` is a pointwise equaliser (recall that we are in the functor category
`Under R ⥤ Type u`, so pointwise means when evaluated at every `A : Under R`). -/
noncomputable def isLimitEvaluationFork (A : Under R) :
    IsLimit (((evaluation (Under R) (Type u)).obj A).mapCone (fork R x)) :=
  IsLimit.postcomposeHomEquiv _ _ <| IsLimit.equivIsoLimit (evaluationForkIso R x A).symm
    Types.equalizerLimit.isLimit

/-- `fork` is an equaliser. -/
noncomputable def isLimitFork : IsLimit (fork R x) :=
  evaluationJointlyReflectsLimits _ fun A ↦ isLimitEvaluationFork R x A

variable (M k)

/-- `left` is corepresentable by `Sym[R](Mᵏ)`. -/
noncomputable def CorepresentableBy.left : Functor.CorepresentableBy (leftFunctor R M k)
    (R.mkUnder <| SymmetricAlgebra R (Fin k → M)) where
  homEquiv {A} := (CommRingCat.homMkUnderEquiv _ _ _).trans (corepresentLeft R M k A)
  homEquiv_comp φ f := by ext m i; simp

/-- `right` is corepresentable by `Sym[R](R^(Fin k × Fin k))`. -/
noncomputable def CorepresentableBy.right : Functor.CorepresentableBy (rightFunctor R k)
    (R.mkUnder <| SymmetricAlgebra R (Fin k → Fin k → R)) where
  homEquiv {A} := (CommRingCat.homMkUnderEquiv _ _ _).trans (corepresentRight R k A)
  homEquiv_comp φ f := by ext m i; simp

variable {M k} in
/-- The corepresentative of `composeNat`. -/
noncomputable abbrev composeCorep : (R.mkUnder <| SymmetricAlgebra R (Fin k → Fin k → R)) ⟶
    (R.mkUnder <| SymmetricAlgebra R (Fin k → M)) :=
  (CorepresentableBy.left R M k).homOfNatTrans (CorepresentableBy.right R k) (composeNat R x)

/-- The corepresentative of `const1Nat`. -/
noncomputable abbrev const1Corep : (R.mkUnder <| SymmetricAlgebra R (Fin k → Fin k → R)) ⟶
    (R.mkUnder <| SymmetricAlgebra R (Fin k → M)) :=
  (CorepresentableBy.left R M k).homOfNatTrans (CorepresentableBy.right R k) (const1Nat R M k)

/-- `chartFunctor` is corepresentable. -/
noncomputable def CorepresentableBy.chartFunctor :
    Functor.CorepresentableBy (chartFunctor R x)
      (coequalizer (composeCorep R x) (const1Corep R M k)) :=
  (CorepresentableBy.left R M k).equalizer (CorepresentableBy.right R k) (isLimitFork R x)
    (colimit.isColimit _)

end Category

end Corepresentable


end Grassmannian

end Module
