/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Lemmas
import EllipticCurve.ProjectiveSpace.TensorProduct.BaseChange
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `n`th symmetric tensor power of `M` as the `TensorPower` quotiented by the relation
that the `tprod` of `n` elements is equal to the `tprod` of the same elements permuted by a
permutation of `Fin n`. We denote this space by `Sym[R]^n M`, and the canonical multilinear map
from `M ^ n` to `Sym[R]^n M` by `⨂ₛ[R] i, f i`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogneous (multivariate) polynomials of degree `n`.

-/

suppress_compilation

universe u u₁ u₂ v v₁ v₂ v₃ w w₁

open TensorProduct Equiv SymmetricMap Function

section CommSemiring

variable (R : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M]
  (N : Type v₁) [AddCommMonoid N] [Module R N] (P : Type v₂) [AddCommMonoid P] [Module R P]
  (A : Type w) [CommSemiring A] [Algebra R A]
  (B : Type w₁) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (n : ℕ)

/-- The relation on the `n`ᵗʰ tensor power of `M` that two tensors are equal if they are related by
a permutation of `Fin n`. -/
inductive SymmetricPower.Rel : ⨂[R]^n M → ⨂[R]^n M → Prop
  | perm : (e : Perm (Fin n)) → (f : Fin n → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/-- The symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `n`ᵗʰ tensor power by the relation that two tensors are equal
if they are related by a permutation of `Fin n`. -/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R M n)).Quotient

@[inherit_doc] scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => SymmetricPower R M n

namespace SymmetricPower

instance : AddCommMonoid (Sym[R]^n M) := AddCon.addCommMonoid _

/-- The canonical map from the `n`ᵗʰ tensor power to the `n`ᵗʰ symmetric tensor power. -/
def mk' : ⨂[R]^n M →+ Sym[R]^n M where
  __ := AddCon.mk' _

variable {R M n} in
@[elab_as_elim] lemma mk'_induction {C : Sym[R]^n M → Prop} (ih : ∀ x, C (mk' R M n x))
    (x : Sym[R]^n M) : C x :=
  AddCon.induction_on x ih

variable {R M n} in
@[elab_as_elim] lemma mk'_inductionOn {C : Sym[R]^n M → Prop} (x : Sym[R]^n M)
    (ih : ∀ x, C (mk' R M n x)) : C x :=
  AddCon.induction_on x ih

section SMul

open PiTensorProduct

variable {R₁ : Type u₁} [Monoid R₁] [DistribMulAction R₁ R] [SMulCommClass R₁ R R]

variable {R M n} in
lemma smulAux' (r : R) (x y : ⨂[R]^n M) (h : Rel R M n x y) :
    addConGen (Rel R M n) (r • x) (r • y) := by
  induction h with
  | perm e f => cases n with
    | zero => convert (addConGen (Rel R M 0)).refl _
    | succ n =>
      convert AddConGen.Rel.of _ _ (Rel.perm (R := R) e (Function.update f 0 (r • f 0)))
      · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
      · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
          ← Function.update_comp_equiv, Function.update_eq_self]; rfl

variable {R M n} in
lemma smulAux (r₁ : R₁) (x y : ⨂[R]^n M) (h : Rel R M n x y) :
    addConGen (Rel R M n) (r₁ • x) (r₁ • y) := by
  have := SMulCommClass.isScalarTower R₁ R
  convert smulAux' (r₁ • 1) x y h using 1 <;> rw [smul_one_smul]

instance smul : SMul R₁ (Sym[R]^n M) where
  smul r := AddCon.lift _ ((AddCon.mk' _).comp (AddMonoidHom.smulLeft r)) <|
    AddCon.addConGen_le fun x y h ↦ Quotient.sound <| by convert smulAux r x y h

variable {R M n} in
lemma smul_def (r : R₁) (x : ⨂[R]^n M) : r • mk' R M n x = mk' R M n (r • x) :=
  rfl

variable {R₂ : Type u₂} [Monoid R₂] [DistribMulAction R₂ R] [SMulCommClass R₂ R R]
  [SMul R₁ R₂] [IsScalarTower R₁ R₂ R]

instance : IsScalarTower R₁ R₂ (Sym[R]^n M) where
  smul_assoc x y := mk'_induction fun z ↦ by simp [smul_def]

end SMul

instance module (R₁ : Type u₁) [Semiring R₁] [Module R₁ R] [SMulCommClass R₁ R R] :
    Module R₁ (Sym[R]^n M) where
  one_smul := mk'_induction fun x ↦ congr_arg (mk' R M n) <| one_smul R₁ x
  mul_smul r s := mk'_induction fun x ↦ congr_arg (mk' R M n) <| mul_smul r s x
  zero_smul := mk'_induction fun x ↦ congr_arg (mk' R M n) <| zero_smul R₁ x
  add_smul r s := mk'_induction fun x ↦ congr_arg (mk' R M n) <| add_smul r s x
  smul_zero _ := map_zero _
  smul_add _ := map_add _

-- shortcut instance
instance : Module R (Sym[R]^n M) :=
  module R M n R

/-- The canonical map from the `n`ᵗʰ tensor power to the `n`ᵗʰ symmetric tensor power. -/
def mk : ⨂[R]^n M →ₗ[R] Sym[R]^n M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

@[elab_as_elim] lemma mk_induction {C : Sym[R]^n M → Prop} (ih : ∀ x, C (mk R M n x))
    (x : Sym[R]^n M) : C x :=
  mk'_induction ih x

@[elab_as_elim] lemma mk_inductionOn {C : Sym[R]^n M → Prop} (x : Sym[R]^n M)
    (ih : ∀ x, C (mk R M n x)) : C x :=
  mk'_inductionOn x ih

variable {M n} in
/-- The multilinear map that takes `n` elements of `M` and returns their symmetric tensor product.
Denoted `⨂ₛ[R] i, f i`. -/
def tprod : M [Σ^Fin n]→ₗ[R] Sym[R]^n M :=
  ⟨(mk R M n).compMultilinearMap (PiTensorProduct.tprod R), fun x e ↦
    Eq.symm <| Quot.sound <| AddConGen.Rel.of _ _ <| Rel.perm e x⟩

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R M n} in
@[simp] lemma tprod_perm_apply (e : Perm (Fin n)) (f : Fin n → M) :
    (⨂ₛ[R] i, f (e i)) = tprod R f :=
  (tprod R).2 f e

theorem range_mk : LinearMap.range (mk R M n) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor product. -/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (M := M) (n := n))) = ⊤ := by
  rw [tprod, coe_mk, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

variable {R M n} in
@[elab_as_elim] lemma inductionOn {C : Sym[R]^n M → Prop} (x : Sym[R]^n M)
    (zero : C 0) (smul_tprod : ∀ (r : R) x, C (r • tprod R x))
    (add : ∀ x y, C x → C y → C (x + y)) : C x := by
  obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
  obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
  refine FreeAddMonoid.inductionOn x zero (fun ⟨r, x⟩ ↦ ?_) fun _ _ ↦ add _ _
  simpa [tprod, ← map_smul, ← PiTensorProduct.tprodCoeff_eq_smul_tprod] using smul_tprod r x

variable {R M n} in
@[elab_as_elim] lemma induction {C : Sym[R]^n M → Prop}
    (zero : C 0) (smul_tprod : ∀ (r : R) x, C (r • tprod R x)) (add : ∀ x y, C x → C y → C (x + y))
    (x : Sym[R]^n M) : C x :=
  inductionOn x zero smul_tprod add

variable {R M N n} in
omit [Module R N] in
@[ext] lemma addHom_ext {f g : Sym[R]^n M →+ N}
    (h : ∀ (r : R) (x : Fin n → M), f (r • tprod R x) = g (r • tprod R x)) :
    f = g :=
  DFunLike.ext _ _ fun x ↦ inductionOn x (by simp) h (by intros; simp [*])

variable {R M N n} in
@[ext] lemma hom_ext {f g : Sym[R]^n M →ₗ[R] N}
    (h : ∀ x : Fin n → M, f (tprod R x) = g (tprod R x)) :
    f = g :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext fun r x ↦ by simp [map_smul, h]

variable {R M N n} in
def liftAux (f : M [Σ^Fin n]→ₗ[R] N) : Sym[R]^n M →ₗ[R] N where
  __ := AddCon.lift _ (AddMonoidHomClass.toAddMonoidHom <| PiTensorProduct.lift f) <|
    AddCon.addConGen_le fun _ _ h ↦ h.rec fun e x ↦ by simp
  map_smul' c x := AddCon.induction_on x <| by convert (PiTensorProduct.lift f.1).map_smul c

variable {R M N n} in
@[simp] lemma liftAux_tprod (f : M [Σ^Fin n]→ₗ[R] N) (x : Fin n → M) :
    liftAux f (tprod R x) = f x := by
  change liftAux f (AddCon.mk' _ _) = _; simp [liftAux]

def lift : M [Σ^Fin n]→ₗ[R] N ≃ₗ[R] (Sym[R]^n M →ₗ[R] N) where
  toFun f := liftAux f
  invFun f := f.compSymmetricMap (tprod R)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := hom_ext fun x ↦ by simp
  map_smul' c f := hom_ext fun x ↦ by simp

variable {R M N n} in
@[simp] lemma lift_tprod (f : M [Σ^Fin n]→ₗ[R] N) (x : Fin n → M) :
    lift R M N n f (tprod R x) = f x :=
  liftAux_tprod f x

variable {R M N n} in
@[simp] lemma lift_symm_coe (f : Sym[R]^n M →ₗ[R] N) :
    ⇑((lift R M N n).symm f) = ⇑f ∘ ⇑(tprod R) := rfl

variable {R M N} in
def map (f : M →ₗ[R] N) : Sym[R]^n M →ₗ[R] Sym[R]^n N :=
  lift _ _ _ _ <| (tprod R).compLinearMap f

@[simp] lemma map_tprod (f : M →ₗ[R] N) (x : Fin n → M) :
    map n f (tprod R x) = ⨂ₛ[R] i, f (x i) := by
  simp [map]

/-- Functoriality of `map`. -/
@[simp] lemma map_id : map n (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  hom_ext fun x ↦ by simp

variable {R M N P} in
/-- Functoriality of `map`. -/
lemma map_comp (f : N →ₗ[R] P) (g : M →ₗ[R] N) :
    map n (f ∘ₗ g) = map n f ∘ₗ map n g :=
  hom_ext fun x ↦ by simp

variable {R M N P} in
@[simp] lemma map_map_apply (f : N →ₗ[R] P) (g : M →ₗ[R] N) (x : Sym[R]^n M) :
    map n f (map n g x) = map n (f ∘ₗ g) x := by
  simp [map_comp]

variable {R M N} in
/-- `map` converts linear equiv to linear equiv. -/
def mapLinearEquiv (e : M ≃ₗ[R] N) : Sym[R]^n M ≃ₗ[R] Sym[R]^n N :=
  .ofLinear (map n e) (map n e.symm)
    (by rw [← map_comp, e.comp_symm, map_id])
    (by rw [← map_comp, e.symm_comp, map_id])

@[simp] lemma mapLinearEquiv_coe (e : M ≃ₗ[R] N) :
    (mapLinearEquiv n e).toLinearMap = map n e := rfl

@[simp] lemma mapLinearEquiv_coe' (e : M ≃ₗ[R] N) :
    ⇑(mapLinearEquiv n e) = map n e := rfl

@[simp] lemma mapLinearEquiv_symm (e : M ≃ₗ[R] N) :
    (mapLinearEquiv n e).symm = mapLinearEquiv n e.symm := rfl

def mul (i j : ℕ) : Sym[R]^i M →ₗ[R] Sym[R]^j M →ₗ[R] Sym[R]^(i + j) M :=
  lift _ _ _ _ <|
  { toFun f := lift _ _ _ _ <|
    { toFun g := tprod R <| Fin.append f g
      map_update_add' g c x y := by simp
      map_update_smul' g c r x := by simp
      map_perm_apply' g e := by
        convert (tprod_perm_apply (Fin.permAdd 1 e) _) using 2
        ext x; exact x.addCases (by simp) (by simp) }
    map_update_add' f c x y := hom_ext fun g ↦ by simp
    map_update_smul' f c r x := hom_ext fun g ↦ by simp
    map_perm_apply' f e := hom_ext fun g ↦ by
      simp only [lift_tprod, coe_mk, MultilinearMap.coe_mk]
      convert (tprod_perm_apply (Fin.permAdd e 1) _) using 2
      ext x; exact x.addCases (by simp) (by simp) }

scoped infixl:70 "✱" => SymmetricPower.mul _ _ _ _

variable {R M N} in
@[simp] lemma map_mul (i j : ℕ) (f : M →ₗ[R] N) :
    (mul R M i j).compr₂ (map (i + j) f) = (mul R N i j).compl₁₂ (map i f) (map j f) :=
  hom_ext fun v ↦ hom_ext fun w ↦ by simp [mul, Fin.apply_append_apply, Function.comp_def]

variable {R M N} in
@[simp] lemma map_mul_apply {i j : ℕ} (f : M →ₗ[R] N) (x : Sym[R]^i M) (y : Sym[R]^j M) :
    map (i + j) f (x ✱ y) = map i f x ✱ map j f y :=
  congr($(map_mul i j f) x y)

section simp_lemmas

-- We hard code special cases with small numbers.
variable {R M N} (f : M →ₗ[R] N)

@[simp] lemma map_mul_one_one (x y : Sym[R]^1 M) :
    map 2 f (x ✱ y) = map 1 f x ✱ map 1 f y :=
  map_mul_apply f x y

@[simp] lemma map_mul_one_two (x : Sym[R]^1 M) (y : Sym[R]^2 M) :
    map 3 f (x ✱ y) = map 1 f x ✱ map 2 f y :=
  map_mul_apply f x y

@[simp] lemma map_mul_two_one (x : Sym[R]^2 M) (y : Sym[R]^1 M) :
    map 3 f (x ✱ y) = map 2 f x ✱ map 1 f y :=
  map_mul_apply f x y

@[simp] lemma map_mul_one_three (x : Sym[R]^1 M) (y : Sym[R]^3 M) :
    map 4 f (x ✱ y) = map 1 f x ✱ map 3 f y :=
  map_mul_apply f x y

@[simp] lemma map_mul_two_two (x y : Sym[R]^2 M) :
    map 4 f (x ✱ y) = map 2 f x ✱ map 2 f y :=
  map_mul_apply f x y

@[simp] lemma map_mul_three_one (x : Sym[R]^3 M) (y : Sym[R]^1 M) :
    map 4 f (x ✱ y) = map 3 f x ✱ map 1 f y :=
  map_mul_apply f x y

end simp_lemmas

@[simps!] def zero_equiv : Sym[R]^0 M ≃ₗ[R] R where
  __ := lift R M R 0 ((ofIsEmpty R M R (Fin 0)).symm 1)
  invFun r := r • tprod R ![]
  left_inv x := by
    induction x using SymmetricPower.inductionOn with
    | zero => simp
    | smul_tprod r x => simp [Subsingleton.elim x ![]]
    | add x y hx hy => simp_all [add_smul]
  right_inv r := by simp

@[simps!] def one_equiv : Sym[R]^1 M ≃ₗ[R] M where
  __ := lift R M M 1 ((ofSubsingleton R M M 0).symm 1)
  invFun m := tprod R ![m]
  left_inv x := by
    induction x using SymmetricPower.inductionOn with
    | zero => simp [(tprod R).map_coord_zero (g := ![(0 : M)]) 0]
    | smul_tprod r x =>
        convert (tprod R).map_update_smul x 0 r (x 0) <;>
        exact funext <| Fin.forall_fin_one.2 <| by simp
    | add x y hx hy =>
        have (m₁ m₂ : M) : tprod R ![m₁ + m₂] = tprod R ![m₁] + tprod R ![m₂] := by
          convert (tprod R).map_update_add ![0] 0 m₁ m₂ using 3 <;>
          exact funext <| Fin.forall_fin_one.2 <| by simp
        conv => enter [2]; rw [← hx, ← hy]
        simp [this]
  right_inv m := by simp

def toBaseChange : (Sym[R]^n M) →ₗ[R] (Sym[A]^n (A ⊗[R] M)) :=
  lift _ _ _ _ <| ((tprod A).restrictScalars R).compLinearMap (TensorProduct.mk R A M 1)

variable {M n} in
@[simp] lemma toBaseChange_tprod (x : Fin n → M) :
    toBaseChange R M A n (tprod R x) = ⨂ₛ[A] i, (1 ⊗ₜ x i) := by
  simp [toBaseChange, restrictScalars]

def baseChange : (A ⊗[R] Sym[R]^n M) ≃ₗ[A] Sym[A]^n (A ⊗[R] M) :=
  .ofLinear (LinearMap.liftBaseChangeEquiv A <| toBaseChange R M A n)
    (lift A _ _ _ <| SymmetricMap.baseChange _ _ _ _ _ (tprod R))
    ((lift _ _ _ _).symm.injective <| baseChange_hom_ext fun v ↦ by simp)
    ((LinearMap.liftBaseChangeEquiv A).symm.injective <| hom_ext fun v ↦ by simp)

variable {M A n} in
@[simp] lemma baseChange_tmul_tprod (r : A) (x : Fin n → M) :
    baseChange R M A n (r ⊗ₜ[R] tprod R x) = r • ⨂ₛ[A] i, (1 ⊗ₜ x i) := by
  simp [baseChange, toBaseChange_tprod]

variable {M n} in
lemma baseChange_one_tmul_tprod (x : Fin n → M) :
    baseChange R M A n (1 ⊗ₜ[R] tprod R x) = ⨂ₛ[A] i, (1 ⊗ₜ x i) := by
  simp

variable {R M N} in
theorem map_comp_toBaseChange (f : M →ₗ[R] N) :
    (map n (f.baseChange A)).restrictScalars R ∘ₗ toBaseChange R M A n =
      toBaseChange R N A n ∘ₗ map n f :=
  hom_ext <| by simp

variable {R M N n} in
lemma map_toBaseChange_apply (f : M →ₗ[R] N) (x : Sym[R]^n M) :
    map n (f.baseChange A) (toBaseChange R M A n x) =
      toBaseChange R N A n (map n f x) :=
  congr($(map_comp_toBaseChange A n f) x)

variable {R M N} in
/-- Naturality of `baseChange`. -/
theorem map_comp_baseChange (f : M →ₗ[R] N) :
    map n (f.baseChange A) ∘ₗ baseChange R M A n =
      baseChange R N A n ∘ₗ (map n f).baseChange A :=
  (LinearMap.liftBaseChangeEquiv A).symm.injective <| hom_ext <| by simp

variable {R M N A n} in
lemma map_baseChange_apply (f : M →ₗ[R] N) (x : A ⊗[R] Sym[R]^n M) :
    map n (f.baseChange A) (baseChange R M A n x) =
      baseChange R N A n ((map n f).baseChange A x) :=
  congr($(map_comp_baseChange A n f) x)

lemma toBaseChange_of_isScalarTower :
    (toBaseChange R M B n).restrictScalars R =
      (map n (AlgebraTensorModule.cancelBaseChange R A B B M)).restrictScalars R ∘ₗ
        (toBaseChange A (A ⊗[R] M) B n).restrictScalars R ∘ₗ
          (toBaseChange R M A n) :=
  hom_ext fun v ↦ by simp

variable {R M n} in
lemma toBaseChange_apply_of_isScalarTower (x : Sym[R]^n M) :
    toBaseChange R M B n x =
      map n (AlgebraTensorModule.cancelBaseChange R A B B M).toLinearMap
        (toBaseChange A (A ⊗[R] M) B n <| toBaseChange R M A n x) :=
  congr($(toBaseChange_of_isScalarTower R M A B n) x)

section Algebra

variable [Module A M] [IsScalarTower R A M]

@[simp] lemma mul_tprod_tprod (i j : ℕ) (v : Fin i → M) (w : Fin j → M) :
    mul R M i j (tprod R v) (tprod R w) = tprod R (Fin.append v w) := by
  simp [mul]

instance : One (Sym[R]^n A) where
  one := tprod R 1

lemma one_def : (1 : Sym[R]^n A) = tprod R 1 := rfl

def eval : Sym[R]^n A →ₗ[R] A :=
  lift _ _ _ _ <| mkPiAlgebra R (Fin n) A

@[simp] lemma eval_tprod (v : Fin n → A) :
    eval R A n (tprod R v) = ∏ i, v i := by
  simp [eval]

@[simp] lemma eval_one : eval R A n 1 = 1 := by
  simp [one_def]

@[simp] lemma eval_mul (i j : ℕ) :
    (mul R A i j).compr₂ (eval R A (i + j)) =
      (LinearMap.mul R A).compl₁₂ (eval R A i) (eval R A j) :=
  hom_ext fun v ↦ hom_ext fun w ↦ by simp [Fin.prod_univ_add]

@[simp] lemma eval_mul_apply (i j : ℕ) (v : Sym[R]^i A) (w : Sym[R]^j A) :
    eval R A (i + j) (mul R A i j v w) = eval R A i v * eval R A j w :=
  congr($(eval_mul R A i j) v w)

section simp_lemmas

-- custom simp lemmas for concrete small values

@[simp] lemma eval_mul_one_one (v w : Sym[R]^1 A) :
    eval R A 2 (mul R A 1 1 v w) = eval R A 1 v * eval R A 1 w :=
  eval_mul_apply R A 1 1 v w

@[simp] lemma eval_mul_two_one (v : Sym[R]^2 A) (w : Sym[R]^1 A) :
    eval R A 3 (mul R A 2 1 v w) = eval R A 2 v * eval R A 1 w :=
  eval_mul_apply R A 2 1 v w

@[simp] lemma eval_mul_one_two (v : Sym[R]^1 A) (w : Sym[R]^2 A) :
    eval R A 3 (mul R A 1 2 v w) = eval R A 1 v * eval R A 2 w :=
  eval_mul_apply R A 1 2 v w

end simp_lemmas

end Algebra

def evalSelf : Sym[R]^n R ≃ₗ[R] R :=
  .ofLinear (eval R R n)
    (LinearMap.smulRight (S := R) 1 1)
    ((LinearMap.ringLmapEquivSelf R R _).injective <| by simp)
    (hom_ext fun v ↦ by simp [one_def, ← map_smul_univ])

@[simp] lemma evalSelf_coe : (evalSelf R n).toLinearMap = eval R R n := rfl

@[simp] lemma evalSelf_coe' : ⇑(evalSelf R n) = eval R R n := rfl

end SymmetricPower

end CommSemiring

section CommRing

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N] (n : ℕ)

instance : AddCommGroup (Sym[R]^n M) := AddCon.addCommGroup _

end CommRing

-- TODO: GradedMonoid.GMonoid!
