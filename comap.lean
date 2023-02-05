import ring_theory.dedekind_domain.ideal
import number_theory.number_field.basic
import ring_theory.ideal.local_ring
import ring_theory.valuation.valuation_subring
import frobenius

namespace is_dedekind_domain

variables {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]
[is_domain R] [is_domain S] [is_dedekind_domain R] [is_dedekind_domain S] 

/-
def height_one_spectrum.map (e : R ≃+* S) (P : height_one_spectrum R) : 
  height_one_spectrum S := {
  as_ideal := ideal.map e P.as_ideal,
  is_prime := begin
  sorry,
  end,
  ne_bot := begin
  sorry,
  end }

lemma ideal.comap_eq_bot_iff {R : Type*} {S : Type*} {F : Type*} 
  [semiring R] [semiring S] [ring_equiv_class F R S] {f : F} {I : ideal S}:
    ideal.comap f I = ⊥ ↔ I = ⊥ :=
begin
  split,
  { rintro hcomap,
  --rw bot_eq_zero at *,
  ext y,
  rw set_like.ext_iff at hcomap,  
  simp_rw ideal.mem_bot at *,
  specialize hcomap (equiv_like.inv f y),
  simp at hcomap,
  rw hcomap,
  clear hcomap,
  sorry,
  },
  {sorry},
end

-/
lemma ideal.comap_eq_bot_iff {R : Type*} {S : Type*} [semiring R] 
  [semiring S] (f : R ≃+* S) {I : ideal S} : 
  ideal.comap f I = ⊥ ↔ I = ⊥ := 
begin
  simp [set_like.ext_iff, ideal.mem_bot],
  split,
  {rintros hcomap y,
  specialize hcomap (f.symm y),
  simp at hcomap,
  rw hcomap, },
  {rintros h x,
  specialize h (f x),
  simp at h,
  rw h, },
end

def height_one_spectrum.comap (e : R ≃+* S) (Q : height_one_spectrum S) : 
  height_one_spectrum R :=
  { as_ideal := ideal.comap e Q.as_ideal,
  is_prime := begin
  exact ideal.is_prime.comap e,
  end,
  ne_bot := begin
  have := Q.ne_bot,
  contrapose! this,
  rwa ideal.comap_eq_bot_iff at this,
  end}

section

open valuation_subring

variables {K L : Type*} [field K] [field L] [number_field K]
[number_field L] [algebra K L] [is_galois K L]

--#check ideal.sum_ramification_inertia 
--#check @ideal.sum_ramification_inertia
--#check is_noetherian

--(q.valuation : _root_.valuation L (ℤₘ₀)).valuation_subring)
--def comap_val (P : height_one_spectrum R) (Q : height_one_spectrum S) :
  --height_one_spectrum S → height_one_spectrum R := sorry

def comap_val (A : valuation_subring K ) (B : valuation_subring L) : 
    (valuation_subring L) → (valuation_subring K) := sorry

theorem comap_val_finite_fibers (A : valuation_subring K)
  (B : valuation_subring L) :
  finite  ((comap_val A B)⁻¹' {A}) := sorry

end
end is_dedekind_domain
