import ring_theory.ideal.local_ring
import ring_theory.valuation.valuation_subring
import number_theory.number_field.basic
import field_theory.cardinality
import ring_theory.dedekind_domain.adic_valuation
import group_theory.quotient_group
import ring_theory.valuation.ramification_group
import galois_lemmata

namespace local_ring

variables {A : Type*} {B : Type*} [comm_ring B] [comm_ring A]
  [local_ring A] [local_ring B] [algebra A B] [is_local_ring_hom (algebra_map A B)]

instance (e : B ≃+* B) : is_local_ring_hom (e.to_ring_hom) := {
  map_nonunit := begin
  rintros b  ⟨u, hu⟩,
  have huinv : u * u⁻¹ = 1,
    { simp only [mul_right_inv], },
  unfold is_unit,
  change ∃ v, _,
  let v := units.map((e.symm).to_ring_hom.to_monoid_hom) u,
  use v,
  change e.symm(u) = b,
  change (u : B) = e b at hu,
  rw hu,
  simp only [ring_equiv.symm_apply_apply],

end }

noncomputable instance general_algebra_map : 
  algebra (local_ring.residue_field A) (local_ring.residue_field B) :=
ring_hom.to_algebra (local_ring.residue_field.map (algebra_map A B))

def algebra_equiv_to_residue_equiv :
(B ≃ₐ[A] B) →* ((local_ring.residue_field B) ≃ₐ[local_ring.residue_field A] (local_ring.residue_field B)) :=
{ to_fun := λ x, 
  { to_fun := local_ring.residue_field.map (x.to_ring_equiv.to_ring_hom),
    inv_fun := local_ring.residue_field.map (x.symm.to_ring_equiv.to_ring_hom),
    left_inv := λ y, begin
      simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.symm_to_ring_equiv, residue_field.map_map,
      ring_equiv.symm_to_ring_hom_comp_to_ring_hom, residue_field.map_id, ring_hom.id_apply],
      end,
    right_inv := λ y, begin
      simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.symm_to_ring_equiv, residue_field.map_map,
      ring_equiv.to_ring_hom_comp_symm_to_ring_hom, residue_field.map_id, ring_hom.id_apply],
      end,
    map_mul' := λ x y, begin
      simp only [map_mul],
      end,
    map_add' := λ x y, begin
      simp only [map_add], 
      end,
    commutes' := begin
      have hx := x.commutes,
      suffices : (residue_field.map x.to_ring_equiv.to_ring_hom).comp (algebra_map (residue_field A) (residue_field B)) = algebra_map (residue_field A) (residue_field B),
      rwa fun_like.ext_iff at this,
      have hres : function.surjective (residue A), {
      exact (ideal.quotient.mk (maximal_ideal A)).is_surjective,
      },
      rw ← ring_hom.cancel_right hres,
      rw ring_hom.comp_assoc,
      change _ = (residue_field.map _).comp _,
      rw residue_field.map_comp_residue,
      change (residue_field.map x.to_ring_equiv.to_ring_hom).comp ((residue_field.map _).comp _) = _,
      rw residue_field.map_comp_residue,
      rw ← ring_hom.comp_assoc,
      rw residue_field.map_comp_residue,
      ext r,
      simp only [alg_equiv.to_ring_equiv_eq_coe, ring_hom.coe_comp, function.comp_app],
      congr',
      exact hx r,
      end, },
  map_one' := begin
    ext,
    simp only [alg_equiv.to_ring_equiv_eq_coe, alg_equiv.coe_mk, alg_equiv.one_apply],
    have hid := local_ring.residue_field.map_id_apply a,
    apply hid,
    end,
  map_mul' := λ x y,
    begin
    ext,
    simp only [alg_equiv.to_ring_equiv_eq_coe, residue_field.map_map, alg_equiv.coe_mk, alg_equiv.mul_apply],
    refl,
    end }

end local_ring

namespace valuation_subring

variables {K L : Type*} [field K] [field L]

def ring_hom.valuation_subring_comap (A : valuation_subring L) (f : K →+* L):
   (comap A f) →+* A :=
{ to_fun := λ x, ⟨f x.1, x.2⟩,
  map_one' := subtype.eq f.map_one,
  map_mul' := λ x y, subtype.eq (f.map_mul x y),
  map_add' := λ x y, subtype.eq (f.map_add x y),
  map_zero' := subtype.eq f.map_zero, }

instance valuation_subring_comap_local (A : valuation_subring L) (f : K →+* L) :
  (is_local_ring_hom (ring_hom.valuation_subring_comap A f))  :=
{ map_nonunit :=
  begin
    rintros ⟨a, ha⟩ ⟨y, hy : (y : ↥A) = ⟨f a, _⟩⟩,
    have hainv : a * a⁻¹ = 1,
    { apply mul_inv_cancel,
      rintro rfl,
      have hy0 : (y : A) = 0, simp [hy, f.map_zero], refl,
      have this : (0 : A) ≠ 1 := zero_ne_one,
      rw [← zero_mem_nonunits, ← hy0] at this,
      exact this (units.is_unit y),
    },
    refine is_unit_of_mul_eq_one ⟨a, ha⟩ ⟨a⁻¹, (_ : f a⁻¹ ∈ A)⟩
      (_ : (⟨a * a⁻¹, _⟩ : A.comap f)= ⟨1, _⟩), swap, simp [hainv],
    rcases y with ⟨⟨y1, h₁⟩, ⟨y2, h₂⟩, h1, h2⟩,
    convert h₂,
    have hy' : y1 = f a, simpa using hy,
    have h1' : y1 * y2 = 1 := subtype.mk.inj h1,
    apply_fun f at hainv,
    rw [map_mul, map_one] at hainv,
    rw hy' at h1',
    exact inv_unique hainv h1',
  end
}

noncomputable instance algebra_comap (A : valuation_subring L) (f : K →+* L) : 
   algebra (local_ring.residue_field (comap A f)) (local_ring.residue_field A) :=
ring_hom.to_algebra (local_ring.residue_field.map (ring_hom.valuation_subring_comap A f))

section

variables (K) [algebra K L]

open_locale pointwise

def decomposition_subgroup_to_residue_aut (A : valuation_subring L) : 
 (A.decomposition_subgroup K) →* ring_aut (local_ring.residue_field A) :=
 (local_ring.residue_field.map_aut).comp
 (mul_semiring_action.to_ring_aut (A.decomposition_subgroup K) A)

instance foo (A : valuation_subring L) : algebra (comap A (algebra_map K L)) A :=
ring_hom.to_algebra (ring_hom.valuation_subring_comap A (algebra_map K L))

def decomposition_subgroup.restrict (A : valuation_subring L) :
  (A.decomposition_subgroup K) →* (A ≃ₐ[comap A (algebra_map K L)] A) := {
  to_fun := λ x, {
    commutes' := begin
      rintros ⟨r, hr⟩,
      cases x with d hd,
      have := d.commutes,
      specialize this r,
      apply subtype.ext,
      exact this,
    end,
    ..(mul_semiring_action.to_ring_aut (A.decomposition_subgroup K) A x) },
  map_one' := begin
    ext,
    simp only [map_one, alg_equiv.coe_mk, alg_equiv.one_apply],
    refl,
    end,
  map_mul' := begin
    rintros x y,
    ext,
    simp only [alg_equiv.mul_apply, alg_equiv.coe_mk, map_mul],
    refl,
    end,
    }

end

namespace frobenius

variables [fintype K] [algebra K L]

/- find notation/def-/
--#print notation ¬
--#print not

--set_option pp.notation false

lemma power {p : ℕ} {m : ℕ} (hp : nat.prime p) (hpm : nat.prime (p ^ m)) :
  p = p ^ m :=
begin
  cases (le_or_lt 2 m) with hm h, 
  { exfalso,
    exact nat.prime.pow_not_prime hm hpm,
  },
  interval_cases m,
  {
   simp only [pow_zero],
   rw pow_zero at hpm,
   exfalso,
   have := nat.prime.ne_one hpm,
   unfold ne at this,
   dunfold not at this,
   apply this,
   refl, },
  {
  simp only [pow_one],
  }
end 

lemma char_p_of_card {p : ℕ} {n : ℕ} (hp : p.prime) (h : fintype.card K = p^n) :
  char_p K p := begin
  have hyp : add_order_of (1 : K) ∣ p^n,
  { rw ← h,
    apply add_order_of_dvd_card_univ,},
  rw nat.dvd_prime_pow hp at hyp,
  rcases hyp with ⟨m, hm, hpm⟩,
  have hK := char_p.add_order_of_one K,
  rw hpm at hK,
  resetI,
  have := char_p.char_is_prime K (p^m),
  convert hK,
  apply power hp this,
  end

lemma pow_card_eq {K : Type* } [field K] [fintype K] (x : K) :
  x ^ fintype.card K = x :=
begin
  rw finite_field.pow_card,
end

variables (K) (L)

def frob : (L →ₐ[K] L) := { 
  to_fun := λ x, x^fintype.card K,
  map_one' := one_pow (fintype.card K),
  map_mul' := λ x y, mul_pow x y (fintype.card K),
  map_zero' := begin
    simp only [zero_pow_eq_zero],
    exact fintype.card_pos,
    end,
  map_add' := λ x y, begin
    have foo : is_prime_pow (fintype.card K) := fintype.is_prime_pow_card_of_field,
      unfold is_prime_pow at foo,
      rcases foo with ⟨p, k, hp, hk, h⟩,
      rw ← h,
    haveI : fact (nat.prime p),
      { rw fact_iff,
        exact nat.prime_iff.mpr hp,},
    haveI : char_p L p, 
      { have : char_p K p ↔ char_p L p, exact algebra.char_p_iff K L p,
        rw ← this,
        apply char_p_of_card (nat.prime_iff.mpr hp) h.symm, },
    apply add_pow_char_pow,
  end,
  commutes' := λ x, begin
    have foo : is_prime_pow (fintype.card K) := 
      fintype.is_prime_pow_card_of_field,
      unfold is_prime_pow at foo,
      rcases foo with ⟨p, k, hp, hk, h⟩,
      rw ← h,
    haveI : fact (nat.prime p),
      { rw fact_iff,
        exact nat.prime_iff.mpr hp, },
    have : x^p^k = x,
      {rw h,
       rw finite_field.pow_card, },
      rw ← map_pow,
      rw this, end, }

variables {K} {L}

theorem frob_bijective (ha : algebra.is_algebraic K L) : function.bijective (frob K L) :=
algebra.is_algebraic.alg_hom_bijective ha _

noncomputable def equiv (ha : algebra.is_algebraic K L) : (L ≃ₐ[K] L) := 
   alg_equiv.of_bijective (frob K L) (frob_bijective ha)  

end frobenius

open_locale number_field
open is_dedekind_domain
open_locale classical polynomial

variables [number_field K] [number_field L] [algebra K L] [is_galois K L] (K)

open valuation_subring

noncomputable def _root_.is_dedekind_domain.height_one_spectrum.valuation_subring
 (q : height_one_spectrum (𝓞 L)) : valuation_subring L := 
  q.valuation.valuation_subring

/-- The natural reduction homomorphism. -/
noncomputable def decomposition_subgroup.to_residue_field_equiv (A : valuation_subring L) :
  (decomposition_subgroup K A) →* 
  ((local_ring.residue_field A) ≃ₐ[local_ring.residue_field (comap A (algebra_map K L))]
  (local_ring.residue_field A)) := 
  (local_ring.algebra_equiv_to_residue_equiv).comp (decomposition_subgroup.restrict K A)
--sorry--   (local_ring.algebra_equiv_to_residue_equiv).comp 
--(valuation_subring.decomposition_subgroup.restrict A (algebra_map K L))

instance galois_res (q : height_one_spectrum (𝓞 L)) : 
  is_galois (local_ring.residue_field (q.valuation_subring.comap (algebra_map K L)))
    (local_ring.residue_field (q.valuation_subring)) := begin
  sorry
  end

instance fin_dim (q: height_one_spectrum (𝓞 L)) :
  finite_dimensional (local_ring.residue_field (q.valuation_subring.comap (algebra_map K L)))
    (local_ring.residue_field ↥(q.valuation_subring)) := sorry

/-- The natural reduction homomorphism is surjective. -/
theorem decomposition_subgroup.surjective (q : height_one_spectrum (𝓞 L)) :
  function.surjective (decomposition_subgroup.to_residue_field_equiv K
  q.valuation_subring) := 
/- Let q be a prime of L above p prime of K -/
begin
unfold function.surjective,
rintros g, --g ∈ Gal ((𝓞 L)/q / (𝓞 K)/p))
/-Suppose β ∈ (𝓞 L)/q with (𝓞 L)/q = (𝓞 K)/p[β] 
(e.g. a generator for ((𝓞 L)/q)^x )
--###########################################################
theorem lemma1 [finite_dimensional K L] (β : L)
(hβ : algebra.adjoin K ({β} : set L) = ⊤) : 
   function.injective  (λ g, g β : (L ≃ₐ[K] L) → L ) := 
-/
have β : local_ring.residue_field (q.valuation_subring),
{sorry},
have hβ : algebra.adjoin (local_ring.residue_field 
  (comap (q.valuation_subring) (algebra_map K L))) 
  ({β} : set (local_ring.residue_field (q.valuation_subring))) = ⊤,
{sorry},
have hinj: function.injective (λ g, g β :
  ((local_ring.residue_field (q.valuation_subring)) 
  ≃ₐ[local_ring.residue_field 
  (comap (q.valuation_subring) (algebra_map K L))]
  (local_ring.residue_field (q.valuation_subring))) 
  → (local_ring.residue_field (q.valuation_subring))),
{exact lemma1 β hβ},
/- Let f(x) ∈ (𝓞 K)/p[X] be its minimal polynomial 
and β = β₁, β₂,..., βₙ ∈ (𝓞 L)/q its roots
It's sufficient to prove that ∃ σ ∈ Gal(L/K) with 
g(q)=q and g(β)= β₂. --/
have x : local_ring.residue_field (q.valuation_subring),
{sorry},
have fx := 
(minpoly (local_ring.residue_field 
(comap (q.valuation_subring) (algebra_map K L))) x),
have roots_fx := fx.root_set (local_ring.residue_field
 ((q.valuation_subring))),
/- Let F (X) ∈ (𝓞 K)[X] be its minimal polynomial 
over K and α = α₁,α₂,...,αᵣ ∈ (𝓞 L) be its roots
 (L/K normal ⇒ all roots are in L ) -/
have y : (q.valuation_subring), {sorry},
have Fx := 
  (minpoly (comap (q.valuation_subring) (algebra_map K L)) y),
have roots_Fx := Fx.root_set (q.valuation_subring),
/- Pick α ∈ (𝓞 L) with α = β mod q,
 α = 0 mod q′ for all other prime q′ above p
(by the CRT)
-/
/- F (X) mod p has β as a root
 ⇒ F (X) mod p is divisible by f(X)
 ⇒ F (X) mod p has β₂ as a root
-/
/-
WLOG α₂ mod q = β₂. 
Now take g ∈ Gal(L/K) such that g(α₁) = α₂.
Then g(α) ≠ 0 mod q implies g(q)=q and g(b)=b₂
-/
have α₁ : local_ring.residue_field (q.valuation_subring),
{sorry},
have α₂ : local_ring.residue_field (q.valuation_subring),
{sorry},
have hpoly : minpoly (local_ring.residue_field 
(comap (q.valuation_subring) (algebra_map K L))) α₁
 = minpoly (local_ring.residue_field 
(comap (q.valuation_subring) (algebra_map K L))) α₂,
{sorry},
have : ∃ (g : ((local_ring.residue_field (q.valuation_subring)) 
  ≃ₐ[local_ring.residue_field 
  (comap (q.valuation_subring) (algebra_map K L))]
  (local_ring.residue_field (q.valuation_subring))) ), g α₁ = α₂,
{exact intermediate_field.conjugate_roots α₁ α₂ hpoly},
/- theorem conjugate_roots (α₁ : L) (α₂ : L) 
(hpoly : minpoly K α₁ = minpoly K α₂) :
   ∃ (g : (L ≃ₐ[K] L)), g α₁ = α₂
-/
sorry,
end
/-The inertia group is defined as the kernel of the map
from D to the group of automorphisms of the residue field 
of A `ring_aut A`. 

But we want it to be the kernel of the map 
from D to local_ring.residue_field ↥A ≃ₐ[local_ring.residue_field 
↥(A.comap (algebra_map K L))] local_ring.residue_field ↥A -/

theorem decomposition_subgroup.bijective (q : height_one_spectrum (𝓞 L))
  (h : inertia_subgroup K q.valuation_subring = ⊥) :
function.bijective (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring) := 
begin
split,
{ have : (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring).ker = ⊥,
{sorry},
 exact (decomposition_subgroup.to_residue_field_equiv K
 q.valuation_subring).ker_eq_bot_iff.mp this,},
{exact decomposition_subgroup.surjective K q}
end

--thought
def ring_of_integers_to_res (B : valuation_subring L) :
  (𝓞 L) →+* (local_ring.residue_field B) := sorry

def res_field_equiv (B : valuation_subring L)
  (h : local_ring.maximal_ideal B ≠ ⊥ ) : 
  (𝓞 L) ⧸ (ring_of_integers_to_res B).ker
   ≃+* local_ring.residue_field B := sorry

instance res_field_finite (B : valuation_subring L)
  (h : local_ring.maximal_ideal B ≠ ⊥) :
 fintype (local_ring.residue_field B) := begin
 --have hh := (res_field_equiv B h).to_equiv,
 sorry
end

def frobq (ha : algebra.is_algebraic K L)
  (q : height_one_spectrum (𝓞 L)) 
  (h : inertia_subgroup K q.valuation_subring = ⊥) : 
  (decomposition_subgroup K q.valuation_subring) := 
{ val := begin
--have :=
--(equiv.of_bijective (decomposition_subgroup.to_residue_field_equiv
-- K (q.valuation_subring)))⁻¹(frobenius.equiv ha),
sorry,
end,
property := sorry, }

end valuation_subring
