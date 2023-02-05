import field_theory.cardinality
import field_theory.minpoly
import ring_theory.adjoin.basic
import field_theory.normal

variables {K L : Type*} [field K] [field L] [algebra K L] [is_galois K L]

theorem lemma1 [finite_dimensional K L] (β : L) (hβ : algebra.adjoin K ({β} : set L) = ⊤) : 
   function.injective  (λ g, g β : (L ≃ₐ[K] L) → L ) := 
  begin
  unfold function.injective,   
  rintros σ₁ σ₂ hσ,
  apply alg_equiv.coe_alg_hom_injective,
  refine alg_hom.ext_of_adjoin_eq_top hβ _,
  simp [hσ],
  end

namespace intermediate_field

open adjoin polynomial

lemma foo {α₁ α₂ : L} (hpoly : minpoly K α₁ = minpoly K α₂) :
  (aeval (power_basis (is_galois.integral K α₁)).gen)
  (minpoly K (power_basis (is_galois.integral K α₂)).gen) = 0 :=
begin
  apply (injective_iff_map_eq_zero _).1 (algebra_map K⟮α₁⟯ L).injective,
  have : is_integral K (adjoin_simple.gen K α₂),
  { rw [← is_integral_algebra_map_iff (algebra_map K⟮α₂⟯ L).injective],
    simp [is_galois.integral K α₂],
    all_goals { apply_instance } },
  rw [power_basis_gen, power_basis_gen, ← aeval_algebra_map_apply, adjoin_simple.algebra_map_gen,
    minpoly.eq_of_algebra_map_eq (algebra_map K⟮α₂⟯ L).injective this
    (adjoin_simple.algebra_map_gen K α₂).symm, ← hpoly],
  exact minpoly.aeval _ _
end

@[simps] noncomputable def equiv {α₁ α₂ : L} (hpoly : minpoly K α₁ = minpoly K α₂) : K⟮α₁⟯ ≃ₐ[K] K⟮α₂⟯ :=
power_basis.equiv_of_root (adjoin.power_basis (is_galois.integral K α₁))
  (power_basis (is_galois.integral K α₂)) (foo hpoly) (foo hpoly.symm)

theorem conjugate_roots (α₁ : L) (α₂ : L) (hpoly : minpoly K α₁ = minpoly K α₂) :
   ∃ (g : (L ≃ₐ[K] L)), g α₁ = α₂ :=
begin
  refine ⟨(equiv hpoly).lift_normal _, _⟩,
  simp_rw [← adjoin_simple.algebra_map_gen K α₁, ← adjoin_simple.algebra_map_gen K α₂],
  rw [alg_equiv.lift_normal_commutes],
  congr,
  simpa [adjoin.power_basis_gen] using
    power_basis.lift_gen (adjoin.power_basis (is_galois.integral K α₁)) _ (foo hpoly.symm),
end

end intermediate_field
