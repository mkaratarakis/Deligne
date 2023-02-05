import field_theory.is_alg_closed.algebraic_closure
import linear_algebra.general_linear_group
import topology.algebra.continuous_monoid_hom
import field_theory.krull_topology


variables (k : Type*) [comm_ring k] [topological_space k] [topological_ring k]

noncomputable! def galois_rep (p : ℕ) (h: prime p) := continuous_monoid_hom
 ((algebraic_closure ℚ) ≃ₐ[ℚ] (algebraic_closure ℚ) ) (GL (fin p) k)

--Let ρ : GQ → GLn(K) be an n-dimensional Galois 
--representation over a field K, 
--and let p be --a prime.
--Let p be a prime number, D_p ≤ G_Q 
--be some choice of decomposition group,
--let I_p ≤ D_p be the inertia 
--subgroup (Ip and Dp are defined below). 
--A Galois representation --ρ : GQ → GLn(K)
-- is unramified at p if Ip ⊆ ker ρ.

--def is_unramified (q : height_one_spectrum (𝓞 L))
 -- (h : inertia_subgroup K q.valuation_subring = ⊥ ): Prop 
 -- := inertia_subgroup K q.valuation_subring  ≤ (galois_representation).ker