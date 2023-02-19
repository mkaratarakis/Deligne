import field_theory.is_alg_closed.algebraic_closure
import topology.algebra.continuous_monoid_hom
import field_theory.krull_topology
import linear_algebra.matrix.general_linear_group
import frobenius
import topology.instances.matrix

variables (k : Type*) [comm_ring k] [topological_space k] [topological_ring k]

/- The type of Galois representations -/
noncomputable! def galois_rep := continuous_monoid_hom
 ((algebraic_closure ℚ) ≃ₐ[ℚ] (algebraic_closure ℚ) ) (GL (fin 2) k)

