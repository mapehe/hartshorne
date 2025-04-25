import Alggeom.Basic

open Poly MvPolynomial

-- Define the Rabinowitsch homomorphism.
noncomputable def φ
  {n : ℕ+} {k : Type*} [Field k] (g : k[n]) :
  k [n + 1] →+* k(n) :=
  MvPolynomial.eval₂Hom
    (algebraMap k (k(n)))
    (λ (i : Fin (n + 1)) =>
      if h : (i : ℕ) < n then
        algebraMap (k[n]) (k(n)) (X ⟨i, h⟩)
      else
        (algebraMap (k[n]) (k(n)) g)⁻¹)
