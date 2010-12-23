Require Import Reals.

Set Implicit Arguments.

Open Scope R_scope.

Module Type Integrals.

Axiom Riemann_integrable : forall (f : R -> R) (a b:R), Type.
Axiom RiemannInt_P1 : forall (f: R -> R) (a b : R), Riemann_integrable f a b -> Riemann_integrable f b a.
Axiom RiemannInt : forall (f : R -> R) (a b: R) (pr: Riemann_integrable f a b), R.
Axiom RiemannInt_ext : forall (f : R -> R) (a b:R) (pr1 pr2: Riemann_integrable f a b), RiemannInt pr1 = RiemannInt pr2.
Axiom Riemann_integrable_singleton : forall (f:R -> R) (a:R), Riemann_integrable f a a.
Axiom continuity_implies_RiemannInt :
  forall (f:R -> R) (a b:R),
    (forall x:R, (a <= x <= b \/ b <= x <= a)-> continuity_pt f x) -> Riemann_integrable f a b.
Axiom RiemannInt_opp : forall (f:R -> R) (a b:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b a), RiemannInt pr1 = - RiemannInt pr2.
Axiom RiemannInt_singleton : forall (f:R -> R) (a:R) (pr:Riemann_integrable f a a), RiemannInt pr = 0.
Axiom Riemann_integrable_linear : forall (f g:R -> R) (a b l:R),
    Riemann_integrable f a b ->
    Riemann_integrable g a b ->
    Riemann_integrable (fun x:R => f x + l * g x) a b.
Axiom RiemannInt_linear : forall (f g:R -> R) (a b l:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable g a b)
    (pr3:Riemann_integrable (fun x:R => f x + l * g x) a b),
    RiemannInt pr3 = RiemannInt pr1 + l * RiemannInt pr2.
Axiom Riemann_integrable_const : forall a b c:R, Riemann_integrable (fct_cte c) a b.
Axiom RiemannInt_const : forall (a b c:R) (pr:Riemann_integrable (fct_cte c) a b),
    RiemannInt pr = c * (b - a).

Axiom Riemann_integrable_Rabs : forall (f:R -> R) (a b:R),
    Riemann_integrable f a b -> Riemann_integrable (fun x:R => Rabs (f x)) a b.
Axiom Riemann_integrable_chasles : forall (f: R->R) (a b c: R),
  Riemann_integrable f a b ->
    Riemann_integrable f b c -> Riemann_integrable f a c.
Axiom RiemannInt_monotony: forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f a c.
Axiom RiemannInt_monotony2 : forall (f:R -> R) (a b c:R),
    Riemann_integrable f a b -> a <= c <= b -> Riemann_integrable f c b.
Axiom RiemannInt_chasles: forall (f:R -> R) (a b c:R) (pr1:Riemann_integrable f a b)
    (pr2:Riemann_integrable f b c) (pr3:Riemann_integrable f a c),
    RiemannInt pr1 + RiemannInt pr2 = RiemannInt pr3.
Axiom derive_Riemann_integrable: forall (f:R -> R) (H: derivable f) (cont1 : continuity (derive f H)) (a b:R), Riemann_integrable (derive f (H)) a b.
Axiom FTC_Riemann : forall (f:R -> R) (H: derivable f) (cont1 : continuity (derive f H)) (a b:R) (pr:Riemann_integrable (derive f H) a b),
    RiemannInt pr = f b - f a.

End Integrals.