Require Import Monad.

Ltac unroll_hypotheses := match goal with
  | H : inhabited _ |- _ => destruct H as (H); unroll_hypotheses
  | _ => idtac
end.

Ltac fail_if_not_prop :=
  let Hprop := fresh in
  pose proof inhabits I as Hprop;
  destruct Hprop as [Hprop];
  clear Hprop.

Ltac unlift := fail_if_not_prop; unroll_hypotheses; try apply inhabits.

