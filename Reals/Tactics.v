Ltac eapply_assumption := match goal with
 | H: _ |- _ => eapply H
end.
