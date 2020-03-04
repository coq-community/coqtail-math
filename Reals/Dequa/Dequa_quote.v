
(** This file provides the user with the tactics needed to quote differential
    equations as [diff_equa] terms and use [Dequa_facts]' main theorem to solve
    them.

    In order to solve an equation [E(x)]:

    1. we represent it as couple [(env, e)] where:
    - [env] is a [list (sigT infinite_cv_radius)] such that every sequence [an]
    appears only once in [env];
    - [e] is a [diff_equa] term such that [interp_in_R e env x] is isomorphic to
    [E(x)] (the only difference being the proofs used to construct [sum]s and
    [nth_derive]s).

    2. we use [env] in order to normalise the goal using proof-irrelevance
    theorems (e.g. the fact that [sum an r1] is extensionaly equal to [sum an r2]
    so not distinguishing [sum an r1 x] from [sum an r2 x] was harmless).
*)

Require Import List.
Require Import Rsequence_def Rpser_def Rpser_def_simpl Rpser_sums Rpser_derivative Rpser_usual.
Require Import Rfunction_classes.
Require Import Nth_derivative_def Nth_derivative_facts.
Require Import Dequa_def Dequa_facts.

(** * Quoting differential equations *)

(** [isconst s x] yields a boolean value telling you whether [s] is an
    expression that does not depends on [x] or that does.
    Optimisation: our variable [x] will always appear as the last
    argument of the application so we chose a right to left depth-first
    search algorithm. **)

Ltac isconst := fun s x => match s with
  | x     => false
  | ?f ?e =>
    match isconst e x with
      | true  => isconst f x
      | false => false
    end
  | ?y    => true
end.

(** [add_var an rho l] adds the sequence [an] and the proof that its
    radius of convergence is infinite [rho] to the environment and
    returns an integer representing it.
    If [an] is already in the environment (no matter what the proof
    looks like), we do not reinsert it. This allows us to create the
    most general differential equation. **)

Ltac add_var an rho l :=
  let rec aux an rho l n :=
  match l with
    | List.nil                    => constr:(pair n (List.cons (existT _ an rho) List.nil))
    | List.cons (existT _ an _) _ => constr:(pair n l)
    | List.cons ?a ?tl =>
      match aux an rho tl (S n) with
        | (?m , ?tl') => constr:(pair m (List.cons a tl'))
      end
  end in aux an rho l O.

(** [quote_side_equa env s x] quotes the side equation [s] whose variable
    is [x] according to the current environment [env].
    If [s] is a constant with respect to [x] then we do not look at its structure
    and represent it as a [cst s]. If [s] is a kth derivative then we try to find
    [k] and we use the appropriate representation [y p k] where [p] is the
    representation of [s] in the environment.
    Otherwise we deconstruct [s] until we reach either a constant or a function. **)

Ltac quote_side_equa := fun env s x => match isconst s x with
  | true  => constr: (pair env (cst s))
  | false =>
    match constr:(s) with
(* Common constructors for arithmetical operations *)
      | Ropp ?s1       =>
        match quote_side_equa env s1 x with
         | (?env1, ?p) => constr: (pair env1 (opp p))
        end
      | Rmult ?s1 ?s2  =>
        match isconst s1 x with
          | true  =>
            match quote_side_equa env s2 x with
              | (?env1, ?p) => constr: (pair env1 (scal s1 p))
            end
          | false =>
            match isconst s2 x with
              | true  =>
                match quote_side_equa env s1 x with
                  | (?env1, ?p) => constr: (pair env1 (scal s2 p))
                end
              | false => 
                match quote_side_equa env s1 x with
                  | (?env1, ?p) =>
                    match quote_side_equa env1 s2 x with
                      | (?env2, ?q) => constr: (pair env2 (mult p q))
            	    end
                end
	    end
        end
      | Rminus ?s1 ?s2 =>
        match quote_side_equa env s1 x with
          | (?env1, ?p) =>
            match quote_side_equa env1 s2 x with
              | (?env2, ?q) => constr: (pair env2 (min p q))
            end
        end
      | Rplus ?s1 ?s2  =>
        match quote_side_equa env s1 x with
          | (?env1, ?p) =>
            match quote_side_equa env1 s2 x with
              | (?env2, ?q) => constr: (pair env2 (plus p q))
            end
        end
(* Function symbols *)
      | derive (sum ?an ?rho) ?c x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (pair env' (y p 1 1))
        end
      | nth_derive (sum ?an ?rho) ?c x =>
        match add_var an rho env with
          | (?p, ?env') =>
            match type of c with
              | D ?k (sum an rho) => constr: (pair env' (y p k 1))
            end
        end
      | sum ?an ?rho x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (pair env' (y p 0 1))
        end
      | x =>
        match add_var identity_seq identity_infinite_cv_radius env with
          | (?p, ?env') => constr: (pair env' (y p 0 1))
        end
      | derive (sum ?an ?rho) ?c (?a * x) =>
        match add_var an rho env with
          | (?p, ?env') => constr: (pair env' (y p 1 a))
        end
      | nth_derive (sum ?an ?rho) ?c (?a * x) =>
        match add_var an rho env with
          | (?p, ?env') =>
            match type of c with
              | D ?k (sum an rho) => constr: (pair env' (y p k a))
            end
        end
      | sum ?an ?rho (?a * x) =>
        match add_var an rho env with
          | (?p, ?env') => constr: (pair env' (y p 0 a))
        end
(** If everything fails, we output a 404 constant.
    Just for testing; should be removed (TODO) **)
      | _ => constr: (pair env (cst 404))
    end
end.

(** Adhoc lemmas to be moved? **)

Require Import Rfunction_def Rextensionality.

Lemma nth_derive_sum_PI_O : forall an (r1 r2 : infinite_cv_radius an),
  nth_derive (sum an r1) (D_infty_Rpser an r1 O) == sum an r2.
Proof.
intros an r1 r2 ; apply sum_ext ; reflexivity.
Qed.

Lemma nth_derive_sum_PI_O' : forall an (r1 r2 : infinite_cv_radius an),
 (fun x => nth_derive (sum an r1) (D_infty_Rpser an r1 O) (1 * x)) == sum an r2.
Proof.
intros an r1 r2 x ; rewrite Rmult_1_l ; apply nth_derive_sum_PI_O.
Qed.


Lemma nth_derive_sum_PI_1 : forall an (r1 r2 : infinite_cv_radius an) (pr : derivable (sum an r2)),
  nth_derive (sum an r1) (D_infty_Rpser an r1 1%nat) == derive (sum an r2) pr.
Proof.
intros an r1 r2 pr ; apply derive_ext, sum_ext ; reflexivity.
Qed.

Lemma nth_derive_sum_PI_1' : forall an (r1 r2 : infinite_cv_radius an) (pr : derivable (sum an r2)),
  (fun x => nth_derive (sum an r1) (D_infty_Rpser an r1 1%nat) (1 * x)) == derive (sum an r2) pr.
Proof.
intros an r1 r2 pr x ; rewrite Rmult_1_l ; apply nth_derive_sum_PI_1.
Qed.

Lemma nth_derive_sum_PI: forall (n : nat) an (r1 r2 : infinite_cv_radius an) (pr : D n (sum an r2)),
  nth_derive (sum an r1) (D_infty_Rpser an r1 n) == nth_derive (sum an r2) pr.
Proof.
intros n an r1 r2 pr ; apply nth_derive_ext, sum_ext ; reflexivity.
Qed.

Lemma nth_derive_sum_PI': forall (n : nat) an (r1 r2 : infinite_cv_radius an) (pr : D n (sum an r2)),
  (fun x => nth_derive (sum an r1) (D_infty_Rpser an r1 n) (1 * x)) == nth_derive (sum an r2) pr.
Proof.
intros n an r1 r2 pr x ; rewrite Rmult_1_l ; apply nth_derive_sum_PI.
Qed.

(** Normalising the goal **)

Ltac normalize_rec := fun p s x =>
match p with | (existT _ ?an ?rho) =>
match isconst s x with | false =>
  match s with
    | Ropp ?s1 => progress (normalize_rec p s1 x)
    | Rplus ?s1 ?s2 => progress (normalize_rec p s1 x)
    | Rplus ?s1 ?s2 => progress (normalize_rec p s2 x)
    | Rminus ?s1 ?s2 => progress (normalize_rec p s1 x)
    | Rminus ?s1 ?s2 => progress (normalize_rec p s2 x)
    | Rmult ?s1 ?s2 =>
      match isconst s2 x with
        | true => replace (Rmult s1 s2)%R with (Rmult s2 s1)%R by (apply Rmult_comm)
        | false => progress (normalize_rec p s1 x) ; progress (normalize_rec p s2 x)
        | false => progress (normalize_rec p s1 x)
        | false => progress (normalize_rec p s2 x)
      end
    | sum an ?rho2 x => replace (sum an rho2 x)%R with
                        (nth_derive (sum an rho) (D_infty_Rpser an rho O) (1 * x))%R
                        by (apply (nth_derive_sum_PI_O' an rho rho2 x))
    | derive (sum an ?rho2) ?pr x => replace (derive (sum an rho2) pr x)%R with
                        (nth_derive (sum an rho) (D_infty_Rpser an rho 1%nat) (1 * x))%R
                        by (apply (nth_derive_sum_PI_1' an rho rho2 pr x))
    | sum an ?rho2 (?a * x) => replace (sum an rho2 (a * x))%R with
                        (nth_derive (sum an rho) (D_infty_Rpser an rho O) (a * x))%R
                        by (apply (nth_derive_sum_PI_O an rho rho2 (a * x)))
    | derive (sum an ?rho2) ?pr (?a * x) => replace (derive (sum an rho2) pr (a * x))%R with
                        (nth_derive (sum an rho) (D_infty_Rpser an rho 1%nat) (a * x))%R
                        by (apply (nth_derive_sum_PI_1 an rho rho2 pr (a * x)))
(** This case is special: we want to do something iff the nth_derive has not
    the right shape. **)
    | nth_derive (sum an rho) (D_infty_Rpser an rho ?n) x =>
       replace (nth_derive (sum an rho) (D_infty_Rpser an rho n) x)%R with
       (nth_derive (sum an rho) (D_infty_Rpser an rho n) (1 * x))%R
       by (rewrite Rmult_1_l ; reflexivity)
    | nth_derive (sum an ?rho2) ?pr x =>
      match type of pr with | C ?n (sum an rho2) =>
        replace (nth_derive (sum an rho2) pr x)%R with
        (nth_derive (sum an rho) (D_infty_Rpser an rho n) (1 * x))%R
        by (apply nth_derive_sum_PI')
      end
    | nth_derive (sum an rho) (D_infty_Rpser an rho ?n) (?a * x) => idtac
    | nth_derive (sum an ?rho2) ?pr (?a * x) =>
      match type of pr with | C ?n (sum an rho2) =>
        replace (nth_derive (sum an rho2) pr (a * x))%R with
        (nth_derive (sum an rho) (D_infty_Rpser an rho n) (a * x))%R
        by (apply nth_derive_sum_PI)
      end
  end
end
end.

Ltac normalize := fun env s x =>
match env with
  | List.nil => idtac
  | List.cons ?p ?env2 => repeat (normalize_rec p s x) ; normalize env2 s x
end.


Ltac quote_diff_equa := fun x =>
match goal with
  | |- ?s1 = ?s2 =>
   match quote_side_equa (@List.nil (sigT infinite_cv_radius)) s1 x with
    | (?env1, ?p) =>
     match quote_side_equa env1 s2 x with
       | (?env2, ?q) => constr: (pair env2 (p :=: q))
     end
   end
end.

(** Solving an equation **)

Ltac solve_diff_equa_on := fun x =>
let H := fresh "H" in
match quote_diff_equa x with
  | (?env, ?p) =>
    match goal with
      | |- ?s1 = ?s2 => normalize env s1 x ; normalize env s2 x ;
                        cut ([| p |]N (map (@projT1 _ infinite_cv_radius) env)) ;
                        [intro H ; apply (interp_equa_in_N_R _ _ H x) ; clear H | simpl ;
                        repeat rewrite An_expand_1 ; repeat rewrite An_nth_deriv_0 ;
                        repeat rewrite An_nth_deriv_1 ]
    end
end.

Ltac solve_diff_equa :=
let x := fresh "x" in intro x ; solve_diff_equa_on x.


(* TODO *)

(** * Test materials *)
(** TODO: remove everything in this section as soon as the library is
   working *)

Goal forall an (ra rb : infinite_cv_radius an) x, sum an ra x = sum an rb x.
intros an ra rb ; solve_diff_equa ; reflexivity.
Qed.

Goal forall an bn (ra: infinite_cv_radius an) (rb rc: infinite_cv_radius bn)
 (rab: infinite_cv_radius (an + bn + bn)), forall (u x : R),
  (sum (an + bn + bn)%Rseq rab x = sum bn rb x + sum an ra x + sum bn rc x)%R.
intros an bn ra rb rc rab x.
 solve_diff_equa ; intro n ; unfold Rseq_plus ; ring.
Qed.
