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
Require Import C_n_def C_n_usual.
Require Import Nth_derivative_def.
Require Import Dequa_def Dequa_facts.

(** * Quoting differential equations *)

(** [isconst s x] yields a boolean value telling you whether [s] is an
    expression that does not depends on [x] or that does.
    Optimisation: our variable [x] will always appear as the last
    argument of the application so we chose a right to left depth-first
    search algorithm. **)

Ltac isconst := fun s x => match constr: s with
  | x     => constr: false
  | ?f ?e =>
    match isconst e x with
      | true  => isconst f x
      | false => constr: false
    end
  | ?y    => constr: true
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
    | List.nil                    => constr: (n , List.cons (existT _ an rho) List.nil)
    | List.cons (existT _ an _) _ => constr: (n , l)
    | List.cons ?a ?tl =>
      match aux an rho tl (S n) with
        | (?m , ?tl') => constr: (m , List.cons a tl')
      end
  end in aux an rho l O.

(** [rec_quote_side_equa env s x] quotes the side equation [s] whose variable
    is [x] according to the current environment [env].
    If [s] is a constant with respect to [x] then we do not look at its structure
    and represent it as a [cst s]. If [s] is a kth derivative then we try to find
    [k] and we use the appropriate representation [y p k] where [p] is the
    representation of [s] in the environment.
    Otherwise we deconstruct [s] until we reach either a constant or a function. **)

Ltac rec_quote_side_equa := fun env s x => match isconst s x with
  | true  => constr: (env, cst s)
  | false =>
    match constr: s with
(* Common constructors for arithmetical operations *)
      | Ropp ?s1       =>
        match rec_quote_side_equa env s1 x with
         | (?env1, ?p) => constr: (env1, opp p)
        end
      | Rmult ?s1 ?s2  =>
        match isconst s1 x with
          | true  =>
            match rec_quote_side_equa env s2 x with
              | (?env1, ?p) => constr: (env1, scal s1 p)
            end
          | false =>
            match isconst s2 x with
              | true  =>
                match rec_quote_side_equa env s1 x with
                  | (?env1, ?p) => constr: (env1, scal s2 p)
                end
            end
        end
      | Rminus ?s1 ?s2 =>
        match rec_quote_side_equa env s1 x with
          | (?env1, ?p) =>
            match rec_quote_side_equa env1 s2 x with
              | (?env2, ?q) => constr: (env2, min p q)
            end
        end
      | Rplus ?s1 ?s2  =>
        match rec_quote_side_equa env s1 x with
          | (?env1, ?p) =>
            match rec_quote_side_equa env1 s2 x with
              | (?env2, ?q) => constr: (env2, plus p q)
            end
        end
(* Function symbols *)
      | derive (sum ?an ?rho) ?c x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (env', y p 1)
        end
      | nth_derive (sum ?an ?rho) ?c x =>
        match add_var an rho env with
          | (?p, ?env') =>
            match type of c with
              | C ?k (sum an rho) => constr: (env', y p k)
            end
        end
      | sum ?an ?rho x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (env', y p 0)
        end
      | x =>
        match add_var identity_seq identity_infinite_cv_radius env with
          | (?p, ?env') => constr: (env', y p 0)
        end
(** If everything fails, we output a 404 constant.
    Just for testing; should be removed (TODO) **)
      | _ => constr: (env, cst 404)
    end
end.

Ltac quote_diff_equa := fun x =>
match goal with
  | |- ?s1 = ?s2 =>
   match rec_quote_side_equa (@List.nil (sigT infinite_cv_radius)) s1 x with
    | (?env1, ?p) =>
     match rec_quote_side_equa env1 s2 x with
       | (?env2, ?q) => constr: (env2, p :=: q)
     end
   end
end.

Ltac quote_diff_equa_in := fun H =>
let x := fresh "x" in intro x ; match quote_diff_equa x with | (_, ?p) => pose (H := p) end.

Ltac solve_diff_equa :=
  let H := fresh "H" in
  let H' := fresh "H" in
  let x := fresh "x" in
  intro x ;
  match quote_diff_equa x with
   | (?env, ?de) => cut ([| de |]N (map (@projT1 _ infinite_cv_radius) env)) ;
     [intro H' ; assert (H := interp_equa_in_N_R _ _ H' x) ; clear H' |]
  end.


(** * Normalizing the goal *)

(* TODO *)

(** * Test materials *)
(** TODO: remove everything in this section as soon as the library is
   working *)

Ltac quote_side_equa := fun s x =>
match rec_quote_side_equa (@List.nil (sigT infinite_cv_radius)) s x with
  | (?env, ?p) => constr: p
end.

Goal forall an bn cn, infinite_cv_radius an -> infinite_cv_radius bn ->
 infinite_cv_radius cn -> True.
 intros an bn cn ra rb rc.
 pose (x := 3).
 let k := quote_side_equa (sum an ra x)%R x in pose (H1 := k).
 let k := quote_side_equa
  (- (sum an ra x  + (nth_derive (sum cn rc) (C_infty_Rpser cn rc 3%nat) x))
  - (sum bn rb x + derive (sum cn rc) (derivable_sum cn rc) x) * 6)%R x in
 pose (H := k).
 exact I.
Qed.

Goal forall an bn (ra: infinite_cv_radius an) (rb: infinite_cv_radius bn)
 (rab: infinite_cv_radius (an + bn)), forall (u x : R),
  (sum (an + bn)%Rseq rab x = sum an ra x + sum bn rb x)%R.
intros an bn ra rb rab x ; solve_diff_equa ; [apply H |].
 intro n ; simpl ; unfold Rseq_plus ; repeat rewrite An_nth_deriv_0 ; reflexivity.
Qed.
