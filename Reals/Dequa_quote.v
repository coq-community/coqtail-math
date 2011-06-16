Require Import List.
Require Import Rsequence_def Rpser_def Rpser_sums.
Require Import Nth_derivative_def.
Require Import Dequa_def.


(** [isconst s x] yields a boolean value telling you whether [s] is
    an expression that does not depends on [x] or that does.
    Optimisation: our variable [x] will always appear as the last
    argument of the application. *)

Ltac isconst := fun s x => match constr: s with
  | x     => constr: false
  | ?f ?e =>
    match isconst e x with
      | true  => isconst f x
      | false => constr: false
    end
  | ?y    => constr: true
end.

(**
    [add_var an rho l] adds the sequence [an] and the proof that its
    radius of convergence is infinite [rho] to the environment and
    returns an integer representing it.
    If [an] is already in the environment (no matter what the proof
    look like), we do not reinsert it. This allows us to create the
    more general differential equation (and will probably cause
    problems when going back to the unquoted form...).
**)

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

(** TODO: propagate the environment! *)

Ltac rec_quote_side_equa env := fun s x => match isconst s x with
  | true  => constr: (cst s)
  | false =>
    match constr: s with
      | Ropp ?s1       =>
        let p := rec_quote_side_equa env s1 x in constr: (opp p)
      | Rmult ?s1 ?s2  =>
        match isconst s1 x with
          | true  => let p := rec_quote_side_equa env s2 x in constr: (scal s1 p)
          | false => fail
        end
      | Rminus ?s1 ?s2 =>
        let p := rec_quote_side_equa env s1 x in
        let q := rec_quote_side_equa env s2 x in constr: (min p q)
      | Rplus ?s1 ?s2  =>
        let p := rec_quote_side_equa env s1 x in
        let q := rec_quote_side_equa env s2 x in constr: (plus p q)
(** HERE: we need to extract the derivative *)
      | nth_derive (sum ?an ?rho) ?c x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (y p 1)
        end
      | sum ?an ?rho x =>
        match add_var an rho env with
          | (?p, ?env') => constr: (y p 0)
        end
(** If everything fails, we output a 404 constant.
    Just for testing; should be removed (TODO) **)
      | _ => constr: (cst 404)
    end
end.

Ltac quote_side_equa := rec_quote_side_equa (@List.nil (sigT infinite_cv_radius)).

(** Test case *)

Goal forall an bn, infinite_cv_radius an -> infinite_cv_radius bn -> True.
 intros an bn ra rb.
 pose (x := 3).
(* let k := quote_side_equa (sum an ra x)%R x in pose (H := k). *)
 let k := quote_side_equa (- (sum an ra x + 3) - 6 * (sum bn rb x))%R x in
 pose (H := k).
 exact I.
Qed.




