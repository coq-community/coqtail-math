From Coq Require Import ZArith Znumtheory Lia Psatz List Bool.
From Coqtail Require Import Zprime MillerRabin.

Import ListNotations.
Open Scope Z_scope.

(** Checking naively for <= 1373652 would take a few hours, so we
    split the computation *)

Lemma MR_range_split l a b c : a <= b <= c -> MR_range l a c = MR_range l a b && MR_range l (1 + b) c.
Proof.
  intros abc.
  apply eq_true_iff_eq.
  rewrite andb_true_iff.
  rewrite 3 MR_range_spec.
  split.
  - intros ac; split; intros n bn; apply ac; lia.
  - intros [ab bc]; intros n bn. destruct (Z_lt_ge_dec n (1 + b)). apply ab; lia. apply bc; lia.
Qed.

Lemma MR_range_split' l a b c : a <= b <= c -> MR_range l a b = true -> MR_range l (1 + b) c = true -> MR_range l a c = true.
Proof.
  intros abc.
  rewrite (MR_range_split _ a b c); auto.
  now intros -> ->.
Qed.

(** First technique to parallelize computation: using "par:" *)

Local Ltac halve :=
  match goal with
    |- MR_range ?l ?a ?b = true =>
    pose (c := (a + b) / 2);
    vm_compute in c;
    apply (MR_range_split' l a c); [ easy | | simpl "+" ]; subst c
  end.

Lemma miller_rabin_2_3_par n : n <= 100000 -> miller_rabin [2; 3] n = primeb n.
Proof.
  apply MR_range_spec_2.
  (* Time native_compute. (* 48 secs *) reflexivity. *)

  halve; halve; halve; halve; halve.
Abort.
(*
  Time par: abstract (native_compute; reflexivity). (* 80 seconds : more ! *)
Qed. (* instant, when using abstract, but the Qed work is done sequentially anyway, it seems. *)
*)

(* Same for 1373652, note that the speed up is always less that 2 because of the Qed or abstract

Lemma miller_rabin_2_3_1373652_par n : n <= 1373652 -> miller_rabin [2; 3] n = primeb n.
Proof.
  apply MR_range_spec_2.
  halve; halve; halve; halve; halve; halve. (* 64 subgoals *)
  (* Time par: native_compute; reflexivity. (* 533 seconds -- njobs=8 *) *)
  Time par: abstract (native_compute; reflexivity). (* 2110 seconds ~= 533+1700 *)
Time Qed. (* 1700 seconds (0.2 with abstract) *)
*)

(** Other technique using async proofs (only coqc and coqide, the
    standard proof general is not there yet AFAIK)

To activate, be sure those lines are in your _CoqProject. This should
activate 8 threads for coqide and when make runs coqc.

-arg -async-proofs
-arg on
-arg -async-proofs-j
-arg 8

*)

Definition max := 1373652.
Definition d := max / 99.
Definition part n := MR_range [2; 3] (d * n) (Z.min max (d * n + d - 1)) = true.

Lemma M00 : part 00. Proof using. abstract (native_compute; idtac "00 done"; reflexivity). Qed.
Lemma M01 : part 01. Proof using. abstract (native_compute; idtac "01 done"; reflexivity). Qed.
Lemma M02 : part 02. Proof using. abstract (native_compute; idtac "02 done"; reflexivity). Qed.
Lemma M03 : part 03. Proof using. abstract (native_compute; idtac "03 done"; reflexivity). Qed.
Lemma M04 : part 04. Proof using. abstract (native_compute; idtac "04 done"; reflexivity). Qed.
Lemma M05 : part 05. Proof using. abstract (native_compute; idtac "05 done"; reflexivity). Qed.
Lemma M06 : part 06. Proof using. abstract (native_compute; idtac "06 done"; reflexivity). Qed.
Lemma M07 : part 07. Proof using. abstract (native_compute; idtac "07 done"; reflexivity). Qed.
Lemma M08 : part 08. Proof using. abstract (native_compute; idtac "08 done"; reflexivity). Qed.
Lemma M09 : part 09. Proof using. abstract (native_compute; idtac "09 done"; reflexivity). Qed.
Lemma M10 : part 10. Proof using. abstract (native_compute; idtac "10 done"; reflexivity). Qed.
Lemma M11 : part 11. Proof using. abstract (native_compute; idtac "11 done"; reflexivity). Qed.
Lemma M12 : part 12. Proof using. abstract (native_compute; idtac "12 done"; reflexivity). Qed.
Lemma M13 : part 13. Proof using. abstract (native_compute; idtac "13 done"; reflexivity). Qed.
Lemma M14 : part 14. Proof using. abstract (native_compute; idtac "14 done"; reflexivity). Qed.
Lemma M15 : part 15. Proof using. abstract (native_compute; idtac "15 done"; reflexivity). Qed.
Lemma M16 : part 16. Proof using. abstract (native_compute; idtac "16 done"; reflexivity). Qed.
Lemma M17 : part 17. Proof using. abstract (native_compute; idtac "17 done"; reflexivity). Qed.
Lemma M18 : part 18. Proof using. abstract (native_compute; idtac "18 done"; reflexivity). Qed.
Lemma M19 : part 19. Proof using. abstract (native_compute; idtac "19 done"; reflexivity). Qed.
Lemma M20 : part 20. Proof using. abstract (native_compute; idtac "20 done"; reflexivity). Qed.
Lemma M21 : part 21. Proof using. abstract (native_compute; idtac "21 done"; reflexivity). Qed.
Lemma M22 : part 22. Proof using. abstract (native_compute; idtac "22 done"; reflexivity). Qed.
Lemma M23 : part 23. Proof using. abstract (native_compute; idtac "23 done"; reflexivity). Qed.
Lemma M24 : part 24. Proof using. abstract (native_compute; idtac "24 done"; reflexivity). Qed.
Lemma M25 : part 25. Proof using. abstract (native_compute; idtac "25 done"; reflexivity). Qed.
Lemma M26 : part 26. Proof using. abstract (native_compute; idtac "26 done"; reflexivity). Qed.
Lemma M27 : part 27. Proof using. abstract (native_compute; idtac "27 done"; reflexivity). Qed.
Lemma M28 : part 28. Proof using. abstract (native_compute; idtac "28 done"; reflexivity). Qed.
Lemma M29 : part 29. Proof using. abstract (native_compute; idtac "29 done"; reflexivity). Qed.
Lemma M30 : part 30. Proof using. abstract (native_compute; idtac "30 done"; reflexivity). Qed.
Lemma M31 : part 31. Proof using. abstract (native_compute; idtac "31 done"; reflexivity). Qed.
Lemma M32 : part 32. Proof using. abstract (native_compute; idtac "32 done"; reflexivity). Qed.
Lemma M33 : part 33. Proof using. abstract (native_compute; idtac "33 done"; reflexivity). Qed.
Lemma M34 : part 34. Proof using. abstract (native_compute; idtac "34 done"; reflexivity). Qed.
Lemma M35 : part 35. Proof using. abstract (native_compute; idtac "35 done"; reflexivity). Qed.
Lemma M36 : part 36. Proof using. abstract (native_compute; idtac "36 done"; reflexivity). Qed.
Lemma M37 : part 37. Proof using. abstract (native_compute; idtac "37 done"; reflexivity). Qed.
Lemma M38 : part 38. Proof using. abstract (native_compute; idtac "38 done"; reflexivity). Qed.
Lemma M39 : part 39. Proof using. abstract (native_compute; idtac "39 done"; reflexivity). Qed.
Lemma M40 : part 40. Proof using. abstract (native_compute; idtac "40 done"; reflexivity). Qed.
Lemma M41 : part 41. Proof using. abstract (native_compute; idtac "41 done"; reflexivity). Qed.
Lemma M42 : part 42. Proof using. abstract (native_compute; idtac "42 done"; reflexivity). Qed.
Lemma M43 : part 43. Proof using. abstract (native_compute; idtac "43 done"; reflexivity). Qed.
Lemma M44 : part 44. Proof using. abstract (native_compute; idtac "44 done"; reflexivity). Qed.
Lemma M45 : part 45. Proof using. abstract (native_compute; idtac "45 done"; reflexivity). Qed.
Lemma M46 : part 46. Proof using. abstract (native_compute; idtac "46 done"; reflexivity). Qed.
Lemma M47 : part 47. Proof using. abstract (native_compute; idtac "47 done"; reflexivity). Qed.
Lemma M48 : part 48. Proof using. abstract (native_compute; idtac "48 done"; reflexivity). Qed.
Lemma M49 : part 49. Proof using. abstract (native_compute; idtac "49 done"; reflexivity). Qed.
Lemma M50 : part 50. Proof using. abstract (native_compute; idtac "50 done"; reflexivity). Qed.
Lemma M51 : part 51. Proof using. abstract (native_compute; idtac "51 done"; reflexivity). Qed.
Lemma M52 : part 52. Proof using. abstract (native_compute; idtac "52 done"; reflexivity). Qed.
Lemma M53 : part 53. Proof using. abstract (native_compute; idtac "53 done"; reflexivity). Qed.
Lemma M54 : part 54. Proof using. abstract (native_compute; idtac "54 done"; reflexivity). Qed.
Lemma M55 : part 55. Proof using. abstract (native_compute; idtac "55 done"; reflexivity). Qed.
Lemma M56 : part 56. Proof using. abstract (native_compute; idtac "56 done"; reflexivity). Qed.
Lemma M57 : part 57. Proof using. abstract (native_compute; idtac "57 done"; reflexivity). Qed.
Lemma M58 : part 58. Proof using. abstract (native_compute; idtac "58 done"; reflexivity). Qed.
Lemma M59 : part 59. Proof using. abstract (native_compute; idtac "59 done"; reflexivity). Qed.
Lemma M60 : part 60. Proof using. abstract (native_compute; idtac "60 done"; reflexivity). Qed.
Lemma M61 : part 61. Proof using. abstract (native_compute; idtac "61 done"; reflexivity). Qed.
Lemma M62 : part 62. Proof using. abstract (native_compute; idtac "62 done"; reflexivity). Qed.
Lemma M63 : part 63. Proof using. abstract (native_compute; idtac "63 done"; reflexivity). Qed.
Lemma M64 : part 64. Proof using. abstract (native_compute; idtac "64 done"; reflexivity). Qed.
Lemma M65 : part 65. Proof using. abstract (native_compute; idtac "65 done"; reflexivity). Qed.
Lemma M66 : part 66. Proof using. abstract (native_compute; idtac "66 done"; reflexivity). Qed.
Lemma M67 : part 67. Proof using. abstract (native_compute; idtac "67 done"; reflexivity). Qed.
Lemma M68 : part 68. Proof using. abstract (native_compute; idtac "68 done"; reflexivity). Qed.
Lemma M69 : part 69. Proof using. abstract (native_compute; idtac "69 done"; reflexivity). Qed.
Lemma M70 : part 70. Proof using. abstract (native_compute; idtac "70 done"; reflexivity). Qed.
Lemma M71 : part 71. Proof using. abstract (native_compute; idtac "71 done"; reflexivity). Qed.
Lemma M72 : part 72. Proof using. abstract (native_compute; idtac "72 done"; reflexivity). Qed.
Lemma M73 : part 73. Proof using. abstract (native_compute; idtac "73 done"; reflexivity). Qed.
Lemma M74 : part 74. Proof using. abstract (native_compute; idtac "74 done"; reflexivity). Qed.
Lemma M75 : part 75. Proof using. abstract (native_compute; idtac "75 done"; reflexivity). Qed.
Lemma M76 : part 76. Proof using. abstract (native_compute; idtac "76 done"; reflexivity). Qed.
Lemma M77 : part 77. Proof using. abstract (native_compute; idtac "77 done"; reflexivity). Qed.
Lemma M78 : part 78. Proof using. abstract (native_compute; idtac "78 done"; reflexivity). Qed.
Lemma M79 : part 79. Proof using. abstract (native_compute; idtac "79 done"; reflexivity). Qed.
Lemma M80 : part 80. Proof using. abstract (native_compute; idtac "80 done"; reflexivity). Qed.
Lemma M81 : part 81. Proof using. abstract (native_compute; idtac "81 done"; reflexivity). Qed.
Lemma M82 : part 82. Proof using. abstract (native_compute; idtac "82 done"; reflexivity). Qed.
Lemma M83 : part 83. Proof using. abstract (native_compute; idtac "83 done"; reflexivity). Qed.
Lemma M84 : part 84. Proof using. abstract (native_compute; idtac "84 done"; reflexivity). Qed.
Lemma M85 : part 85. Proof using. abstract (native_compute; idtac "85 done"; reflexivity). Qed.
Lemma M86 : part 86. Proof using. abstract (native_compute; idtac "86 done"; reflexivity). Qed.
Lemma M87 : part 87. Proof using. abstract (native_compute; idtac "87 done"; reflexivity). Qed.
Lemma M88 : part 88. Proof using. abstract (native_compute; idtac "88 done"; reflexivity). Qed.
Lemma M89 : part 89. Proof using. abstract (native_compute; idtac "89 done"; reflexivity). Qed.
Lemma M90 : part 90. Proof using. abstract (native_compute; idtac "90 done"; reflexivity). Qed.
Lemma M91 : part 91. Proof using. abstract (native_compute; idtac "91 done"; reflexivity). Qed.
Lemma M92 : part 92. Proof using. abstract (native_compute; idtac "92 done"; reflexivity). Qed.
Lemma M93 : part 93. Proof using. abstract (native_compute; idtac "93 done"; reflexivity). Qed.
Lemma M94 : part 94. Proof using. abstract (native_compute; idtac "94 done"; reflexivity). Qed.
Lemma M95 : part 95. Proof using. abstract (native_compute; idtac "95 done"; reflexivity). Qed.
Lemma M96 : part 96. Proof using. abstract (native_compute; idtac "96 done"; reflexivity). Qed.
Lemma M97 : part 97. Proof using. abstract (native_compute; idtac "97 done"; reflexivity). Qed.
Lemma M98 : part 98. Proof using. abstract (native_compute; idtac "98 done"; reflexivity). Qed.
Lemma M99 : part 99. Proof using. abstract (native_compute; idtac "99 done"; reflexivity). Qed.

Lemma miller_rabin_2_3_1373652 n : n <= max -> miller_rabin [2; 3] n = primeb n.
Proof using.
  apply MR_range_spec_0.
  Local Ltac p pr := refine (MR_range_split' _ _ _ _ _ pr _); [ split; discriminate | ].

  p M00. p M01. p M02. p M03. p M04. p M05. p M06. p M07. p M08. p M09.
  p M10. p M11. p M12. p M13. p M14. p M15. p M16. p M17. p M18. p M19.
  p M20. p M21. p M22. p M23. p M24. p M25. p M26. p M27. p M28. p M29.
  p M30. p M31. p M32. p M33. p M34. p M35. p M36. p M37. p M38. p M39.
  p M40. p M41. p M42. p M43. p M44. p M45. p M46. p M47. p M48. p M49.
  p M50. p M51. p M52. p M53. p M54. p M55. p M56. p M57. p M58. p M59.
  p M60. p M61. p M62. p M63. p M64. p M65. p M66. p M67. p M68. p M69.
  p M70. p M71. p M72. p M73. p M74. p M75. p M76. p M77. p M78. p M79.
  p M80. p M81. p M82. p M83. p M84. p M85. p M86. p M87. p M88. p M89.
  p M90. p M91. p M92. p M93. p M94. p M95. p M96. p M97. p M98. p M99.

  idtac "all done".
  reflexivity.
Qed.
