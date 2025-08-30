From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra zmodp.
Import GroupScope Order.TTheory GRing.Theory Num.Theory.
Require Import utils. 
From vass Require Import algebra_ext matrix_ext.

(******************************************************************************)
(*  Linear rational arithmetic and Fourier-Motzkin variable elimination       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LRA.

Variable (R : realFieldType).

(*TBD: move to library 
  Probable coercion Order.type -> R:RealFieldType*)
Lemma ltr_asym : forall (x y:R), false = (x < y < x)%R.
Proof.
by move => x y; rewrite lt_asym.
Qed.

Section QFLRA.

Variable (dim : nat).

Inductive QFLRA_formula :=
  | QFLRA_neg   of QFLRA_formula
  | QFLRA_and   of QFLRA_formula & QFLRA_formula
  | QFLRA_or    of QFLRA_formula & QFLRA_formula
  | QFLRA_leq   of 'cV[R]_dim. (*  QFLRA_leq : forall _ : matrix R dim 1, QFLRA_formula. *)


(* Equal formulas need to be formally equal (no meaning on operators )*)
Fixpoint eq_QFLRA_formula (f1 f2 : QFLRA_formula) :=
  match f1, f2 with
    | QFLRA_neg f1', QFLRA_neg f2' => eq_QFLRA_formula f1' f2'
    | QFLRA_and f1l f1r, QFLRA_and f2l f2r =>
      eq_QFLRA_formula f1l f2l && eq_QFLRA_formula f1r f2r
    | QFLRA_or f1l f1r, QFLRA_or f2l f2r =>
      eq_QFLRA_formula f1l f2l && eq_QFLRA_formula f1r f2r
    | QFLRA_leq t1, QFLRA_leq t2 => t1 == t2
    | _, _ => false
  end.

Lemma eq_QFLRA_formulaP : Equality.axiom eq_QFLRA_formula.
Proof.
move=> f1 f2; apply/(iffP idP) => [| <-].
- by elim: f1 f2 =>
    [f1' IH | f1l IHl f1r IHr | f1l IHl f1r IHr | t1]
    [//= f2' /IH -> | | | //= t2 /eqP ->]
    //= f2l f2r /andP [] /IHl -> /IHr ->.
- by elim: f1 => //= [f1l -> | f1l ->] *; rewrite ?eqxx.
Defined.

HB.instance Definition _ := @hasDecEq.Build _ _ eq_QFLRA_formulaP .

End QFLRA.

Inductive LRA_formula (dim : nat) :=
  | LRA_forall  of LRA_formula (1 + dim)
  | LRA_exists  of LRA_formula (1 + dim)
  | LRA_neg     of LRA_formula dim
  | LRA_and     of LRA_formula dim & LRA_formula dim
  | LRA_or      of LRA_formula dim & LRA_formula dim
  | LRA_imply   of LRA_formula dim & LRA_formula dim
  | LRA_leq     of 'cV[R]_dim. (*  LRA_leq : forall _ : matrix R dim 1, LRA_formula. *)


(* Uses pair_eqP in eqtype.v circa line 812 section ProdEqType *)
Fact LRA_literal_eqP dim :  @Equality.axiom (bool * 'cV[R]_dim)%type pair_eq.
Proof. apply pair_eqP. Qed.

Section LRA_again.

Variable (dim:nat).

(* This does not bring anything new ... but is OK for HB *)
HB.instance Definition _ := @hasDecEq.Build _ _  (@LRA_literal_eqP dim ).

End LRA_again.

Definition LRA_literal dim:= (bool * 'cV[R]_dim)%type.

(* Here we extract the scalar from a 1x1 'scalar produc' matrix *)
Definition LRA_interpret_af dim (I f : 'cV[R]_dim) := ((f^T *m I) 0 0)%R.


(* Check the role of the boolean first arg ? specify exact/with some margin comparison 
   Arises first in  NF_neg_CNF below!
? *)
Definition LRA_interpret_literal dim (I : 'cV_dim) (f : LRA_literal dim) :=
  (0%R < LRA_interpret_af I f.2 ?<= if f.1)%O.

(* Recursion on interpretation of LRA formula *)
Lemma LRA_af_recl dim (I f : 'cV_(1 + dim)) :
  LRA_interpret_af I f =
  (f 0 0 * I 0 0 + LRA_interpret_af (dsubmx I) (dsubmx f))%R.
Proof.
(* This is the blow by blow account ...*)
rewrite /LRA_interpret_af -{1}(hsubmxK f^T) -{1}(vsubmxK I) .
rewrite mul_row_col. (* product by blocks*)
rewrite  2!mxE.      (* reduce to computation of single element (0,0) by summation on row/col*)
rewrite big_ord_recl. (* extract first elt and recurse on sum*)
rewrite big_ord0. (* sum on empty *)
rewrite 3!mxE addr0 lshift0.
rewrite trmx_dsub. (* deal with transposition (dsubmx f)^T  -> rsubmx f^T *)
exact: Logic.eq_refl.
Qed.

Lemma LRA_interpret_af_add dim (I f1 f2 : 'cV_dim) :
  (LRA_interpret_af I (f1 + f2) =
   LRA_interpret_af I f1 + LRA_interpret_af I f2)%R.
Proof.
 by rewrite /LRA_interpret_af;
 rewrite linearD; (* transpose linearity *)
 rewrite mulmxDl;  (* matrix mul distributes ... again linearity*)
 rewrite mxE //=.
 Qed.

Lemma LRA_interpret_af_opp dim (I f : 'cV_dim) :
  (LRA_interpret_af I (- f) = - LRA_interpret_af I f)%R.
Proof. by rewrite /LRA_interpret_af linearN mulNmx mxE. Qed.

(* Interpretation (recursive) as Prop of the logic *)
Fixpoint LRA_interpret_formula'
  dim (f : LRA_formula dim) : 'cV[R]_dim -> Prop :=
  match f with
  | LRA_forall f' => fun I =>
    forall x, LRA_interpret_formula' f' (col_mx (const_mx x) I)
  | LRA_exists f' => fun I =>
    exists x, LRA_interpret_formula' f' (col_mx (const_mx x) I)
  | LRA_neg f' => fun I => ~ LRA_interpret_formula' f' I
  | LRA_and f1 f2 => fun I =>
    LRA_interpret_formula' f1 I /\ LRA_interpret_formula' f2 I
  | LRA_or f1 f2 => fun I =>
    LRA_interpret_formula' f1 I \/ LRA_interpret_formula' f2 I
  | LRA_imply f1 f2 => fun I =>
    LRA_interpret_formula' f1 I -> LRA_interpret_formula' f2 I
  | LRA_leq t => fun I => (0 <= \sum_i t i 0 * I i 0)%R
  end.

Notation LRA_interpret_formula I f := (@LRA_interpret_formula' _ f I).

(* Interpretation of expressions *)
Fixpoint QFLRA_interpret_formula
  dim (I : 'cV_dim) (f : QFLRA_formula dim) : bool :=
  match f with
    | QFLRA_neg f       => ~~ QFLRA_interpret_formula I f
    | QFLRA_and f1 f2   => QFLRA_interpret_formula I f1 &&
                           QFLRA_interpret_formula I f2
    | QFLRA_or f1 f2    => QFLRA_interpret_formula I f1 ||
                           QFLRA_interpret_formula I f2
    | QFLRA_leq t       => (0 <= (t^T *m I) 0 0)%R
  end.

(* Top in lattice *)
Definition QFLRA_top dim : QFLRA_formula dim := QFLRA_leq 0%R.
Arguments QFLRA_top {dim}.

(* Semantic interpretation of Top *)
Lemma QFLRA_top_true dim (I : 'cV_dim) : QFLRA_interpret_formula I QFLRA_top.
Proof. by rewrite /= trmx0 mul0mx mxE. Qed.

(* Bottom in lattice *)
Definition QFLRA_bot dim : QFLRA_formula dim := QFLRA_neg QFLRA_top.
Arguments QFLRA_bot {dim}.

Lemma QFLRA_bot_false dim (I : 'cV_dim) :
  QFLRA_interpret_formula I QFLRA_bot = false.
Proof. by move: (QFLRA_top_true I) =>/=  ->. Qed.

Definition NF_neg dim (fss : seq (seq (LRA_literal dim))) :=
  [seq [seq (negb f.1, - f.2)%R | f : LRA_literal dim <- fs] |
   fs <- fss].

(** Negation and quantifiers; Here lss : seq (seq (LRA_literal dim))                              *)
Lemma NF_neg_CNF dim (I : 'cV_dim) lss :
  has (all (LRA_interpret_literal I)) (NF_neg lss) =
  ~~ all (has (LRA_interpret_literal I)) lss.
Proof.
rewrite /NF_neg /LRA_interpret_literal -has_predC has_map.
apply/eq_in_has => /= afs _; rewrite -all_predC all_map.
apply/eq_in_all => -[f t] _ /= ; rewrite lteifNE //=.
by rewrite LRA_interpret_af_opp //=; case: f =>//=; congr (~~ _); 
  [rewrite oppr_le0 | rewrite oppr_lt0].
Qed.

Lemma NF_neg_DNF dim (I : 'cV_dim) lss :
  all (has (LRA_interpret_literal I)) (NF_neg lss) =
  ~~ has (all (LRA_interpret_literal I)) lss.
Proof.
rewrite /NF_neg /LRA_interpret_literal -all_predC all_map.
apply/eq_in_all => /= afs _; rewrite -has_predC has_map.
apply/eq_in_has => -[f t] _ /=; rewrite lteifNE /LRA_interpret_af //= linearN mulNmx mxE.
congr (~~ _); case: f => //=; by [rewrite oppr_le0 | rewrite oppr_lt0].
Qed.

Fixpoint
  QFLRA_DNF dim (f : QFLRA_formula dim) : seq (seq (LRA_literal dim)) :=
  match f with
    | QFLRA_neg f' => NF_neg (QFLRA_CNF f')
    | QFLRA_and f1 f2 =>
      [seq fs1 ++ fs2 | fs1 <- QFLRA_DNF f1, fs2 <- QFLRA_DNF f2]
    | QFLRA_or f1 f2 => QFLRA_DNF f1 ++ QFLRA_DNF f2
    | QFLRA_leq f' => [:: [:: (true, f')]]
  end with
  QFLRA_CNF dim (f : QFLRA_formula dim) : seq (seq (LRA_literal dim)) :=
  match f with
    | QFLRA_neg f' => NF_neg (QFLRA_DNF f')
    | QFLRA_and f1 f2 => QFLRA_CNF f1 ++ QFLRA_CNF f2
    | QFLRA_or f1 f2 =>
      [seq fs1 ++ fs2 | fs1 <- QFLRA_CNF f1, fs2 <- QFLRA_CNF f2]
    | QFLRA_leq f' => [:: [:: (true, f')]]
  end.

Lemma QFLRA_NF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :
  (has (all (LRA_interpret_literal I)) (QFLRA_DNF f) =
     QFLRA_interpret_formula I f) *
  (all (has (LRA_interpret_literal I)) (QFLRA_CNF f) =
     QFLRA_interpret_formula I f).
Proof.
elim: f => /=.
- by move=> q [] {3}<- <-; rewrite NF_neg_CNF NF_neg_DNF.
- move=> q1 [] {2}<- <- q2 [] {2}<- <-; split; last by rewrite all_cat.
  elim: (QFLRA_DNF q1) => //= qs qss IH.
  rewrite has_cat {}IH andb_orl; congr orb.
  elim: (QFLRA_DNF q2); rewrite /= ?andbF => // qs' qss' IH.
  by rewrite all_cat {}IH andb_orr.
- move=> q1 [] {2}<- <- q2 [] {2}<- <-; split; first by rewrite has_cat.
  elim: (QFLRA_CNF q1) => //= qs qss IH.
  rewrite all_cat {}IH orb_andl; congr andb.
  elim: (QFLRA_CNF q2); rewrite /= ?orbT => // qs' qss' IH.
  by rewrite has_cat {}IH orb_andr.
- by move=> f; rewrite !andbT !orbF /=.
Qed.

Definition QFLRA_DNF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :=
  (QFLRA_NF_correctness I f).1.

Definition QFLRA_CNF_correctness dim (I : 'cV_dim) (f : QFLRA_formula dim) :=
  (QFLRA_NF_correctness I f).2.

Definition QFLRA_l2f dim (l : LRA_literal dim) :=
  if l.1 then QFLRA_leq l.2 else QFLRA_neg (QFLRA_leq (- l.2)%R).

Lemma QFLRA_l2f_correctness dim (I : 'cV_dim) (l : LRA_literal dim) :
  LRA_interpret_literal I l = QFLRA_interpret_formula I (QFLRA_l2f l).
Proof.
rewrite /QFLRA_l2f /LRA_interpret_literal; case: l.1 => //=.
rewrite -ltNge -subr_lt0 sub0r; congr (_ < _)%R.
rewrite /LRA_interpret_af  linearN mulNmx !mxE =>//=.
Qed.

Definition QFLRA_unDNF dim (lss : seq (seq (LRA_literal dim))) :=
  foldr (fun ls => QFLRA_or
                     (foldr (fun l => QFLRA_and (QFLRA_l2f l)) QFLRA_top ls))
        QFLRA_bot lss.

Lemma QFLRA_unDNF_correctness
  dim (I : 'cV_dim) (lss : seq (seq (LRA_literal dim))) :
  has (all (LRA_interpret_literal I)) lss =
  QFLRA_interpret_formula I (QFLRA_unDNF lss).
Proof.
elim: lss; first by rewrite /foldr QFLRA_bot_false.
move=> /= ls lss ->; congr orb.
elim: ls {lss}; first by rewrite /foldr QFLRA_top_true.
move=> /= l ls ->; congr andb; exact: QFLRA_l2f_correctness.
Qed.

Definition exists_conj_elim
  dim (ls : seq (LRA_literal (1 + dim))) : seq (LRA_literal dim) :=
  let lsp := [seq l : LRA_literal (1 + dim) <- ls | (0 < l.2 0 0)]%R in
    (* - (a_1 x_1 + ... + a_n x_n) <<= a_0 x_0 *)
  let lsn := [seq l : LRA_literal (1 + dim) <- ls | (0 > l.2 0 0)]%R in
    (* - b_0 x_0 <<= b_1 x_1 + ... + b_n x_n *)
  [seq (l.1, dsubmx l.2)
    | l : LRA_literal (1 + dim) <- ls & l.2 0 0 == 0]%R ++
  [seq (lp.1 && ln.1, lp.2 0 0 *: dsubmx ln.2 -
                      ln.2 0 0 *: dsubmx lp.2)%R
    | lp : LRA_literal (1 + dim) <- lsp, ln : LRA_literal (1 + dim) <- lsn]
  (*
       - (a_1 x_1 + ... + a_n x_n) <<= a_0 x_0 /\
       - b_0 x_0 <<= b_1 x_1 + ... + b_n x_n
  <=>  b_0 (a_1 x_1 + ... + a_n x_n) <<= a_0 (b_1 x_1 + ... + b_n x_n)
  <=>  0 <= (a_0 b_1 - b_0 a_1) x_1 + ... + (a_0 b_n - b_0 a_n) x_n
  *).

Definition literal_interval dim (I : 'cV_dim) (l : LRA_literal (1 + dim)) :=
  let r := (- LRA_interpret_af I (dsubmx l.2) / l.2 0 0)%R in
  if (l.2 0 0 == 0)%R
  then if LRA_interpret_literal I (l.1, dsubmx l.2) then
         `]-oo, +oo[%O else `]0%R, 0%R[%O
  else if (0 < l.2 0 0)%R then Interval (BSide l.1 r) (BInfty _ false)
                          else Interval (BInfty _ true) (BSide (~~ l.1) r).




Lemma literal_intervalE dim x0 (I : 'cV_dim) (l : LRA_literal (1 + dim)) :
  LRA_interpret_literal (col_mx (const_mx x0) I) l =
  (x0 \in literal_interval I l).
Proof.
rewrite /literal_interval /LRA_interpret_literal LRA_af_recl.
rewrite /LRA_interpret_af trmx_dsub mxE split1 unlift_none /= mxE col_mxKd.
case: (ltrgtP (l.2 0 0) 0)%R => /= H.

(* Much longer than the original which I could not get to work; probable reason
   the 'try' above was rejected and did not prepare for the sequel!  *)                 

- elim: l H =>/= [a] bV HbVNeg.
  set xmat:=  ((rsubmx  bV^T *m I) 0 0) %R .
  rewrite // in_itv Bool.andb_true_l Bool.negb_involutive.

  +  case: a => //=.
    * rewrite -lerBlDr sub0r; rewrite ler_ndivlMr; last  by apply HbVNeg.
      by rewrite {1}mulrC.
    * set nbV0:= (- (bV 0 0))%R.
      have NbV: ((bV 0 0) = -nbV0)%R by rewrite /nbV0 opprK.
      rewrite NbV. rewrite ltr_ndivlMr; first by rewrite -ltrBlDr  sub0r {1}mulrC.
      by rewrite /nbV0 opprK; exact HbVNeg.

- elim: l H =>/= [a] bV HbVPos.
  set xmat:=  ((rsubmx  bV^T *m I) 0 0) %R .
  +  case: a => //=; 
      first by rewrite -lerBlDr sub0r  in_itv Bool.andb_true_r mulrC //=; rewrite ler_pdivrMr.
      rewrite in_itv /= Bool.andb_true_r ltr_pdivrMr; last by exact HbVPos.
      by rewrite -ltrBlDr sub0r mulrC.


 -  elim: l H =>/= [a] bV bvZ.
    set xmat:= ((rsubmx bV^T *m I) 0 0)%R.
    +  case: a => //=; case Hmat: (0 <= xmat)%R =>/=.
       * by rewrite in_itv bvZ mul0r add0r /xmat =>//=.
       * by rewrite bvZ mul0r add0r Hmat in_itv  lt_asym.
       * rewrite bvZ mul0r add0r.
       have := le0r xmat; rewrite Hmat => H1; symmetry in H1.
       elim: (Bool.orb_prop _ _ H1 )=> H2'.
       replace (0 < xmat)%R with false.
          by rewrite in_itv -ltr_asym.
          by rewrite (eqP H2') ltxx.
        by rewrite H2' in_itv => //=.
    +  case H1: (0 < xmat)%R.
        * by rewrite in_itv //= bvZ mul0r add0r.
        * by rewrite in_itv //= bvZ mul0r add0r H1  -ltr_asym.
Qed.

Lemma exists_conj_elimP dim I (ls : seq (LRA_literal (1 + dim))) :
  reflect
    (exists x, all (LRA_interpret_literal (col_mx (const_mx x) I)) ls)
    (all (LRA_interpret_literal I) (exists_conj_elim ls)).
Proof.
have af_decomp (l1 l2 : LRA_literal (1 + dim)) :
  LRA_interpret_af I
    (l1.2 0 0 *: dsubmx l2.2 - l2.2 0 0 *: dsubmx l1.2)%R =
  (l1.2 0 0 * LRA_interpret_af I (dsubmx l2.2) -
   l2.2 0 0 * LRA_interpret_af I (dsubmx l1.2))%R.

  by rewrite /LRA_interpret_af  mulmx_trl mulmxBr -!scalemxAr 3!mxE;
    congr (_ + _)%R; rewrite mulmx_trl !mxE.

apply/(iffP idP); rewrite /exists_conj_elim all_cat.
- case/andP; rewrite all_map => H /all_allpairsP H0.
  suff: itv_nonempty
          (\big[Order.meet/`]-oo, +oo[%O]_(l <- ls) literal_interval I l)
    by case/itv_nonemptyP => /= x; rewrite in_itv_bigI => H1; exists x;
      apply/allP => /= l /(allP H1); rewrite literal_intervalE.
  have H1 (l : LRA_literal dim.+1) :
    (l.2 0 0 == 0)%R -> l \in ls -> literal_interval I l = `]-oo, +oo[%O
    by move=> H1 H2; rewrite /literal_interval H1;
       move: (allP H l); rewrite mem_filter H1 H2 /= => /(_ isT) ->.
  rewrite itv_bigI_pairwise0;
    apply/allP => /= itv /allpairsP [] [] /= l1 l2 [H2 H3 H4]; subst itv.
  case_eq (l1.2 0 0 == 0)%R => H4;
    first rewrite (H1 l1) // meet1x {H4};
    (case_eq (l2.2 0 0 == 0)%R => H5;
     first rewrite (H1 l2) // ?meetx1 {H5});
    rewrite /literal_interval ?H4 ?H5;
    do !case: ifP => //=; move=> H6 H7; try rewrite -negb_and negbK.
  + have {H5 H6} {}H4: (l2.2 0 0 < 0)%R by rewrite ltNge le_eqVlt eq_sym H5 H6.
    move: (H0 l1 l2).


    by rewrite negbK !mem_filter H2 H3 H4 H7 /LRA_interpret_literal /=
               lteif_pdivrMr // mulrAC lteif_ndivlMr // !mulNr
               -addr_lteif0r af_decomp !(mulrC (LRA_interpret_af _ _))%R => ->.
  + have {H5 H7} {}H4: (l1.2 0 0 < 0)%R by rewrite ltNge le_eqVlt eq_sym H4 H7.
    move: (H0 l2 l1).
    by rewrite negbK !mem_filter H2 H3 H4 H6 /LRA_interpret_literal /=
               lteif_pdivrMr // mulrAC lteif_ndivlMr // !mulNr
               -addr_lteif0r af_decomp !(mulrC (LRA_interpret_af _ _))%R => ->.
- case=> x H; apply/andP; split.
  + rewrite all_map; apply/allP => /= l; rewrite mem_filter =>
      /andP [/eqP H0 /(allP H)].
    by rewrite /LRA_interpret_literal LRA_af_recl !mxE;
      case: splitP => i // _; rewrite ord1 H0 mul0r add0r col_mxKd.
  + apply/allP => l /allpairsP [] [] /= l1 l2 /= [].
    rewrite !mem_filter => //= /andP [H0] /(allP H) H1
                               /andP [H2] /(allP H) H3 ->.
    move: H0 H2 H1 H3.
    rewrite /LRA_interpret_literal /= !LRA_af_recl !mxE;
      case: splitP => i // _; rewrite ord1 !addr_lteif0r af_decomp subr_lteif0r.
    move=> /(lteif_pM2l l2.1) <- /(lteif_nM2l l1.1) <-.
    rewrite !mulrN mulrCA col_mxKd !mxE; exact: lteif_trans.
Qed.


Definition exists_DNF_elim dim (lss : seq (seq (LRA_literal dim.+1))) :
  QFLRA_formula dim :=
  QFLRA_unDNF [seq exists_conj_elim ls | ls <- lss].

Lemma exists_DNF_elimP dim I (lss : seq (seq (LRA_literal (1 + dim)))) :
  reflect (exists x,
             has (all (LRA_interpret_literal (col_mx (const_mx x) I))) lss)
          (QFLRA_interpret_formula I (exists_DNF_elim lss)).
Proof.
rewrite /exists_DNF_elim -QFLRA_unDNF_correctness; apply/(iffP hasP).
- case=> /= ls' /mapP [] /= ls H -> {ls'} /exists_conj_elimP [] x H0.
  by exists x; apply/hasP => /=; exists ls.
- case=> x /hasP [] ls H H0; exists (exists_conj_elim ls); first exact: map_f.
  by apply/exists_conj_elimP; exists x.
Qed.



Fixpoint Fourier_Motzkin dim (f : LRA_formula dim) : QFLRA_formula dim :=
  match f with
    | LRA_forall f' =>
      QFLRA_neg (exists_DNF_elim (QFLRA_DNF (QFLRA_neg (Fourier_Motzkin f'))))
    | LRA_exists f' =>
      exists_DNF_elim (QFLRA_DNF (Fourier_Motzkin f'))
    | LRA_neg f' => QFLRA_neg (Fourier_Motzkin f')
    | LRA_and f1 f2 => QFLRA_and (Fourier_Motzkin f1) (Fourier_Motzkin f2)
    | LRA_or f1 f2 => QFLRA_or (Fourier_Motzkin f1) (Fourier_Motzkin f2)
    | LRA_imply f1 f2 =>
      QFLRA_or (QFLRA_neg (Fourier_Motzkin f1)) (Fourier_Motzkin f2)
    | LRA_leq t => QFLRA_leq (\col_i (t i 0))%R
  end.

Lemma Fourier_MotzkinP dim I (f : LRA_formula dim) :
  reflect (LRA_interpret_formula I f)
          (QFLRA_interpret_formula I (Fourier_Motzkin f)).
Proof.
elim/LRA_formula_rect: dim / f I => //= dim.
- move=> f IH I; apply/(iffP idP) => [/exists_DNF_elimP H x|H].
  + apply/IH/negP => /negP H0; apply: H; exists x.
    by rewrite NF_neg_CNF QFLRA_NF_correctness.
  + apply/negP => /exists_DNF_elimP [x].
    rewrite NF_neg_CNF QFLRA_NF_correctness => /IH; apply; exact: H.
- by move=> f IH l; apply/(iffP (exists_DNF_elimP _ _));
     move=> [x H]; exists x; move: H;
     rewrite QFLRA_NF_correctness => /IH.
- by move=> f IH I; apply/(iffP idP); move/IH.
- by move=> f1 IH1 f2 IH2 I; apply/(iffP andP); case=> /IH1 H /IH2 H0.
- by move=> f1 IH1 f2 IH2 I; apply/(iffP orP);
    (case; [move/IH1; left | move/IH2; right]).
- by move=> f1 IH1 f2 IH2 I;
    rewrite -implybE; apply/(iffP implyP) => H /IH1 /H /IH2.
- move=> t I; rewrite mxE.
  set r1 := (\sum_i _)%R; set r2 := (\sum_i _)%R.
  suff ->: r1 = r2 by exact: idP.
  by subst r1 r2; apply/eq_bigr => /= i _; rewrite !mxE.
Qed.

End LRA.
