(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import bigop div ssralg ssrint ssrnum fintype order.
From mathcomp Require Import binomial matrix interval rat.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype landau sequences.

(******************************************************************************)
(*               More standard sequences and series (WIP)                     *)
(*                                                                            *)
(* The main purpose of this file is to test extensions to sequences.v         *)
(*                                                                            *)
(* is_cvg_series_exp_pos == convergence of \sum_n^+oo x^n / n!                *)
(*                 e_seq == (1 + 1 / n) ^ n                                   *)
(*             cvg_e_seq == e_seq converges                                   *)
(*        euler_constant == Euler constant defined as lim e_seq               *)
(*          dvg_harmonic == the harmonic series does not converge             *)
(*               riemann == Riemann sequence 1/(n + 1)^a                      *)
(*           dvg_riemann == the Riemann series does not converge              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* PR? *)
Section move_to_ssrnat.

Lemma leq_fact n : (n <= n`!)%nat.
Proof.
elim: n => // n ih; rewrite factS mulSn -(add1n n) leq_add // ?fact_gt0 //.
by rewrite leq_pmulr // fact_gt0.
Qed.

Lemma prod_rev n m :
  (\prod_(0 <= k < n - m) (n - k) = \prod_(m.+1 <= k < n.+1) k)%N.
Proof.
rewrite [in RHS]big_nat_rev /= -{1}(add0n m.+1) big_addn subSS.
by apply eq_bigr => i _; rewrite addnS subSS addnC subnDr.
Qed.

Lemma fact_split n m : (m <= n)%nat ->
  (n`! = \prod_(0 <= k < n - m) (n - k) * m`!)%nat.
Proof.
move=> Ni; rewrite [in RHS]fact_prod mulnC prod_rev -big_cat [in RHS]/index_iota.
rewrite subn1 -iota_add subSS addnBCA // subnn addn0 [in LHS]fact_prod.
by rewrite [in RHS](_ : n = n.+1 - 1)%nat // subn1.
Qed.

End move_to_ssrnat.

Section exponential_series.

Variable (R : realType).

Definition exp_ (x : R) : R^o ^nat := fun n => x ^+ n / n`!%:R.

Lemma exp_ge0 x n : 0 <= x -> 0 <= exp_ x n.
Proof. by move=> x0; rewrite /exp_ divr_ge0 // ?exprn_ge0 // ler0n. Qed.

Lemma series_exp_0 n : series (exp_ 0) n.+1 = 1.
Proof.
rewrite /series/= big_nat_recl// /exp_ expr0n eqxx fact0 divr1; apply/eqP.
rewrite addrC eq_sym -subr_eq eq_sym subrr big1 // => /= i _.
by rewrite expr0n /= mul0r.
Qed.

Section exp_cvg_series_pos.
Variable x : R.

Let S0 N n : R^o := (N ^ N)%:R * \sum_(N.+1 <= i < n) (x / N%:R) ^+ i.

Let cvg_S0 N (x0 : 0%R < x) (xN : x < N%:R) : cvg (S0 N).
Proof.
apply: is_cvgZr; rewrite is_cvg_series_restrict exprn_geometric.
apply/is_cvg_geometric_series.
rewrite ger0_norm ?divr_ge0 ?ler0n //; last exact: ltW.
by rewrite ltr_pdivr_mulr ?mul1r // (lt_trans _ xN).
Qed.

Let S1 N n : R^o := \sum_(N.+1 <= i < n) exp_ x i.

Lemma incr_S1 N (x0 : 0%R < x) : nondecreasing_seq (S1 N).
Proof.
apply/nondecreasing_seqP => n; rewrite /S1.
have [nN|Nn] := leqP n N.
- rewrite (_ : index_iota _ _ = [::]) ?big_nil; last first.
    by apply/eqP; rewrite -size_eq0 size_iota subn_eq0 (leq_trans nN).
  rewrite (_ : index_iota _ _ = [::]) ?big_nil //.
  by apply/eqP; rewrite -size_eq0 size_iota subSS subn_eq0 (leq_trans nN).
- by rewrite big_nat_recr //= ler_addl divr_ge0 // ?ler0n // exprn_ge0 // ltW.
Qed.

Let ler_S1_sup N (x0 : 0%R < x) (xN : x < N%:R) n :
  S1 N n <= sup [set S0 N n | n in setT].
Proof.
rewrite (@le_trans _ _ (S0 N n)) //; last first.
  apply/sup_upper_bound; last by exists n.
  split; first by exists (S0 N n); exists n.
  rewrite (_ : (fun y : R^o => _) =
      (fun y => exists2 n0, setT n0 & `|S0 N n0| = y)); last first.
    have S'_ge0 : forall n, 0 <= S0 N n.
      move=> m; rewrite mulr_ge0 // ?ler0n //; apply sumr_ge0 => i _.
      by rewrite exprn_ge0 // divr_ge0 // ?ler0n // ltW.
    by rewrite predeqE => y; split => -[z _ <-]; exists z => //; rewrite ger0_norm.
  exact: (cvg_has_ub (cvg_S0 x0 xN)).
rewrite /S0 big_distrr /=; apply ler_sum => i _.
have [Ni|iN] := ltnP N i; last first.
  rewrite expr_div_n mulrCA ler_pmul2l ?exprn_gt0 //.
  rewrite (@le_trans _ _ 1) //; last first.
    rewrite natrX -exprB // ?unitfE; last first.
      by rewrite gt_eqF // (lt_trans _ xN).
    move: iN; rewrite leq_eqVlt => /orP[/eqP ->|iN].
      by rewrite subnn expr0.
    by rewrite exprn_ege1 // ler1n (leq_trans _ iN).
  rewrite invr_le1 // ?ler1n ?ltr0n ?fact_gt0 //.
  by rewrite unitfE pnatr_eq0 gt_eqF // ltEnat /= fact_gt0.
rewrite /exp_ expr_div_n (fact_split Ni) mulrCA.
rewrite ler_pmul2l ?exprn_gt0 // natrX -invf_div -exprB; last 2 first.
  by rewrite ltnW.
  by rewrite unitfE gt_eqF // (lt_trans _ xN).
have ? : (0 < \prod_(0 <= k < i - N.+1) (i - k))%N.
  rewrite big_seq_cond; apply prodn_cond_gt0 => /= j.
  rewrite andbT /index_iota mem_iota add0n leq0n /= subn0 => jiN.
  by rewrite subn_gt0 (leq_trans jiN) //= leq_subr.
rewrite ler_pinv; last 2 first.
  rewrite inE unitfE natrM mulf_neq0 /= ?pnatr_eq0 -?lt0n ?fact_gt0 //.
  by rewrite -natrM ltr0n muln_gt0 fact_gt0 andbT.
  rewrite inE unitfE exprn_gt0 // ?andbT ?((lt_trans _ xN)) //.
  by rewrite gt_eqF // exprn_gt0 // (lt_trans _ xN).
rewrite (@le_trans _ _
    (\prod_(0 <= k < i - N.+1) (i - k) * N.+1 * N)%:R) //; last first.
  rewrite ler_nat -mulnA leq_mul2l; apply/orP; right.
  by rewrite factS leq_mul2l leq_fact orbT.
rewrite -mulnA prod_rev mulnA mulnC (mulnC _ N.+1) !mulnA.
rewrite -(@prednK (i - N)%nat) ?subn_gt0 // exprS !natrM -mulrA.
rewrite ler_pmul2l ?(lt_trans _ xN) //.
have [iN1|] := ltP O (i - N).-1; last first.
  rewrite leEnat leqn0 => /eqP ->; rewrite expr0 -natrM ler1n muln_gt0.
  rewrite andTb big_seq_cond; apply prodn_cond_gt0 => /= j.
  by rewrite /index_iota mem_iota andbT; case: j.
rewrite -(@prednK (i - N).-1%nat) // exprS.
rewrite ler_pmul //?ler_nat ?exprn_ge0 ?ler0n //.
rewrite -natrX ler_nat -subn2 -subnDA addn2 -prod_nat_const_nat.
rewrite big_nat_recr /=; last first.
  by move: iN1; rewrite -subn1 ltEnat /= subn_gt0 -addn1 ltn_subRL addn1.
rewrite -[X in (X <= _)%nat]muln1 leq_mul // ?(leq_trans _ Ni) //.
rewrite -(@ler_nat R) !natr_prod big_seq_cond [in X in _ <= X]big_seq_cond.
apply ler_prod => j.
rewrite /index_iota mem_iota andbT subnKC; last first.
  by move: iN1; rewrite -subn1 ltEnat /= subn_gt0 -addn1 ltn_subRL addn1.
case/andP => Nj ji.
by rewrite ler0n /= ler_nat (leq_trans _ Nj) // (@leq_trans N.+1).
Qed.

Lemma is_cvg_series_exp_pos : 0 < x -> cvg (series (exp_ x)).
Proof.
move=> x0; rewrite /series; near \oo => N.
have xN : x < N%:R.
  near: N.
  exists (absz (floor x)).+1 => // m; rewrite /mkset -(@ler_nat R) => xm.
  rewrite {xm}(lt_le_trans _ xm) // (lt_le_trans (lt_succ_Rfloor x)) //.
  rewrite -addn1 natrD (_ : 1%:R = 1%R) // ler_add2r RfloorE.
  by rewrite -(@gez0_abs (floor x)) // floor_ge0 // ltW.
rewrite -(@is_cvg_series_restrict N.+1).
apply: (nondecreasing_is_cvg (incr_S1 N x0) (ler_S1_sup x0 xN)).
Grab Existential Variables. all: end_near. Qed.

End exp_cvg_series_pos.

Lemma normed_series_exp x : [normed series (exp_ x)] = series (exp_ `|x|).
Proof.
rewrite funeqE => n /=; apply: eq_bigr => k _.
by rewrite /exp_ normrM normfV normrX [`|_%:R|]@ger0_norm.
Qed.

Lemma exp_cvg_series x : cvg (series (exp_ x)).
Proof.
have [/eqP ->|x0] := boolP (x == 0).
  apply/cvg_ex; exists 1; apply/cvg_distP => // => _/posnumP[e].
  rewrite near_map; near=> n.
  have [m ->] : exists m, n = m.+1 by exists n.-1; rewrite prednK //; near: n; exists 1%nat.
  by rewrite series_exp_0 subrr normr0.
apply: normed_cvg; rewrite normed_series_exp.
by apply: is_cvg_series_exp_pos; rewrite normr_gt0.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_exp_ (x : R) : exp_ x --> (0 : R^o).
Proof. exact: (cvg_series_cvg_0 (@exp_cvg_series x)). Qed.

End exponential_series.

Section euler_constant.

Variable (R : realType).

Definition e_seq : (R^o) ^nat := fun n => (1 + 1 / n%:R) ^+ n.

Lemma e_seq0 : e_seq O = 1.
Proof. by rewrite /e_seq expr0 {1}(_ : 1 = 1%:R) // ler_nat. Qed.

Lemma e_seq1 : e_seq 1%nat = 2.
Proof. by rewrite /e_seq expr1 divr1. Qed.

Lemma e_seq2 : e_seq 2%nat = 9%:R / 4%:R.
Proof.
rewrite /e_seq -{1}(@divrr _ 2) ?unitfE // -mulrDl.
by rewrite expr_div_n {2}(_ : 1 = 1%:R) // -natrD -2!natrX.
Qed.

Section e_seq_is_bounded_by_4.
Let v_ (n m : nat) : R^o := (n - m + 2)%:R / (n - m)%:R.

Let v_increasing (n : nat) : forall m, (m < n)%nat -> v_ n.*2 m < v_ n.*2 m.+1.
Proof.
move=> m mn.
rewrite /v_.
have H : forall p q,
  (1 < q < p)%nat -> (p%:R : R) / q%:R < (p%:R - 1) / (q%:R - 1).
  move=> p q pq; rewrite ltr_pdivr_mulr; last first.
    move/andP : pq => -[a b].
    by rewrite (_ : 0 = 0%:R) // ltr_nat (ltn_trans _ a).
  rewrite mulrAC ltr_pdivl_mulr; last first.
    by rewrite subr_gt0 (_ : 1 = 1%:R) // ltr_nat; case/andP: pq.
  by rewrite mulrBl mulrBr mul1r mulr1 ler_lt_sub // ltr_nat; case/andP : pq.
rewrite -(addn1 m) !subnDA (@natrB _ _ 1); last first.
  by rewrite subn_gt0 (leq_trans mn) // -addnn leq_addr.
rewrite (_ : (n.*2 - m - 1 + 2)%:R = (n.*2 - m + 2 - 1)%:R); last first.
  rewrite !subn1 !addn2 /= prednK // subn_gt0 (leq_trans mn) //.
  by rewrite -addnn leq_addr.
rewrite (@natrB _ _ 1) ?subn_gt0 ?addn2 //.
apply H; apply/andP; split; last by rewrite ltnS.
move: (mn); rewrite -(ltn_add2r 1) !addn1 => mn'.
rewrite ltn_subRL addn1 (leq_trans mn'){mn'} // -addnn -{1}(addn0 n) ltn_add2l.
by rewrite (leq_trans _ mn).
Qed.

Let v_nondecreasing (n : nat) : forall i, (i < n)%nat -> v_ n.*2 0 <= v_ n.*2 i.
Proof.
elim=> // -[/= _ n1|i ih ni].
  by apply/ltW/v_increasing; rewrite (ltn_trans _ n1).
rewrite (le_trans (ih _)) // ?(leq_trans _ ni) //.
by apply/ltW/v_increasing; rewrite (leq_trans _ ni).
Qed.

Let v_prod (n : nat) : (0 < n)%nat ->
  \prod_(i < n) v_ n.*2 i = (n.*2.+2 * n.*2.+1)%:R / (n.+2 * n.+1)%:R.
Proof.
move=> n0; set lhs := LHS. set rhs := RHS.
rewrite -(@divr1_eq _ lhs rhs) // {}/lhs {}/rhs invf_div mulrA.
rewrite /v_ big_split /= -mulrA mulrACA.
rewrite [X in X * _ = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R); last first.
  rewrite 2!big_ord_recr /= -mulrA; congr (_ * _).
  by rewrite -addnn addnK subnS addnK 2!addn2 /= natrM prednK.
rewrite [X in _ * X = 1](_ : _ = \prod_(i < n.+2) (n.*2 - i + 2)%:R^-1); last first.
  rewrite 2!big_ord_recl /= mulrA [in LHS]mulrC; congr (_ * _).
    rewrite subn0 addn2 subn1 addn2 prednK ?double_gt0 //.
    by rewrite natrM invrM ?unitfE // mulrC.
    apply eq_bigr => i _; congr (_ %:R^-1).
    rewrite /bump !leq0n !add1n -addn2 subnDA subn2 addn2 /= prednK; last first.
      rewrite -subnS subn_gt0 -addnn -(addn1 i) (@leq_trans n.+1) //.
      by rewrite addn1 ltnS.
      by rewrite -{1}(addn0 n) ltn_add2l.
    by rewrite prednK // subn_gt0 -addnn (@leq_trans n) // leq_addr.
by rewrite -big_split /= big1 // => i _; rewrite divrr // ?unitfE addn2.
Qed.

Lemma e_seq_bound : forall n, (0 < n)%nat -> e_seq n < 4%:R.
Proof.
move=> n n0.
rewrite /e_seq -{1}(@divrr _ n%:R) ?unitfE ?pnatr_eq0 -?lt0n // -mulrDl.
rewrite (_ : _ ^+ n = \prod_(i < n) ((n%:R + 1) / n%:R)); last first.
  move _ : (_ / _) => h.
  elim: n n0 => // -[_ _|n ih _].
    by rewrite big_ord_recl big_ord0 mulr1 expr1.
  by rewrite exprS ih // [in RHS]big_ord_recl.
rewrite (@le_lt_trans _ _ (\prod_(i < n) v_ n.*2 i)) //; last first.
  rewrite v_prod // (_ : _ / _%:R = 2%:R * (n.*2.+1)%:R / n.+2%:R); last first.
    rewrite -doubleS natrM -muln2 (natrM _ _ 2) natrM.
    rewrite invrM ?unitfE ?pnatr_eq0 //.
    rewrite mulrCA 3!mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r; congr (_ * _).
  rewrite ltr_pdivr_mulr // (_ : 4 = 2 * 2)%nat // (natrM _ 2) -mulrA.
  rewrite  ltr_pmul2l // -natrM mul2n ltr_nat doubleS 2!ltnS -2!muln2.
  by rewrite leq_mul2r /=.
apply ler_prod => i _; apply/andP; split.
  apply divr_ge0; last exact/ler0n.
  by rewrite [X in _ <= _ + X](_ : _ = 1%:R) // -natrD ler0n.
apply: (@le_trans _ _ (v_ n.*2 (@ord0 n))).
  rewrite /v_ subn0 addn2 -doubleS.
  rewrite -2!muln2 2!natrM invrM // ?unitfE //; last first.
    by rewrite pnatr_eq0 -lt0n.
  rewrite -mulrA (mulrA 2) divrr ?unitfE // div1r.
  by rewrite [X in (_ + X) / _ <= _](_ : _ = 1%:R) // -natrD addn1.
destruct i as [i i0] => /=; exact/v_nondecreasing.
Qed.

End e_seq_is_bounded_by_4.

Section e_seq_increasing.

Let sum_group_by_2 n (f : nat -> R) :
  \sum_(i < n) f i = \sum_(i < n./2) (f i.*2 + f i.*2.+1) + if
  odd n.+1 then 0 else f n.-1.
Proof.
elim: n.+1 {-2}n (ltnSn n) => {n} // m ih [_|n].
  by rewrite 2!big_ord0 /= addr0.
rewrite ltnS => nm.
rewrite big_ord_recr /= ih // negbK; case: ifPn => /= [|].
  by move/negbTE => no; rewrite no addr0 uphalf_half no add0n.
rewrite negbK => no.
rewrite no uphalf_half no add1n addr0 big_ord_recr /= -!addrA; congr (_ + _).
move: (odd_double_half n); rewrite no add1n => nE.
by rewrite nE -{1}nE.
Qed.

Lemma increasing_e_seq : increasing_seq e_seq.
Proof.
apply/increasing_seqP.
case=> [|n]; first by rewrite e_seq0 e_seq1 {1}(_ : 1 = 1%:R) // ltr_nat /e_seq.
rewrite -(@ltr_pmul2l _ (((n.+2%:R - 1) / n.+2%:R) ^+ n.+2)); last first.
  apply/exprn_gt0/divr_gt0; last by rewrite ltr0n.
  by rewrite subr_gt0 {1}(_ : 1 = 1%:R) // ltr_nat.
rewrite [X in X < _](_ : _ = (n.+2%:R - 1) / n.+2%:R); last first.
  rewrite {1}/e_seq exprS -[RHS]mulr1 -3!mulrA; congr (_ * _).
  rewrite -mulrA; congr (_ * _).
  rewrite (_ : _ / n.+2%:R = (1 + 1 / n.+1%:R) ^-1); last first.
    rewrite -{4}(@divrr _ n.+1%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
    by rewrite invf_div {2 6}(_ : 1 = 1%:R) // -natrD -natrB // subn1 addn1.
  by rewrite exprVn mulVr // unitfE expf_eq0 /= paddr_eq0 //= oner_eq0.
rewrite [X in _ < X](_ : _ = ((n.+2%:R ^+ 2 - 1) / n.+2%:R ^+ 2) ^+ n.+2); last first.
  rewrite /e_seq.
  rewrite -{4}(@divrr _ n.+2%:R) ?unitfE ?pnatr_eq0 // -mulrDl.
  rewrite -exprMn_comm; last by rewrite /GRing.comm mulrC.
  congr (_ ^+ _); rewrite mulrACA -subr_sqr expr1n; congr (_ * _).
  by rewrite -invrM // unitfE pnatr_eq0.
rewrite mulrBl divrr ?unitfE ?pnatr_eq0 // mulrBl.
rewrite divrr ?unitfE ?expf_eq0 /= ?pnatr_eq0 //.
rewrite exprBn_comm; last by rewrite /GRing.comm mulrC.
rewrite big_ord_recl 2!expr0 expr1n bin0 mulr1n 2![in X in _ < X]mul1r.
rewrite big_ord_recl 2!expr1 expr1n bin1 [in X in _ < X]mul1r mulN1r.
rewrite (_ : -1 / _ *+ _ = -1 / n.+2%:R); last first.
  rewrite 2!mulN1r mulNrn; congr (- _).
  rewrite expr2 invrM ?unitfE ?pnatr_eq0 //.
  rewrite -mulrnAr -[RHS]mulr1; congr (_ * _).
  by rewrite -mulr_natl divrr // unitfE pnatr_eq0.
rewrite addrA mulN1r div1r -ltr_subl_addl subrr.
pose F : 'I_n.+1 -> R :=
  fun i => (-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2).
rewrite (eq_bigr F); last first.
  by move=> i _; congr (_ *+ _); rewrite /= expr1n mulr1.
rewrite (sum_group_by_2 n.+1
  (fun i => ((-1) ^+ i.+2 * n.+2%:R ^- 2 ^+ i.+2 *+ 'C(n.+2, i.+2)))).
destruct n as [|n'].
  by rewrite /= big_ord0 add0r -signr_odd /= expr0 mul1r.
set n := n'.+1.
set G := BIG_F.
have G_gt0 : forall i, 0 < G i.
  move=> /= i; rewrite /G.
  rewrite -signr_odd /= negbK odd_double expr0 mul1r.
  rewrite -signr_odd /= negbK odd_double /= expr1 mulN1r.
  rewrite mulNrn (@exprSr _ _ i.*2.+2) -mulrnAr -mulr_natr -mulrBr.
  rewrite mulr_gt0 // ?exprn_gt0 //.
  rewrite subr_gt0 -mulr_natr ltr_pdivr_mull // -natrX -natrM.
  move: (@mul_bin_left n.+2 i.*2.+2).
  move/(congr1 (fun x => x%:R : R)).
  move/(congr1 (fun x => (i.*2.+3)%:R^-1 * x)).
  rewrite natrM mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r => ->.
  rewrite 2!natrM mulrA.
  have ? : (i.*2.+1 < n.+2)%nat.
    move: (ltn_ord i).
    rewrite 3!ltnS -(@leq_pmul2r 2) // !muln2 => /leq_trans; apply.
    case/boolP : (odd n') => on'.
      move: (odd_geq n' on'); rewrite leqnn => /esym.
      by move/leq_trans; apply; rewrite leqnSn.
    by move: (@odd_geq n' n on') => <-; rewrite leqnSn.
  rewrite ltr_pmul2r ?ltr0n ?bin_gt0 // ltr_pdivr_mull // -natrM ltr_nat.
  rewrite -(@ltn_add2r i.*2.+2) subnK // ltn_addr // -{1}(mul1n n.+2) -mulnn.
  by rewrite  mulnA ltn_mul2r /= mulSn addSn ltnS addSn.
have sum_G_gt0 : 0 < \big[+%R/0]_i G i.
  rewrite {1}(_ : 0 = \big[+%R/0]_(i < n.+1./2) 0); last by rewrite big1.
  apply: (@lt_leif _ _ _ _ false).
  rewrite (_ : false = [forall i : 'I_n.+1./2, false]); last first.
    apply/idP/forallP => //=; apply; exact: (@Ordinal _ 0).
  apply: leif_sum => i _; exact/leifP/G_gt0.
case: ifPn => no; first by rewrite addr0.
rewrite addr_gt0 //= -signr_odd (negbTE no) expr0 mul1r.
by rewrite pmulrn_lgt0 ?bin_gt0 // exprn_gt0.
Qed.

End e_seq_increasing.

Lemma cvg_e_seq : cvg e_seq.
Proof.
apply: (@near_nondecreasing_is_cvg _ _ 4%:R).
  by apply: nearW => x y ?; rewrite increasing_e_seq.
by near=> n; rewrite ltW// e_seq_bound//; near: n.
Grab Existential Variables. all: end_near. Qed.

Lemma lim_e_seq_lb : 2 < lim e_seq.
Proof.
apply: (@lt_le_trans _ _ (e_seq 2%nat)).
  by rewrite e_seq2 ltr_pdivl_mulr // -natrM ltr_nat.
rewrite lim_ge//; first exact: cvg_e_seq.
by near=> n; rewrite increasing_e_seq; near: n.
Grab Existential Variables. all: end_near. Qed.

Definition euler_constant : R := lim e_seq.

Lemma euler_constant_gt0 : 0 < euler_constant.
Proof. by rewrite (lt_trans _ lim_e_seq_lb). Qed.

Lemma euler_constant_neq1 : euler_constant != 1.
Proof. by rewrite eq_sym lt_eqF // (lt_trans _ lim_e_seq_lb) // ltr1n. Qed.

End euler_constant.

(* Density of R (i.e., for any x in R and 0 < a, there is an nonincreasing *)
(* sequence of Q.a that converges to x)                                 *)
Section R_dense.

(*Lemma ratr_fracq (G : realType) (p : int) (q : nat) :
  (p + 1)%:~R / q.+1%:~R = @ratr [unitRingType of G] ((p + 1)%:Q / q.+1%:Q).
Proof. by rewrite rmorph_div /= ?ratr_int // unitfE. Qed.*)

(* sequence in Q.a that converges to x \in R *)
Section rat_approx_R.
Variables (G : archiFieldType) (a x : G) (m : int).

Fixpoint seq_Q (n : nat) : rat :=
  if n is n'.+1 then
    if x - ratr (seq_Q n') * a < ratr (1%:Q / (2^n'.+1)%:Q) * a then
      seq_Q n'
    else if x - ratr (seq_Q n') * a > ratr (1%:Q / (2^n'.+1)%:Q) * a then
           seq_Q n' + 1%:Q / (2^n'.+1)%:Q
         else
           0 (* should not happen *)
  else m%:~R.

Hypothesis a0 : 0 < a.

Lemma nondecreasing_seq_Q : (forall q : rat, x != ratr q * a) -> nondecreasing_seq seq_Q.
Proof.
move=> /(_ _)/negPf xa_alg; apply/nondecreasing_seqP => n /=.
have [//||/eqP] := ltgtP; last by rewrite subr_eq -mulrDl -rmorphD/= xa_alg.
by rewrite ler_addl mulr_ge0 // ltW // invr_gt0 // ltr0z exprn_gt0.
Qed.

Hypothesis xma : x < (m + 1)%:~R * a.

Lemma seq_QP : (forall q : rat, x != ratr q * a) ->
   forall n, x - ratr (seq_Q n) * a < ratr (1%:Q / (2^n)%:Q) * a.
Proof.
move=> xqa; elim => [|n ih] /=.
  by rewrite expr0z divr1 ltr_subl_addr -mulrDl 2!ratr_int -intrD addrC.
case: ifPn => [//|].
rewrite -leNgt le_eqVlt => /orP[abs|H1].
  exfalso; move: abs; apply/negP.
  rewrite eq_sym subr_eq -mulrDl -rmorphD /=; exact: xqa.
rewrite H1 rmorphD /= mulrDl opprD addrA ltr_sub_addr -mulrDl -rmorphD.
rewrite -mulrDl /= -intrD exprSz intrM invrM; last 2 first.
  by rewrite unitfE intr_eq0.
  by rewrite unitfE intr_eq0 expf_neq0.
rewrite mulrCA divrr ?unitfE ?intr_eq0 // mulr1.
by rewrite div1r in ih.
Qed.

Hypothesis max : m%:~R * a <= x.

Lemma seq_Q_ub : (forall q : rat, x != ratr q * a) ->
   forall n, ratr (seq_Q n) * a <= x.
Proof.
move=> xa; elim => [|n unx].
  by rewrite /= ratr_int.
move: (seq_QP xa) => H /=.
case: ifPn => //.
rewrite -leNgt le_eqVlt => /orP[abs|K].
- exfalso.
  move: abs; apply/negP.
  by rewrite eq_sym subr_eq -mulrDl -rmorphD /= xa.
- by rewrite K rmorphD /= mulrDl -lter_sub_addl ltW.
Qed.

End rat_approx_R.

Section rat_approx_R_contd.
Variables (R : realType) (a x : R) (m : int).

Hypothesis a0 : 0 < a.
Hypothesis xma : x < (m + 1)%:~R * a.
Hypothesis max : m%:~R * a <= x.

Lemma is_cvg_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  cvg (fun n : nat => ratr (seq_Q a x m n) : R^o).
Proof.
apply: (@nondecreasing_is_cvg _ _ (x / a)).
by apply/nondecreasing_seqP => n; rewrite ler_rat; apply: nondecreasing_seq_Q.
by move=> n; rewrite ler_pdivl_mulr //; apply seq_Q_ub => //; exact/ltrW.
Qed.

Lemma cvg_seq_Q (xa : (forall q : rat, x != ratr q * a)) :
  (fun n : nat => ratr (seq_Q a x m n) * a : R^o) --> (x:R^o).
Proof.
apply/cvg_distP => _/posnumP[e].
rewrite near_map; near=> n.
move: (seq_Q_ub xma max xa n) => H1.
rewrite [X in X < _](_ : _ = `|x - ratr (seq_Q a x m n) * a|%R) //.
rewrite ger0_norm // ?subr_ge0 //.
move: (seq_QP xma xa) => H.
rewrite (lt_le_trans (H _)) // -ler_pdivl_mulr // ltW //.
rewrite [X in X < _](_ : _ = `| (0 - ratr (1%:Q / (2 ^ n)%:Q)) : R^o |); last first.
  rewrite distrC subr0 [RHS](_ : _ = `|ratr (1%:~R / (2 ^ n)%:~R)|%R) //.
  by rewrite ger0_norm // ler0q divr_ge0 // ler0z // -exprnP exprn_ge0.
near: n.
have K : (fun n : nat => ratr (1%:~R / (2 ^ n)%:~R) : R^o) --> (0 : R^o).
  rewrite (_ : (fun _ => _) = geometric 1 (2 ^ -1)); last first.
    rewrite funeqE => n; rewrite /geometric /ratr.
    rewrite coprimeq_num ?absz1 ?coprime1n // gtr0_sg ?exprn_gt0 // mul1r.
    rewrite coprimeq_den ?absz1 ?coprime1n // expfz_eq0 andbF div1r.
    by rewrite ger0_norm // ?exprn_ge0 // -exprz_pintl //= mul1r exprVn.
  by apply: cvg_geometric; rewrite gtr0_norm // exprN1 invr_lt1 ?ltr1n // unitfE.
have ea0 : 0 < e%:num / a by rewrite divr_gt0.
by move/cvg_distP : K => /(_ _ ea0) /=; rewrite near_map.
Grab Existential Variables. all: end_near. Qed.

Lemma start_x : (forall q : rat, x != ratr q * a) ->
  {m : int | m%:~R * a < x < (m + 1)%:~R * a}.
Proof.
move=> xa; exists (floor (x / a)); apply/andP; split; last first.
  by rewrite -ltr_pdivr_mulr // intrD -RfloorE lt_succ_Rfloor.
rewrite -ltr_pdivl_mulr // lt_neqAle -{2}RfloorE ge_Rfloor andbT.
apply/negP => /eqP H.
move: (xa (floor (x / a))%:~R) => /negP; apply; apply/eqP.
by rewrite ratr_int H -mulrA mulVr ?mulr1 // unitfE gt_eqF.
Qed.

End rat_approx_R_contd.

Lemma R_dense_corollary (R : realType) (a x : R) (a0 : 0 < a) :
  {x_ : rat ^nat | nondecreasing_seq x_ /\
    cvg (fun n => ratr (x_ n) : R^o) /\ lim (fun n => ratr (x_ n) * a : R^o) = x}.
Proof.
have [xa|xa] := pselect (forall q : rat, x != ratr q * a); last first.
  have [q xqa] : {q : rat | x = ratr q * a}.
    apply/cid/asboolP/negPn/negP => abs; apply xa => {xa} q.
    apply: contra abs => /eqP ->.
    by apply/asboolP; exists q.
  exists (fun=> q); split => //.
  split; first exact: is_cvg_cst.
  by rewrite xqa; exact: lim_cst.
have [m /andP[max xma]] := start_x a0 xa.
set x0 := m%:~R * a; set x_ := seq_Q a x m; exists (seq_Q a x m).
split; first exact: nondecreasing_seq_Q.
split; first by apply: is_cvg_seq_Q => //; rewrite addrC in xma => //; exact/ltW.
by apply/cvg_lim => //; apply/cvg_seq_Q => //; exact/ltW.
Qed.

End R_dense.

Lemma dvg_harmonic (R : realType) : ~ cvg (@series [zmodType of R^o] (@harmonic R)).
Proof.
have ge_half n : (0 < n)%N -> 2^-1 <= \sum_(n <= i < n.*2) harmonic i :> R.
  case: n => // n _; rewrite (@le_trans _ _
      (\sum_(n.+1 <= i < n.+1.*2) n.+1.*2%:R^-1)) //=; last first.
    by apply: ler_sum_nat => i /andP[? ?]; rewrite lef_pinv ?qualifE ?ler_nat.
  rewrite sumr_const_nat -addnn addnK addnn -mul2n natrM invfM.
  by rewrite -[_ *+ n.+1]mulr_natr divfK.
move/cvg_cauchy/cauchy_ballP => /(_ _ 2^-1%:pos); rewrite !near_map2 -ball_normE/=.
move=> /nearP_dep hcvg; near \oo => n; near \oo => m.
have: `|series harmonic n - series harmonic m| < 2^-1 :> R by near: m; near: n.
rewrite le_gtF// distrC -[series harmonic m](addrNK (series harmonic n.*2)).
rewrite sub_series_geq; last by near: m; apply: nbhs_infty_ge.
rewrite -addrA sub_series_geq -addnn ?leq_addr// addnn.
have hchunk_gt0 i j : 0 <= \sum_(i <= k < j) harmonic k :> R.
  by rewrite ?sumr_ge0//; move=> k _; apply: harmonic_ge0.
by rewrite ger0_norm ?addr_ge0// ler_paddl// ge_half//; near: n.
Grab Existential Variables. all: end_near. Qed.

Section riemann_sequence.
Variable R : realType.
Variable pow_fun : forall a : R, R -> R.
Local Notation "a `^ x" := (pow_fun a x).
Hypothesis pow_fun_gt0 : forall a : R, 0 < a -> (forall x, 0 < a `^ x).
Hypothesis pow_funa1 : forall a : R, 0 < a -> a `^ 1 = a.
Hypothesis pow_fun1 : pow_fun 1 = fun=> 1.
Hypothesis pow_fun_homo_leq :
  forall a : R, 1 < a -> {homo pow_fun a : x y / x <= y}.
Hypothesis pow_fun_morph :
  forall a : R, 0 < a -> {morph pow_fun a : x y / x + y >-> x * y}.
Hypothesis pow_funa0 : forall a : R, 0 < a -> a `^ 0 = 1.
(*
Hypothesis pow_fun_homo_geq :
  forall a : R, 0 < a -> a < 1 -> {homo pow_fun a : x y / x >= y}. *)

Lemma pow_fun_inv (a : R) : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -{1}(pow_funa1 a0) -pow_fun_morph // subrr pow_funa0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma pow_fun_mulrn (a : R) (n : nat) : 0 < a -> pow_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 pow_funa0.
by rewrite -addn1 natrD pow_fun_morph // exprD ih pow_funa1.
Qed.

(*Definition exp_fun : R -> R := pow_fun exp_base.*)

Definition riemann (a : R) : R^o ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemann a n /.

Lemma riemann_gt0 a i : 0 < a -> 0 < riemann a i.
Proof. move=> ?; by rewrite /riemann invr_gt0 pow_fun_gt0. Qed.

Lemma cvg_riemann (a : R): 0 < a <= 1 -> ~ cvg (series (riemann a)).
Proof.
case/andP => a0; rewrite le_eqVlt => /orP[/eqP ->|a1].
  rewrite (_ : riemann 1 = harmonic); first exact: dvg_harmonic.
  by rewrite funeqE => i /=; rewrite pow_funa1.
have : forall n, harmonic n <= riemann a n.
  case=> /= [|n]; first by rewrite pow_fun1 invr1.
  rewrite -[X in _ <= X]div1r ler_pdivl_mulr ?pow_fun_gt0 // mulrC.
  rewrite ler_pdivr_mulr // mul1r -[X in _ <= X]pow_funa1 //.
  by rewrite (pow_fun_homo_leq) // ?ltr1n // ltW.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemann_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemann_sequence.
