Require Import ZArith Zwf.
Require Import ZArith.Znumtheory.
Require Import Psatz.
Set Implicit Arguments.
Open Scope Z.

Lemma rel_prime_factor_exclusive : forall a b c, a <> 0 -> b <> 0 -> rel_prime a b -> 1 < c -> (c | a) -> ~(c | b).
Proof.
  intros a b c Ha Hb Hrp Hc Hdiv.
  destruct Hdiv as [a' ->].
  intros [b' ->].
  rewrite <- Zgcd_1_rel_prime in Hrp.
  rewrite Z.gcd_mul_mono_r_nonneg in Hrp; auto with *.
  rewrite Z.mul_comm in Hrp.
  destruct (Z.mul_eq_1 _ _ Hrp); subst; auto with *.
Qed.

Lemma root_divide : forall n k, 1 <= k -> (n | n ^ k).
Proof.
  intros.
  replace k with (1 + (k - 1)); auto with *.
  rewrite Z.pow_add_r; auto with *.
  cbn.
  auto with *.
Qed.
Hint Resolve root_divide.

Lemma factor_prod : forall a b c d, (a | b) -> (c | d) -> (a * c | b * d).
Proof.
  intros a b c d [b' -> ] [d' ->].
  exists (b' * d').
  lia.
Qed.

Lemma not_prime_divide_prime :
  forall n, 1 < n -> ~prime n -> exists p, 1 < p < n /\ (p | n) /\ prime p.
Proof.
  intro n.
  induction n using (well_founded_ind (Zwf_well_founded 0)).
  intros Hlt (m & Hrange & Hdiv)%not_prime_divide; auto.
  destruct (prime_dec m) as [Hp | Hnp]; eauto.
  destruct (H m) as (p & Hp); auto with *.
  - unfold Zwf.
    auto with *.
  - exists p.
    intuition.
    eauto using Z.divide_trans.
Qed.

Inductive Factors : Z -> Prop :=
| factors_1 : Factors 1
| factors_prod : forall p m, prime p -> Factors m -> Factors (m * p).
Hint Constructors Factors.

Lemma pos_factors : forall n, 1 <= n -> Factors n.
Proof.
  induction n using (well_founded_ind (Zwf_well_founded 0)).
  intro Hn.
  destruct (Zle_lt_or_eq _ _ Hn) as [Hgt | <-]; auto.
  destruct (prime_dec n) as [Hp | Hnp].
  - rewrite <- Z.mul_1_l.
    auto.
  - apply not_prime_divide_prime in Hnp; auto.
    destruct Hnp as (p & Hrange & [n' ->] & Hp).
    apply factors_prod; auto.
    assert (1 <= n') as Hn'; try nia.
    apply H; auto.
    unfold Zwf.
    nia.
Qed.

Lemma factors_pos : forall n, Factors n -> 1 <= n.
Proof.
  intros.
  induction H; auto with *.
  destruct H.
  apply Z.le_trans with m; auto.
  rewrite <- Z.le_mul_diag_r; auto with *.
Qed.
Hint Resolve factors_pos.


Lemma divide_sq_prime : forall p b, prime p -> 1 <= b -> (p ^ 2 | b ^ 2) -> (p | b).
Proof.
  intros p b Hp Hb Hdiv.
  assert (p | b ^ 2) as Hdiv'. {
    apply Z.divide_trans with (p ^ 2); auto with *.
  }
  clear Hdiv.
  rewrite Z.pow_2_r in Hdiv'.
  apply prime_mult in Hdiv'; tauto.
Qed.


Lemma divide_sq_inv : forall a b, 1 <= a -> 1 <= b -> (a ^ 2 | b ^ 2) -> (a | b).
Proof.
  intros a b Ha Hb.
  revert b Hb.
  induction (pos_factors Ha); auto with *.
  intros b Hb Hdiv.
  destruct (@divide_sq_prime p b) as [k ->]; auto with *.
  - apply Z.divide_trans with ((m * p) ^ 2); auto.
    rewrite Z.pow_mul_l.
    auto with *.
  - apply Z.mul_divide_mono_r.
    apply IHf; auto with *.
    + destruct H.
      nia.
    + repeat rewrite Z.pow_mul_l in Hdiv.
      eapply Z.mul_divide_cancel_r; eauto with *.
      intros He%Z.pow_eq_0; subst; auto with *.
Qed.

Definition Square n := exists m, n = m ^ 2.
Lemma Square_pow_2 : forall n, Square (n ^ 2).
Proof.
  intros.
  exists n.
  reflexivity.
Qed.
Hint Resolve Square_pow_2.

Lemma Square_square : forall n, Square (n * n).
Proof.
  intros.
  exists n.
  lia.
Qed.
Hint Resolve Square_square.

Lemma Square_nonneg_root : forall n, Square n -> exists m, 0 <= m /\ n = m ^ 2.
Proof.
  intros n [m ->].
  destruct (Z.lt_ge_cases m 0); eauto.
  exists (- m).
  split; auto with *.
  lia.
Qed.

Lemma Square_product : forall n m, Square n -> Square m -> Square (n * m).
Proof.
  intros n m [n' ->] [m' ->].
  exists (n' * m').
  lia.
Qed.

Lemma Square_product_inv_r : forall n m, 0 <> n -> Square (n * m) -> Square n -> Square m.
Proof.
  intros n m Hnzn (k & Hnnegk & Hk)%Square_nonneg_root (n' & Hnnegn' & ->)%Square_nonneg_root.
  destruct (Z.eq_dec m 0) as [| Hnzm];subst;[exists 0; lia|].
  assert ((n' | k)) as [k' ->]. {
    apply divide_sq_inv; try nia.
    rewrite <- Hk.
    auto with *.
  }
  exists k'.
  rewrite <- Z.mul_cancel_r with (p := n' ^ 2); auto.
  lia.
Qed.

Lemma Square_product_inv_l : forall n m, 0 <> m -> Square (n * m) -> Square m -> Square n.
Proof.
  intros.
  rewrite Z.mul_comm in *.
  eapply Square_product_inv_r; eauto.
Qed.

Lemma prime_mult_sq_aux : forall p n m, prime p -> ~(p | m) -> (p ^ 2 | n * m) -> (p ^ 2 | n).
Proof.
  intros p.
  intros n m Hp Hnd [k Hk].
  assert (p | n * m) as Hdivpnm. {
    rewrite Hk.
    auto with *.
  }
  apply prime_mult in Hdivpnm; auto.
  destruct Hdivpnm as [[n' ->]|]; try contradiction.
  assert (p | n' * m) as Hdivpn'm. {
    destruct Hp.
    replace (n' * m) with (k * p); auto with *.
    nia.
  }
  apply prime_mult in Hdivpn'm; auto.
  destruct Hdivpn'm as [[n'' ->]|]; try contradiction.
  auto with *.
  exists n''.
  lia.
Qed.

Lemma prime_mult_sq : forall p n m, prime p -> rel_prime n m -> (p ^ 2 | n * m) -> (p ^ 2 | n) \/ (p ^ 2 | m).
Proof.
  intros p n m Hp Hrp Hdiv.
  destruct (Z.eq_dec 0 m); subst; auto with *.
  destruct (Z.eq_dec 0 n); subst; auto with *.
  
  assert (p | n * m) as [Hpn | Hpm]%prime_mult; auto with *.
  - apply Z.divide_trans with (p ^ 2); auto with *.
  - left.
    apply prime_mult_sq_aux with m; auto.
    apply rel_prime_factor_exclusive with n; auto with *.
    now destruct Hp.
  - right.
    rewrite Z.mul_comm in Hdiv.
    apply rel_prime_sym in Hrp.
    apply prime_mult_sq_aux with n; auto.
    apply rel_prime_factor_exclusive with m; auto with *.
    now destruct Hp.
Qed.

Lemma rel_prime_square_l : forall n m,
    1 <= n -> 1 <= m ->
    rel_prime n m -> Square (n * m) -> Square n.
Proof.
  intros n m Hposn Hposm Hrp (k & Hposk & Hk)%Square_nonneg_root.
  
  assert (1 <= k) as Hposk'; try nia.
  clear Hposk.
  revert Hk.
  revert n Hposn m Hposm Hrp.
  induction (pos_factors Hposk') as [| p k Hp].
  - exists 1.
    nia.
  - intros n Hposn m Hpsm Hrp Hsq.
    pose proof Hp as [Hppos _].
    assert (p ^ 2 | n * m) as Hdivppnm. {
      rewrite Hsq.
      rewrite Z.pow_mul_l.
      auto with *.
    }
    apply prime_mult_sq in Hdivppnm; auto with *.
    destruct Hdivppnm as [[n' ->] | [m' ->]].
    + apply Square_product; auto.
      apply IHf with (m := m); auto with *.
      * cut (0 <= n'); try nia.
        apply Zmult_le_0_reg_r with (n := p * p); auto with *.
        lia.
      * eapply rel_prime_div; eauto with *.
      * rewrite <- Z.sub_move_0_r.
        apply Zmult_integral_l with (p ^ 2); try lia.
        intros x%Z.pow_eq_0; auto with *.
    + apply IHf with (m := m'); auto with *.
      * cut (0 <= m'); try nia.
        apply Zmult_le_0_reg_r with (n := p * p); auto with *.
        lia.
      * apply rel_prime_sym.
        apply rel_prime_sym in Hrp.
        eapply rel_prime_div; eauto with *.
      * rewrite <- Z.sub_move_0_r.
        apply Zmult_integral_l with (p ^ 2). try lia.
        intros x%Z.pow_eq_0; auto with *.
        lia.
Qed.

Lemma rel_prime_square_r : forall n m,
    1 <= n -> 1 <= m ->
    rel_prime n m -> Square (n * m) -> Square m.
Proof.
  intros.
  apply rel_prime_square_l with (m := n); auto.
  - now apply rel_prime_sym.
  - now rewrite Z.mul_comm.
Qed.


Theorem P1 : forall n,
    0 < n -> Z.gcd (n ^ 2 + 1) (5 * n ^ 2 + 9) = if Z.even n then 1 else 2.
Proof.
  intros n Hpos.
  replace (Z.gcd _ _ ) with (Z.gcd (n * n + 1) 4).
  - rewrite Z.gcd_comm.
    destruct (Z.Even_or_Odd n) as [He | Ho].
    + rewrite (proj2 (Z.even_spec _) He).
      destruct He as [m ->].
      replace (2 * m * (2 * m) + 1) with (1 + m ^ 2 * 4); try lia.
      now rewrite  Z.gcd_add_mult_diag_r.
    + rewrite <- Z.negb_odd.
      rewrite (proj2 (Z.odd_spec _) Ho).
      simpl negb.
      destruct Ho as [m ->].
      replace (_ + _) with (2 * (1 + (m * m +  m) * 2)); try lia.
      replace 4 with (2 * 2); auto.
      rewrite Z.gcd_mul_mono_l.
      now rewrite Z.gcd_add_mult_diag_r.
  - rewrite <- (@Z.gcd_add_mult_diag_r _ 4 5).
    f_equal; lia.
Qed.

Theorem P2 : forall n, 0 < n -> ~Square ((n ^ 2 + 1) * (5 * n ^ 2 + 9)).
Proof.
  intros n Hposn.
  assert (1 <= n ^ 2 + 1) as Hp1; try nia.
  assert (1 <= 5 * n ^ 2 + 9) as Hp2; auto with *.
    
  pose proof (P1 Hposn) as Hrp.
  destruct (Z.Even_or_Odd n) as [He | Ho].
  - rewrite <- Z.even_spec in He.
    rewrite He in *.
    rewrite Zgcd_1_rel_prime in Hrp.
    intro Hsq.
    pose proof (rel_prime_square_l Hp1 Hp2 Hrp Hsq) as (m & Hnnnegm & Hm)%Square_nonneg_root.
    destruct (Z.le_gt_cases m n); nia.
  - destruct Ho as [m ->].
    replace (Z.even (2 * m + 1)) with (Z.even (1 + 2 * m)) in Hrp;try solve [f_equal; lia].
    rewrite Z.even_add_mul_2 in Hrp.
    remember (2 * m ^ 2 + 2 * m + 1) as X.
    replace ((2 * m + 1) ^ 2 + 1) with (X * 2) in *; try lia.
    remember (10 * m * (m + 1) + 7) as Y.
    replace (5 * (2 * m + 1) ^ 2 + 9) with (Y * 2) in *; try lia.
    rewrite Z.gcd_mul_mono_r_nonneg, Z.mul_id_l, Zgcd_1_rel_prime in Hrp; auto with *.
    intro Hsq.
    absurd (Square Y).
    + intro HsqY.
      cut (Y mod 4 = 3 /\ Y mod 4 = 1); auto with *.
      split.
      * rewrite HeqY.
        rewrite Z.add_mod; try discriminate.
        rewrite <- Z.mul_assoc.
        assert (2 | m * (m + 1)) as [m' Heqm']. {
          destruct (Z.Even_or_Odd m) as [[m' ->] | [m' ->]].
          - exists (m' * (2 * m' + 1)). lia.
          - exists ((2 * m' + 1) * (m' + 1)). lia.
        }
        replace (10 * (m * (m + 1))) with (5 * m' * 4); try lia.
        rewrite Z.mod_mul; auto with *.
      * apply Square_nonneg_root in HsqY.
        destruct HsqY as (Y' & HnnegY' & ->).
        destruct (Z.Even_or_Odd Y') as [[Y'' ->] | [Y'' ->]]; try lia.
        replace (_ ^ 2) with (1 + (Y'' ^ 2 + Y'') * 4); try lia.
        rewrite Z.mod_add; auto with *.
    + apply rel_prime_square_r with X; auto with *.
      apply Square_product_inv_l with 4; auto with *.
      * apply (eq_ind _ _ Hsq).
        lia.
      * now exists 2.
Qed.
