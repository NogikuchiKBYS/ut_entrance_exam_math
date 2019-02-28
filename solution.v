Require Import ZArith Zwf.
Require Import ZArith.Znumtheory.
Require Import Lia.
Set Implicit Arguments.
Open Scope Z.

Ltac cut_hyp H := refine ((fun x f => f (H x)) _ _); [| clear H; intro H].

Lemma fequal_impl : forall {A} (P : A -> Prop) (x y : A), x = y -> P x -> P y.
Proof.
  intros.
  now subst.
Qed.

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

Lemma factor_prod : forall a b c d, (a | b) -> (c | d) -> (a * c | b * d).
Proof.
  intros a b c d [b' -> ] [d' ->].
  exists (b' * d').
  lia.
Qed.

Lemma divide_pow : forall n a b, (a | b) -> (a ^ n | b ^ n).
Proof.
  intro n.
  induction n using (well_founded_ind (Zwf_well_founded 0)).
  intros a b.
  destruct (Z.lt_ge_cases n 0) as [| Hge0].
  - repeat rewrite Z.pow_neg_r; auto with *.
  - destruct (Zle_lt_or_eq _ _ Hge0) as [Hge1%Zlt_le_succ | Heq0].
    + simpl in Hge1.
      destruct (Zle_lt_or_eq _ _ Hge1) as [Hge2%Zlt_le_succ | Heq1].
      * specialize (H (n - 1)).
        cut_hyp H. {
          unfold Zwf.
          auto with *.
        }
        intro Hdiv.
        specialize (H a b Hdiv).
        replace n with (n - 1 + 1); auto with *.
        repeat rewrite Z.pow_add_r; auto with *.
        repeat rewrite Z.pow_1_r.
        now apply factor_prod.
      * subst.
        now repeat rewrite Z.pow_1_r.
    + subst.
      repeat rewrite Z.pow_0_r; auto  with *.
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

Lemma factoring_ind :
  forall (P : Z -> Prop)
    (HP1 : P 1)
    (IHP : forall p m, prime p -> P m -> P (m * p)),
  forall n, 1 <= n -> P n.
Proof.
  intros until n.
  induction n using (well_founded_ind (Zwf_well_founded 0)).
  intros [Hn|<-]%Zle_lt_or_eq; auto.
  destruct (prime_dec n) as [Hp | Hnp].
  - specialize (IHP n 1 Hp).
    rewrite Z.mul_1_l in IHP.
    auto.
  - apply not_prime_divide_prime in Hnp; auto.
    destruct Hnp as (p & Hrange & Hdiv & Hp).
    destruct Hdiv as [m ->].
    apply IHP; auto.
    assert (1 <= m) as Hm. {
      destruct Hrange as [H1p Hpmp].
      rewrite <- (Z.mul_1_l p) in Hpmp at 1.
      apply Z.mul_lt_mono_pos_r in Hpmp; auto with *.
    }
    apply H; auto with *.
    unfold Zwf.
    split; auto with *.
    apply Z.lt_mul_diag_r; auto with *.
Qed.


Lemma divide_pow_prime : forall n p b, 0 < n -> prime p -> 1 <= b -> (p ^ n | b ^ n) -> (p | b).
Proof.
  intros n p b Hn Hp Hb Hdiv.
  assert (p | b ^ n) as Hdiv'. {
    apply Z.divide_trans with (p ^ n); auto with *.
    replace n with (1 + (n - 1)); auto with *.
    rewrite Z.pow_add_r; auto with *.
    rewrite Z.pow_1_r.
    auto with *.
  }
  clear Hdiv.
  induction n using (well_founded_ind (Zwf_well_founded 0)).
  unfold Zwf in *.
  destruct (Zle_lt_or_eq 1 n); auto with *.
  - replace n with (1 + (n - 1)) in Hdiv'; auto with *.
    rewrite Z.pow_add_r in Hdiv'; auto with *.
    rewrite Z.pow_1_r in Hdiv'.
    apply prime_mult in Hdiv'; auto.
    destruct Hdiv'; auto.
    apply H with (y := n - 1); auto with *.
  - subst.
    now rewrite Z.pow_1_r in *.
Qed.

Lemma divide_pow_inv : forall n a b, 0 < n -> 1 <= a -> 1 <= b -> (a ^ n | b ^ n) -> (a | b).
Proof.
  intros n a b Hn Ha Hb.
  revert b Hb.
  apply factoring_ind with (n := a); auto with *.
  intros p m Hp IHa b Hb Hdiv.
  destruct (@divide_pow_prime n p b) as [k ->]; auto .
  - apply Z.divide_trans with ((m * p) ^ n); auto.
    rewrite Z.pow_mul_l.
    auto with *.
  - apply Z.mul_divide_mono_r.
    apply IHa.
    + destruct Hp.
      destruct (Z.le_0_mul k p) as [Hkp | Hkp]; auto with *.
      destruct Hkp as [Hk _].
      destruct (Zle_lt_or_eq _ _ Hk); subst; auto with *.
    + apply Z.mul_divide_cancel_r with (p := p ^ n).
      * intros H%Z.pow_eq_0; subst; auto with *.
      * repeat rewrite <- Z.pow_mul_l.
        assumption.
Qed.

Definition Square n := exists m, n = m ^ 2.

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
    assert (1 <= n') as Hposn'. {
      destruct (Zle_lt_or_eq _ _ Hnnegn'); subst; auto with *.
      lia.
    }
    apply divide_pow_inv with (n := 2); auto with *.
    - destruct (Zle_lt_or_eq _ _ Hnnegk); subst; auto with *.
      cbn in *.
      destruct (Zmult_integral _ _ Hk); auto with *.
    - rewrite <- Hk.
      auto with *.
  }
  exists k'.
  rewrite Z.pow_mul_l in Hk.
  rewrite Z.mul_comm in Hk.
  rewrite Z.mul_cancel_r in Hk; auto with *.
Qed.

Lemma Square_product_inv_l : forall n m, 0 <> m -> Square (n * m) -> Square m -> Square n.
Proof.
  intros.
  rewrite Z.mul_comm in *.
  eapply Square_product_inv_r; eauto.
Qed.

Lemma rel_prime_square_l : forall n m,
    1 <= n -> 1 <= m ->
    rel_prime n m -> Square (n * m) -> Square n.
Proof.
  intros n m Hposn Hposm Hrp (k & Hposk & Hk)%Square_nonneg_root.
  
  assert (1 <= k) as Hposk'. {
    destruct (Zle_lt_or_eq _ _ Hposk); auto with *.
    subst.
    cbn in *.
    destruct (Zmult_integral _ _ Hk); subst; auto.
  }
  clear Hposk.
  revert Hk.
  revert n Hposn m Hposm Hrp.
  apply factoring_ind with (n := k); auto.
  - exists 1.
    cbn in *.
    apply Z.mul_eq_1 in Hk.
    lia.
  - intros p k' Hp IH n Hposn m Hpsm Hrp Hsq.
    pose proof Hp as [Hppos _].
    assert (p ^ 2 | n * m) as Hdivppnm. {
      rewrite Hsq.
      rewrite Z.pow_mul_l.
      auto with *.
    }
    assert (p | n * m) as Hdivpnm. {
      apply Z.divide_trans with (p ^ 2); auto with *.
      cbn.
      auto with *.
    }
    apply prime_mult in Hdivpnm; auto.
    destruct Hdivpnm as [[n' ->]|[m' ->]].
    + assert (p | n') as Hdivpn'. {
        rewrite Z.pow_2_r in Hdivppnm.
        replace (n' * p * m) with (p * (n' * m)) in Hdivppnm; try lia.
        rewrite Z.mul_divide_cancel_l in Hdivppnm; auto with *.
        apply prime_mult in Hdivppnm; auto.
        destruct Hdivppnm; auto.
        contradict H.
        eapply rel_prime_factor_exclusive; eauto with *.
        lia.
      }
      destruct Hdivpn' as [n'' ->].
      rewrite <- Z.mul_assoc.
      apply Square_product; auto.
      apply IH with (m := m); auto with *.
      * cut (0 <= n'').
        --  intros [|<-]%Zle_lt_or_eq; auto with *.
        -- apply Zmult_le_0_reg_r with (n := p * p); auto with *.
           lia.
      * eapply rel_prime_div; eauto with *.
      * rewrite <- Z.sub_move_0_r.
        apply Zmult_integral_l with (p ^ 2); try lia.
        intros x%Z.pow_eq_0; auto with *.
    + assert ((p | m')) as Hdivpm'. {
        rewrite Z.pow_2_r in Hdivppnm.
        replace (n * (m' * p)) with (p * (n * m')) in Hdivppnm; try lia.
        rewrite Z.mul_divide_cancel_l in Hdivppnm; auto with *.
        apply prime_mult in Hdivppnm; auto.
        destruct Hdivppnm; auto.
        contradict H.
        apply rel_prime_sym in Hrp.
        eapply rel_prime_factor_exclusive; eauto with *.
        lia.
      }
      destruct Hdivpm' as [m'' ->].
      apply IH with (m := m''); auto with *.
      * cut (0 <= m''). 
        -- intros [|<-]%Zle_lt_or_eq; auto with *.
        -- apply Zmult_le_0_reg_r with (n := p * p); auto with *.
           lia.
      * apply rel_prime_sym.
        apply rel_prime_sym in Hrp.
        apply (rel_prime_div _ _ _ Hrp).
        auto with *.
      * rewrite <- Z.sub_move_0_r.
        apply Zmult_integral_l with (p ^ 2); try lia.
        intros x%Z.pow_eq_0; auto with *.
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
  assert (1 <= n ^ 2 + 1) as Hp1. {
    rewrite Z.pow_2_r.
    replace 1 with (0 + 1) at 1; auto.
    apply Z.add_le_mono_r.
    auto with *.
  }
  assert (1 <= 5 * n ^ 2 + 9) as Hp2; auto with *.
    
  pose proof (P1 Hposn) as Hrp.
  destruct (Z.Even_or_Odd n) as [He | Ho].
  - rewrite <- Z.even_spec in He.
    rewrite He in *.
    rewrite Zgcd_1_rel_prime in Hrp.
    intro Hsq.
    pose proof (rel_prime_square_l Hp1 Hp2 Hrp Hsq) as (m & Hnnnegm & Hm)%Square_nonneg_root.
    destruct (Z.le_gt_cases m n) as [Hle | Hgt].
    + assert (m ^ 2 < n ^ 2 + 1); auto with *.
      apply Z.lt_le_trans with (m ^ 2 + 1); auto with *.
      apply Z.add_le_mono_r.
      apply Z.pow_le_mono_l.
      split; auto.
    + assert (n ^ 2 + 1 < m ^ 2); auto with *.
      assert (n + 1 <= m); auto with *.
      apply Z.lt_le_trans with ((n + 1) ^ 2); try lia.
      apply Z.pow_le_mono_l; auto with *.
  - assert (Z.even n = false) as Heven. {
      rewrite <- Z.odd_spec in Ho.
      rewrite <- Z.negb_odd, Ho.
      reflexivity.
    }
    rewrite Heven in Hrp.
    unfold negb in Hrp.
    destruct Ho as [m ->].
    remember (2 * m ^ 2 + 2 * m + 1) as X.
    replace ((2 * m + 1) ^ 2 + 1) with (X * 2) in *; try lia.
    remember (10 * m * (m + 1) + 7) as Y.
    replace (5 * (2 * m + 1) ^ 2 + 9) with (Y * 2) in *; try lia.
    rewrite Z.gcd_mul_mono_r_nonneg in Hrp; auto with *.
    rewrite Z.mul_id_l in Hrp; auto with *.
    rewrite Zgcd_1_rel_prime in Hrp.
    intro Hsq.
    assert (Square Y). {
      apply rel_prime_square_r with X; auto with *.
      apply Square_product_inv_l with 4; auto with *.
      + refine (fequal_impl _ _ Hsq).
        lia.
      + exists 2.
        lia.
    }

    assert (forall n, Square n -> n mod 4 <> 3) as Hmod4. {
      clear.
      intros _ (m & Hnnegm & ->)%Square_nonneg_root.
      destruct (Z.Even_or_Odd m).
      - assert (4 | m ^ 2) as Hdiv. {
          destruct H as [m' ->].
          exists (m' ^ 2). lia.
        }
        rewrite <- Z.mod_divide in Hdiv; auto with *.
      - destruct H as [m' ->].
        replace (_ ^ 2) with (1 + (m' ^ 2 + m') * 4); try lia.
        rewrite Z.mod_add; auto with *.
    }
    absurd (Y mod 4 = 3); auto.
    rewrite HeqY.
    assert (4 | 10 * m * (m + 1)) as Hdiv. {
      replace 4 with (2 * 2); try lia.
      rewrite <- Z.mul_assoc.
      apply factor_prod.
      - rewrite <- Z.mod_divide; auto with *.
      - destruct (Z.Even_or_Odd m) as [[m' ->] | [m' ->]]; auto with *.
        replace (2 * m' + 1 + 1) with ((m' + 1) * 2); auto with *.
    }
    rewrite <- Z.mod_divide in Hdiv; try discriminate.
    rewrite Z.add_mod; try discriminate.
    rewrite Hdiv.
    reflexivity.
Qed.
