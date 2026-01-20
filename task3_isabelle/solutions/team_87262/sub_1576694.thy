theory Task_VeryVerifiers imports Main begin

subsection ‹Part I›

lemma foldr_conj_init: "foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y"
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems have "foldr (\<lambda>x b. P x \<and> b) xs y" by simp
  with Cons.IH show ?case by blast
qed

lemma foldr_conj_prop:
  "foldr (\<lambda>x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall>x \<in> set xs. P x)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

subsection ‹Part II›

primrec pick :: "nat ⇒ 'a list ⇒ 'a list" where
  "pick 0 xs = []" |
  "pick (Suc n) xs = (case xs of [] ⇒ [] | x # xs' ⇒ x # pick n xs')"

lemma pick_length: "length (pick n xs) = min n (length xs)"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    then show ?thesis by (simp add: Suc.IH)
  qed
qed

lemma pick_items: "∀i < length (pick n xs). (pick n xs) ! i = xs ! i"
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    have step: "⋀i. i < length (pick (Suc n) (x # xs')) ⟹
                    (pick (Suc n) (x # xs')) ! i = (x # xs') ! i"
    proof -
      fix i
      assume Hi: "i < length (pick (Suc n) (x # xs'))"
      show "(pick (Suc n) (x # xs')) ! i = (x # xs') ! i"
      proof (cases i)
        case 0
        then show ?thesis by (simp add: Cons)
      next
        case (Suc j)
        have L: "length (pick (Suc n) (x # xs')) = Suc (length (pick n xs'))"
          by (simp add: Cons)
        from Hi L Suc have "j < length (pick n xs')" by simp
        with Suc.IH[of xs'] have "(pick n xs') ! j = xs' ! j" by simp
        with Cons Suc show ?thesis by simp
      qed
    qed
    from step show ?thesis by blast
  qed
qed

lemma pick_take_eq: "pick n xs = take n xs"
  by (simp add: list_eq_iff_nth_eq pick_items pick_length)

subsection ‹Part III›

primrec conss :: "'a list ⇒ 'a list list ⇒ 'a list list" where
  conss_Nil:  "conss xs [] = []" |
  conss_Cons: "conss xs (y # ys) =
                 (case xs of [] ⇒ []
                           | z # zs ⇒ (z # y) # conss zs ys)"

lemma conss_test_1: \<open>conss [1] [] = []\<close> by simp
lemma conss_test_2: \<open>conss [1, 2] [] = []\<close> by simp
lemma conss_test_3: \<open>conss [] [[1]] = []\<close> by simp
lemma conss_test_4: \<open>conss [] [[1, 2]] = []\<close> by simp
lemma conss_test_5: \<open>conss [1] [[2]] = [[1, 2]]\<close> by simp
lemma conss_test_6: \<open>conss [1, 2] [[3], [4]] = [[1, 3], [2, 4]]\<close> by simp
lemma conss_test_7: \<open>conss [1, 2] [[3]] = [[1, 3]]\<close> by simp
lemma conss_test_8: \<open>conss [1] [[2], [3]] = [[1, 2]]\<close> by simp

lemma conss_length: "length (conss xs ys) = min (length xs) (length ys)"
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons z zs)
    then show ?thesis by (simp add: Cons.IH)
  qed
qed

lemma conss_Cons_Cons: "conss (x # xs) (y # ys) = (x # y) # conss xs ys"
  by simp

lemma hd_conss_tl:
  "∀x ∈ set xss. x ≠ [] ⟹ conss (map hd xss) (map tl xss) = xss"
proof (induction xss)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems have xne: "x ≠ []" and allne: "∀x∈set xs. x ≠ []" by simp_all
  have "conss (map hd (x # xs)) (map tl (x # xs))
        = (hd x # tl x) # conss (map hd xs) (map tl xs)" by (simp add: xne)
  also have "(hd x # tl x) = x" using xne by simp
  also have "x # conss (map hd xs) (map tl xs) = x # xs" using Cons.IH allne by simp
  finally show ?case by simp
qed

lemma hd_conss_tl_filter:
  "conss
     (map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
     (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
   = filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s"
proof -
  have ne: "∀x ∈ set (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s). x \<noteq> []" by simp
  from hd_conss_tl[OF ne] show ?thesis by simp
qed

lemma tl_filter_hd:
  "x # xs \<in> set s \<longleftrightarrow>
   xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s))"
proof (induction s)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases y)
    case Nil
    then show ?thesis using Cons.IH by simp
  next
    case (Cons h t)
    show ?thesis
    proof (cases "h = x")
      case True
      then show ?thesis using Cons.IH Cons by simp
    next
      case False
      then show ?thesis using Cons.IH Cons by simp
    qed
  qed
qed

end
