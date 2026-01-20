theory Task imports Main begin

subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems have "P x \<and> foldr (\<lambda> x b. P x \<and> b) xs y" by simp
  with Cons.IH show ?case by blast
qed


\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
  \<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof
    assume lhs: "foldr (\<lambda> x b. P x \<and> b) (x # xs) True"
    show "\<forall> x' \<in> set (x # xs). P x'"
    proof
      fix x'
      assume asm: "x' \<in> set (x # xs)"
      show "P x'"
      proof (cases "x' = x")
        case True
        then show ?thesis using lhs by simp
      next
        case False
        then have "x' \<in> set xs" using asm by simp
        moreover have "foldr (\<lambda> x b. P x \<and> b) xs True" using lhs by simp
        ultimately show ?thesis using Cons.IH by blast
      qed
    qed
  next
    assume rhs: "\<forall> x' \<in> set (x # xs). P x'"
    show "foldr (\<lambda> x b. P x \<and> b) (x # xs) True"
      using rhs Cons.IH by simp
  qed
qed

subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "pick 0 xs = []" |
    "pick (Suc n) xs = (case xs of
        [] \<Rightarrow> [] |
        y # ys \<Rightarrow> y # pick n ys)"

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    then show ?thesis using Suc.IH[of ys] by simp
  qed
qed

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
proof (induction n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (intro allI impI)
    fix i
    assume "i < length (pick (Suc n) xs)"
    show "pick (Suc n) xs ! i = xs ! i"
    proof (cases xs)
      case Nil
      with \<open>i < length (pick (Suc n) xs)\<close> show ?thesis by simp
    next
      case (Cons y ys)
      with \<open>i < length (pick (Suc n) xs)\<close> have "i < length (y # pick n ys)" by simp
      then show ?thesis
      proof (cases i)
        case 0
        with Cons show ?thesis by simp
      next
        case (Suc j)
        with \<open>i < length (y # pick n ys)\<close> have "j < length (pick n ys)" by simp
        then have "pick n ys ! j = ys ! j" using Suc.IH[of ys] by simp
        with Cons Suc show ?thesis by simp
      qed
    qed
  qed
qed

\<comment> \<open>Function @{term pick} is equivalent to function @{term take}.\<close>
lemma pick_take_eq: "pick n xs = take n xs"
proof (induction n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    then show ?thesis using Suc.IH[of ys] by simp
  qed
qed

subsection \<open>Part III\<close>

\<comment> \<open>The function precedes every list in the second argument (which is a list of lists) with the corresponding item from the first argument. The lists that have no corresponding pair are replaced with an empty list.\<close>
primrec conss :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "conss xs [] = []" |
  "conss xs (y # ys) =
    (case xs of 
      [] \<Rightarrow> [] | 
      z # zs \<Rightarrow> (z # y) # conss zs ys)"

\<comment> \<open>The following tests demonstrate how the function @{term conss} is expected to work.\<close>
lemma conss_test_1: \<open>conss [1] [] = []\<close> by simp
lemma conss_test_2: \<open>conss [1, 2] [] = []\<close> by simp
lemma conss_test_3: \<open>conss [] [[1]] = []\<close> by simp
lemma conss_test_4: \<open>conss [] [[1, 2]] = []\<close> by simp
lemma conss_test_5: \<open>conss [1] [[2]] = [[1, 2]]\<close> by simp
lemma conss_test_6: \<open>conss [1, 2] [[3], [4]] = [[1, 3], [2, 4]]\<close> by simp
lemma conss_test_7: \<open>conss [1, 2] [[3]] = [[1, 3]]\<close> by simp
lemma conss_test_8: \<open>conss [1] [[2], [3]] = [[1, 2]]\<close> by simp

\<comment> \<open>The length of @{term \<open>conss xs ys\<close>} is the minimum length of @{term xs} and @{term ys}.\<close>
lemma conss_length: \<open>length (conss xs ys) = min (length xs) (length ys)\<close>
proof (induction ys arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons z zs)
    then show ?thesis by (simp add: Cons.IH)
  qed
qed

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
  by simp

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
  \<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  assume non_empty: "\<forall>y \<in> set (x # xs). y \<noteq> []"
  then have x_non_empty: "x \<noteq> []" by simp
  have xs_non_empty: "\<forall>y \<in> set xs. y \<noteq> []" using non_empty by simp
  
  from x_non_empty show ?case
  proof (cases x)
    case Nil
    then show ?thesis using x_non_empty by simp
  next
    case (Cons h t)
    have "conss (map hd (x # xs)) (map tl (x # xs)) = 
          conss (hd x # map hd xs) (tl x # map tl xs)" by simp
    then show ?thesis
      by (simp add: Cons conss_Cons_Cons Cons.IH xs_non_empty)
  qed
qed

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
  \<open>conss
    (map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
    (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
    = filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
proof -
  let ?filtered = "filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s"
  
  have non_empty_filtered: "\<forall>x \<in> set ?filtered. x \<noteq> []"
    by auto
    
  show ?thesis
    using non_empty_filtered
    by (simp add: hd_conss_tl)
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
  by (cases xs) auto

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
      xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof
  assume "x # xs \<in> set s"
  then have "x # xs \<in> {ys \<in> set s. ys \<noteq> [] \<and> hd ys = x}"
    by auto
  then have "tl (x # xs) \<in> tl ` {ys \<in> set s. ys \<noteq> [] \<and> hd ys = x}"
    by (rule imageI)
  then show "xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s))"
    by simp
next
  assume "xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s))"
  then have "xs \<in> tl ` {ys \<in> set s. ys \<noteq> [] \<and> hd ys = x}"
    by simp
  then obtain ys where "ys \<in> set s" "ys \<noteq> []" "hd ys = x" "xs = tl ys"
    by auto
  then have "ys = x # xs"
    by (cases ys) auto
  with \<open>ys \<in> set s\<close> show "x # xs \<in> set s"
    by simp
qed

end