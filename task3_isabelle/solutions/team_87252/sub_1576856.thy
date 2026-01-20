theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  assume Prem: \<open>foldr (\<lambda> x b. P x \<and> b) (x # xs) y\<close>
  then have \<open>P x \<and> foldr (\<lambda> x b. P x \<and> b) xs y\<close> by simp
  then have Prem_it: \<open>foldr (\<lambda> x b. P x \<and> b) xs y\<close> by blast
  assume IH: \<open>\<And>y. foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
  with Prem_it have y by blast
  then show ?case by blast
qed


lemma foldr_conj_prop_necessary: \<open>foldr (\<lambda> x b. P x \<and> b) xs True \<Longrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume \<open>foldr (\<lambda> x b. P x \<and> b) (a # xs) True\<close>
  then have X: \<open>P a \<and> foldr (\<lambda> x b. P x \<and> b) xs True\<close> by simp
  then have \<open>P a\<close> by blast
  from X have Y: \<open>foldr (\<lambda> x b. P x \<and> b) xs True\<close> by blast
  assume IH: \<open>foldr (\<lambda> x b. P x \<and> b) xs True \<Longrightarrow> (\<forall> x \<in> set xs. P x)\<close>
  with Y have \<open>\<forall> x \<in> set xs. P x\<close> by blast
  with \<open>P a\<close> have \<open>\<forall> x \<in> set (a # xs). P x\<close> by simp
  then show ?case by blast
qed

lemma foldr_conj_prop_sufficient: \<open>(\<forall> x \<in> set xs. P x) \<Longrightarrow> foldr (\<lambda> x b. P x \<and> b) xs True\<close>
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume Prem: \<open>\<forall> x \<in> set (a # xs). P x\<close>
  then have \<open>P a\<close> by simp
  from Prem have Prem_it: \<open>\<forall> x \<in> set xs. P x\<close> by simp
  assume IH: \<open>(\<forall> x \<in> set xs. P x) \<Longrightarrow> foldr (\<lambda> x b. P x \<and> b) xs True\<close>
  with Prem_it have \<open>foldr (\<lambda> x b. P x \<and> b) xs True\<close> by blast
  with \<open>P a\<close> have \<open>foldr (\<lambda> x b. P x \<and> b) (a # xs) True\<close> by simp
  then show ?case by blast
qed

\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop: \<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
  using foldr_conj_prop_necessary foldr_conj_prop_sufficient by blast


subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
	pick_Zero: \<open>pick 0 xs = []\<close> |
  pick_Suc:  \<open>pick (Suc n) xs = (case xs of Nil \<Rightarrow> [] | (x # xt) \<Rightarrow> (x # pick n xt))\<close>

lemma not_nil_obtain: \<open>xs \<noteq> [] \<Longrightarrow> \<exists> x xt. xs = x # xt\<close>
proof (induction xs)
  case Nil
  then have \<open>\<not> (xs \<noteq> [])\<close> by simp
  then show ?case by blast
  \<comment> \<open>Мда, вот это проблема. И как с этим бороться?\<close>
  oops

(*
lemma not_nil_xs: \<open>Suc n \<le> length xs \<Longrightarrow> xs \<noteq> []\<close> by auto

lemma l1: \<open>n \<le> length xs \<Longrightarrow> length (pick n xs) = n\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases \<open>Suc n \<le> length xs\<close>)
    case True
    then have \<open>xs \<noteq> Nil\<close> using not_nil_xs by blast
    then obtain x xt where \<open>xs = (x # xt)\<close> by auto
    with pick_Suc have \<open>(pick (Suc n) xs) = ((hd xs) # (pick n (tl xs)))\<close> by simp
    oops

lemma l2: \<open>n \<le> length xs \<Longrightarrow> length (pick n (x # xs)) = length (pick n xs)\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have \<open>n \<le> length xs\<close> by simp
(*  assume \<open>(Suc n) \<le> length xs\<close>
  assume \<open>pick n (x # xs) = pick n xs\<close>*)
  then have \<open>length (pick n xs) = n\<close> by simp
  oops

lemma pick_nil: \<open>pick n [] = []\<close>
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by simp
qed

lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction xs)
  case Nil
  then show ?case using pick_nil by simp
next
  case (Cons x xs)
  show ?case
  proof (cases \<open>n \<le> length xs\<close>)
    case True
    assume \<open>n \<le> length xs\<close>
    then have rel_val: \<open>min n (length xs) = n\<close> by simp
    assume \<open>length (pick n xs) = min n (length xs)\<close>
    with rel_val have \<open>length (pick n xs) = n\<close> by simp
    then have \<open>pick n (x # xs) = pick n xs\<close> by simp
    then have \<open>length (pick n (x # xs)) = min n (length xs)\<close> by blast
    oops
*)
\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    \<comment> \<open>Почему-то IH_n - предположение внешней индукции считается, как новое условие\<close>
    assume IH_n: \<open>length (pick n xs) = min n (length xs)\<close>
    assume IH_xs: \<open>length (pick (Suc n) xs) = min (Suc n) (length xs)\<close>
    then have \<open>length (pick (Suc n) (x # xs)) = Suc (length (pick n xs))\<close> by simp
    then have \<open>min (Suc n) (length (x # xs)) = Suc (min n (length xs))\<close> by simp
    then show \<open>length (pick (Suc n) (x # xs)) = min (Suc n) (length (x # xs))\<close> by blast
    oops


\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
	sorry

\<comment> \<open>Function @{term pick} is equivalent to function @{term take}.\<close>
lemma pick_take_eq: \<open>pick n xs = take n xs\<close>
	by (simp add: list_eq_iff_nth_eq pick_items pick_length)


subsection \<open>Part III\<close>

\<comment> \<open>The function precedes every list in the second argument (which is a list of lists) with the corresponding item from the first argument. The lists that have no corresponding pair are replaced with an empty list.\<close>
primrec conss :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
	conss_Nil:	"conss xs [] = []" |
	conss_Cons:	"conss xs (y # ys) =
			(case xs of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z # y) # conss zs ys)"

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
	sorry

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
	sorry

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
	sorry

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
	sorry

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
	sorry

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
	sorry

end