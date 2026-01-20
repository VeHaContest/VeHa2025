theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs arbitrary: y)
  case Nil
  assume Prem: \<open>foldr (\<lambda> x b. P x \<and> b) [] y\<close>
  from Prem have \<open>y\<close> by simp
  then show \<open>y\<close> by blast
next
  case (Cons x xs)
  assume Prem: \<open>foldr (\<lambda> x b. P x \<and> b) (x # xs) y\<close>
  assume IH: \<open>\<And>y. foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
  from Prem have \<open>P x \<and> (foldr (\<lambda> x b. P x \<and> b) xs y)\<close> by simp
  then have \<open>foldr (\<lambda> x b. P x \<and> b) xs y\<close> by blast
  moreover with IH have \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close> by blast
  ultimately show \<open>y\<close> by blast
qed
  
\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induction xs)
  case Nil
  have \<open>foldr (\<lambda> x b. P x \<and> b) [] True = True\<close> by simp
  moreover have \<open>\<forall> x \<in> set []. P x = True\<close> by simp
  ultimately show ?case by simp
next
  case (Cons y ys)
  assume IH: \<open>foldr (\<lambda> x b. P x \<and> b) ys True \<longleftrightarrow> (\<forall> x \<in> set ys. P x)\<close>
  have \<open>foldr (\<lambda> x b. P x \<and> b) (y # ys) True \<longleftrightarrow> (P y) \<and> (foldr (\<lambda> x b. P x \<and> b) ys True)\<close> by simp
  moreover have \<open>(\<forall> x \<in> set (y # ys). P x) \<longleftrightarrow> (P y) \<and> (\<forall> x \<in> set ys. P x)\<close> by simp
  moreover have \<open>((P y) \<and> (foldr (\<lambda> x b. P x \<and> b) ys True)) \<longleftrightarrow> ((P y) \<and> (\<forall> x \<in> set ys. P x))\<close> using IH by blast
  then show ?case by simp
qed

subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
	\<open>pick 0 xs = []\<close> |
	\<open>pick (Suc n) xs = (case xs of [] \<Rightarrow> [] | y # ys \<Rightarrow> y # (pick n ys))\<close>

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc k)
  then show ?case
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons y ys)
    have \<open>length (pick (Suc k) (y # ys)) = Suc (length (pick k ys))\<close> by simp
    assume IH1: \<open>\<And>ws :: 'a list. length (pick k ws) = min k (length ws)\<close>
    then have \<open>length (pick (Suc k) (y # ys)) = Suc (min k (length ys))\<close> by simp
    then have \<open>length (pick (Suc k) (y # ys)) = min (Suc k) (Suc (length ys))\<close> by simp
    then show \<open>length (pick (Suc k) (y # ys)) = min (Suc k) (length (y # ys))\<close> by simp
  qed
qed

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
proof (induction ys arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons z zs)
  assume IH0: \<open>\<And>xs :: 'a list. length (conss xs zs) = min (length xs) (length zs)\<close>
  then show ?case
  proof (induction xs)
    case Nil
    show ?case by simp
  next
    case (Cons w ws)
    have IH: \<open>length (conss ws zs) = min (length ws) (length zs)\<close> using IH0 by simp
    have \<open>min (length (w # ws)) (length (z # zs)) = min (Suc (length ws)) (Suc (length zs))\<close> by simp
    moreover have \<open>min (length (w # ws)) (length (z # zs)) = Suc (min (length ws) (length zs))\<close> by simp
    moreover have \<open>length (conss (w # ws) (z # zs)) = length ((w # z) # conss ws zs)\<close> by simp
    moreover then have \<open>length (conss (w # ws) (z # zs)) = Suc (length (conss ws zs))\<close> by simp
    moreover then have \<open>length (conss (w # ws) (z # zs)) = Suc (min (length ws) (length zs))\<close> using IH by simp
    moreover then show \<open>length (conss (w # ws) (z # zs)) = min (length (w # ws)) (length (z # zs))\<close> by simp
  qed
qed

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
  using conss_Cons by simp

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  assume IH: \<open>\<forall> x \<in> set ys. x \<noteq> [] \<Longrightarrow> conss (map hd ys) (map tl ys) = ys\<close>
  assume H: \<open>\<forall> x \<in> set (y # ys). x \<noteq> []\<close>
  then have P: \<open>y \<noteq> [] \<and> (\<forall> x \<in> set ys. x \<noteq> [])\<close> by simp
  then have \<open>\<forall> x \<in> set ys. x \<noteq> []\<close> by simp
  then have Q: \<open>conss (map hd ys) (map tl ys) = ys\<close> using IH by simp
  with P have R: \<open>y \<noteq> []\<close> by simp
  have \<open>map hd (y # ys) = hd y # map hd ys\<close> by simp
  moreover have \<open>map tl (y # ys) = tl y # map tl ys\<close> by simp
  then have \<open>conss (map hd (y # ys)) (map tl (y # ys)) = conss (hd y # map hd ys) (tl y # map tl ys)\<close> by simp
  then have \<open>conss (map hd (y # ys)) (map tl (y # ys)) = (hd y # tl y) # conss (map hd ys) (map tl ys)\<close> by simp
  then have S: \<open>conss (map hd (y # ys)) (map tl (y # ys)) = (hd y # tl y) # ys\<close> using Q by simp
  moreover have \<open>hd y # tl y = y\<close> using R by simp
  then show \<open>conss (map hd (y # ys)) (map tl (y # ys)) = y # ys\<close> using S by simp
qed

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
proof (induction s)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have \<open>\<forall>x \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (y # ys)). x \<noteq> []\<close> by simp
  then show ?case using hd_conss_tl by blast
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
	sorry

lemma filter_in: \<open>x \<in> set s \<Longrightarrow> P x \<Longrightarrow> x \<in> set (filter P s)\<close>
proof
  assume \<open>x \<in> set s\<close>
  assume \<open>P x\<close>
  oops

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof (cases \<open>x # xs \<in> set s\<close>)
  case True
  assume \<open>x # xs \<in> set s\<close>
  have P: \<open>x # xs \<noteq> []\<close> by simp
  have Q: \<open>hd (x # xs) = x\<close> by simp
  then have \<open>x # xs \<in> set (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)\<close> oops

end