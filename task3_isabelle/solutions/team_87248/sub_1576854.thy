theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  assume "foldr (\<lambda>x b. P x \<and> b) (x # xs) y"
  hence "P x \<and> foldr (\<lambda>x b. P x \<and> b) xs y" by simp
  hence "foldr (\<lambda>x b. P x \<and> b) xs y" by simp
  thus "y" using Cons.hyps by blast
qed

value "foldr (\<lambda>x b. P x \<and> b) [1,1,3,0] False"

\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof
    assume "foldr (\<lambda>x b. P x \<and> b) (x # xs) True"
    hence "P x \<and> foldr (\<lambda>x b. P x \<and> b) xs True" by simp
    hence "P x" and "foldr (\<lambda>x b. P x \<and> b) xs True" by simp_all
    from \<open>foldr (\<lambda>x b. P x \<and> b) xs True\<close> Cons.hyps have "\<forall>x \<in> set xs. P x" by blast
    with \<open>P x\<close> show "\<forall>x \<in> set (x # xs). P x" by simp
  next
    assume "\<forall>x \<in> set (x # xs). P x"
    hence "P x" and "\<forall>x \<in> set xs. P x" by simp_all
    from \<open>\<forall>x \<in> set xs. P x\<close> Cons.hyps have "foldr (\<lambda>x b. P x \<and> b) xs True" by blast
    with \<open>P x\<close> show "foldr (\<lambda>x b. P x \<and> b) (x # xs) True" by simp
  qed
qed

value "foldr (\<lambda>x b. P x \<and> b) [1,2,3] True"          \<comment> \<open>True\<close>
value "\<forall>x \<in> set [1,2,3]. P x"                        \<comment> \<open>True\<close>

value "foldr (\<lambda>x b. P x \<and> b) [1,0,3] False"          \<comment> \<open>False\<close>
value "\<forall>x \<in> set [1,0,3]. P x"


subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>pick 0 xs = []\<close> |
  \<open>pick (Suc n) xs = (case xs of [] \<Rightarrow> [] | x # xs' \<Rightarrow> x # pick n xs')\<close>

value "pick 3 ''hello''"     \<comment> \<open>"hel"\<close>
value "pick 1 ''hi''"       \<comment> \<open>"hi"\<close>
value "pick 0 ''anything''"  \<comment> \<open>""\<close>

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induct n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    then have "pick (Suc n) xs = x # pick n xs'" by simp
    hence "length (pick (Suc n) xs) = Suc (length (pick n xs'))" by simp
    also have "... = Suc (min n (length xs'))" 
      using Suc.hyps[of xs'] by simp
    also have "min (Suc n) (length xs) = Suc (min n (length xs'))"
      using Cons by simp
    finally show ?thesis using Cons by simp
  qed
qed

value "length (pick 3 ''hello'') = min 3 (length (''hello''))"   \<comment> \<open>True\<close>
value "length (pick 7 ''hi'') = min 7 (length (''hi''))"      \<comment> \<open>True\<close>
value "length (pick 0 ''abc'') = min 0 (length (''abc''))"     \<comment> \<open>True\<close>

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
proof (induct n arbitrary: xs)
  case 0
  show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    have pick_eq: "pick (Suc n) xs = x # pick n xs'" using Cons by simp
    hence len_eq: "length (pick (Suc n) xs) = Suc (length (pick n xs'))" by simp
    show ?thesis
    proof (rule allI, rule impI)
      fix i assume "i < length (pick (Suc n) xs)"
      then have "i < Suc (length (pick n xs'))" using len_eq by simp
      then show "(pick (Suc n) xs) ! i = xs ! i"
      proof (cases i)
        case 0
        then show ?thesis using pick_eq Cons by simp
      next
        case (Suc j)
        then have "j < length (pick n xs')" using \<open>i < Suc _\<close> by simp
        hence "pick n xs' ! j = xs' ! j" using Suc.hyps[of xs'] by blast
        then show ?thesis using pick_eq Cons Suc by simp
      qed
    qed
  qed
qed

value "pick 3 ''hello'' ! 1"     \<comment> \<open>''e''\<close>
value "''hello'' ! 1"            \<comment> \<open>''e''\<close>
value "pick 4 ''hi'' ! 0"     \<comment> \<open>''h''\<close>
value "''hi'' ! 0"            \<comment> \<open>''h''\<close>
value "pick 4 ''hi'' ! 1"     \<comment> \<open>''i''\<close>
value "''hi'' ! 1"            \<comment> \<open>''i''\<close>


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
proof (induct ys arbitrary: xs)
  case Nil
  show ?case by (simp add: conss.simps)
next
  case (Cons y ys)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by (simp add: conss_Cons)
  next
    case (Cons z zs)
    have step: "conss xs (y # ys) = (z # y) # conss zs ys"
      using Cons by (subst conss_Cons) simp
    hence len: "length (conss xs (y # ys)) = Suc (length (conss zs ys))"
      by simp
    also have "length (conss zs ys) = min (length zs) (length ys)"
      using Cons.hyps[of zs] by blast
    hence "Suc (length (conss zs ys)) = Suc (min (length zs) (length ys))"
      by simp
    also have "Suc (min (length zs) (length ys)) = min (Suc (length zs)) (Suc (length ys))"
      by (metis min_Suc_Suc)
    also have "Suc (length zs) = length xs"
      using Cons by simp
    also have "Suc (length ys) = length (y # ys)"
      by simp
    finally show ?thesis .
  qed
qed

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
proof -
  have "conss (x # xs) (y # ys)
      = (case (x # xs) of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z # y) # conss zs ys)"
    by (subst conss.simps(2)) simp
  also have "... = (x # y) # conss xs ys"
    by simp
  finally show ?thesis .
qed

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
proof (induct xs)
  case Nil
  show ?case by (simp add: conss_Nil)
next
  case (Cons y ys)
  obtain z zs where "y = z # zs" using Cons.prems by (cases y) auto
  moreover have "\<forall>x \<in> set ys. x \<noteq> []" using Cons.prems by simp
  ultimately show ?case
    by (auto simp: conss_Cons_Cons Cons.hyps)
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
  case (Cons a s)
  show ?case
  proof (cases "a = [] \<or> \<not> P a")
    case True
    hence "filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s) =
           filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s" by simp
    moreover have
      "map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s))
       = map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s)"
      using True by simp
    moreover have
      "map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s))
       = map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s)"
      using True by simp
    ultimately show ?thesis
      by (simp add: Cons.IH)
  next
    case False
    hence A: "a \<noteq> []" and B: "P a" by auto
    have F: "filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s)
            = a # filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s"
      using A B by simp
    hence "map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s))
          = hd a # map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s)"
      by simp
    moreover from F have
      "map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s))
       = tl a # map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s)"
      by simp
    ultimately have
      "conss (map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s)))
              (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s)))
       = (hd a # tl a) # conss (map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
                               (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))"
      by simp
    also have "... = (hd a # tl a) #
          filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s"
      by (simp add: Cons.IH)
    also have "... = filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s)"
      using F A by simp
    finally show ?thesis .
  qed
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
proof -
  assume A: "xs \<noteq> []" and B: "hd xs # ys \<noteq> xs"
  show "tl xs \<noteq> ys"
  proof (cases xs)
    case Nil
    then show ?thesis using A by simp
  next
    case (Cons a as)
    with B have "a # ys \<noteq> a # as" by simp
    hence "ys \<noteq> as" by simp
    thus ?thesis using Cons by simp
  qed
qed

lemma filter_nil: "filter P [] = []" by simp
lemma filter_cons: "filter P (x # xs) = (if P x then x # filter P xs else filter P xs)" by simp
lemma map_nil: "map f [] = []" by simp
lemma map_cons: "map f (x # xs) = f x # map f xs" by simp
lemma hd_cons: "hd (x # xs) = x" by simp
lemma tl_cons: "tl (x # xs) = xs" by simp
lemma map_tl_filter_empty [simp]: "map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) []) = []" by simp
lemma map_tl_filter_cons_eq [simp]: "a \<noteq> [] \<Longrightarrow> (\<lambda>xs. xs \<noteq> [] \<and> P xs) a \<Longrightarrow> map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) (a # s)) = tl a # map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s)" by simp
lemma hd_tl_eq: "x # xs = y # ys \<longleftrightarrow> x = y \<and> xs = ys" by simp

lemma mem_map_tl_filter:
  "xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s)) \<longleftrightarrow>
   (\<exists>ys \<in> set s. ys \<noteq> [] \<and> hd ys = x \<and> tl ys = xs)"
  by (induct s) (auto simp: filter_cons map_cons tl_cons)

lemma map_tl_filter_eq_image:
  "set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s)) = tl ` {ys \<in> set s. ys \<noteq> [] \<and> hd ys = x}"
proof -
  have "set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s)) = 
        {tl ys | ys. ys \<in> set s \<and> ys \<noteq> [] \<and> hd ys = x}" by auto
  also have "... = tl ` {ys \<in> set s. ys \<noteq> [] \<and> hd ys = x}" by auto
  finally show ?thesis .
qed

lemma filter_cons_hd:
  "a \<noteq> [] \<Longrightarrow> (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) a \<Longrightarrow>
   filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (a # s) = a # filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s"
  by simp

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof
  assume "x # xs \<in> set s"
  then obtain ys where "ys = x # xs" "ys \<in> set s" by blast
  then show "xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s))"
    using mem_map_tl_filter by blast
next
  assume "xs \<in> set (map tl (filter (\<lambda>ys. ys \<noteq> [] \<and> hd ys = x) s))"
  then obtain ys where "ys \<in> set s \<and> ys \<noteq> [] \<and> hd ys = x \<and> tl ys = xs"
    using map_tl_filter_eq_image by auto
  then show "x # xs \<in> set s" by auto
qed
end