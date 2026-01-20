theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume Prem: "(foldr (\<lambda> x b. P x \<and> b) (a # xs) y)"
  assume IH: "(\<And>y. foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow>y)"
  from Prem have "(foldr (\<lambda> x b. P x \<and> b) xs y)" by simp
  with IH show ?case by blast
qed

\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof 
  assume Prem1:"foldr (\<lambda>x. (\<and>) (P x)) xs True"
  thus "\<forall>x\<in>set xs. P x"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case using Prem1 by simp
  qed
next
  assume Prem1:"\<forall>x\<in>set xs. P x"
  thus "foldr (\<lambda>x. (\<and>) (P x)) xs True"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case using Prem1 by simp
  qed
qed


subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
	\<open>pick 0 xs = []\<close> |
	\<open>pick (Suc n) xs = (case xs of 
                        Nil \<Rightarrow> [] |
                        Cons x xss \<Rightarrow> x # (pick n xss))\<close>

lemma pick_empty_list: "(pick n []) = []"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma pick_split: "pick (Suc n) (x # xs) = x # pick n xs"
  by simp

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>

lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume P1:"\<And>xs. length (pick n xs) = min n (length xs)"
  then show ?case
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    assume P2:"(\<And>xs. length (pick n xs) =
               min n (length xs)) \<Longrightarrow>
        length (pick (Suc n) xs) =
        min (Suc n) (length xs)"
    assume P3:"(\<And>xs. length (pick n xs) =
              min n (length xs))"
    have "length (pick (Suc n) (a # xs)) = Suc (length (pick n xs))" using pick_split by simp
    then have "length (pick (Suc n) (a # xs)) = Suc (min n (length xs))" using P3 Suc by simp
    then have "length (pick (Suc n) (a # xs)) = min (Suc n) (Suc (length xs))" by simp
    then show ?case by simp
  qed
qed

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
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
    case (Cons a xss)
    assume P1:"(\<And>xs. \<forall>i<length (pick n xs).pick n xs ! i = xs ! i)"
    assume P2:"xs = a # xss"
      (*\<forall>i<length (pick (Suc n) xs).pick (Suc n) xs ! i = xs ! i*)
    have s1:"length (pick (Suc n) xs) = Suc (length (pick n xss))" using pick_split P2 by simp
    have s3:"\<forall>i<length (pick (Suc n) xs).pick (Suc n) xs ! i = xs ! i \<equiv> \<forall>i<Suc (length (pick n xss)).pick (Suc n) xs ! i = xs ! i" using s1 by simp
    have s4:"(\<forall>i<Suc (length (pick n xss)).pick (Suc n) xs ! i = xs ! i) =
          ((pick (Suc n) xs ! 0 = xs ! 0)\<and>(\<forall>i<length (pick n xss).pick (Suc n) xs ! (Suc i) = xs ! (Suc i)))" using All_less_Suc2 by simp
    have s5:"(pick (Suc n) xs ! 0 = xs ! 0)" using P2 by simp
    have s6:"(\<forall>i<length (pick n xss).pick (Suc n) xs ! (Suc i) = xs ! (Suc i))" using P2 Suc.IH by simp 
    then show ?thesis using s3 s4 s5 s6 by simp
  qed
qed

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

lemma conss_split:"conss (x#xs) (y#ys) = (x#y)# conss xs ys" by simp

\<comment> \<open>The length of @{term \<open>conss xs ys\<close>} is the minimum length of @{term xs} and @{term ys}.\<close>
lemma conss_length: \<open>length (conss xs ys) = min (length xs) (length ys)\<close>
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons y yss)
  assume P1:"\<And>xs. length (conss xs yss) = min (length xs) (length yss)"
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a xss)
    assume P2:"xs = a # xss"
      (*length (conss xs (y # yss)) = min (length xs) (length (y # yss))*)
    have s1:"length (conss (a # xss) (y # yss)) = 1 + length (conss xss yss)" using conss_split by simp 
    show ?thesis using P1 P2 s1 by simp
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
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
proof(induction s)
  case Nil
  then show ?case by simp
next
  case (Cons a s)
  then show ?case by simp
qed

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
	sorry

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
proof
  show "x # xs \<in> set s \<Longrightarrow>xs \<in> set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))"
  proof (induction s)
    case Nil
    then show ?case by simp
  next
    case (Cons a s)
    assume P1:"x # xs \<in> set (a # s)"
    assume P2:"(x # xs \<in> set s \<Longrightarrow>xs \<in> set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)))"
    (* xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (a # s)))*)
    show ?case 
    proof (cases "x#xs \<in> set s")
      case True
      then show ?thesis using P2 by simp
    next
      case False
      then have s1:"a= (x # xs)" using P1 by simp
      then have s2:"a \<noteq> []" by blast 
      have s3:"hd a = x" using s1 by simp
      have s5:"a \<noteq> [] \<and> hd a = x" using s2 s3 s1 by simp
      then have "(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x)(a # s)) = a#(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)" by simp
      then have "set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x)(a # s))) = (set (map tl (a#(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))))" by simp
      then have "... = set ((tl a) # (map tl (filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)))" by simp
      then have "... = set (xs # (map tl (filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)))" using s1 by simp
      then show ?thesis using s1 by simp
    qed
  qed
next
  show "xs \<in> set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)) \<Longrightarrow> x # xs \<in> set s"
  proof (induction s)
    case Nil
    then show ?case by simp
  next
    case (Cons a s)
    assume P1:"(xs \<in> set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)) \<Longrightarrow>x # xs \<in> set s)"
    assume P2:"xs \<in> set (map tl(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (a # s)))"
    (*x # xs \<in> set (a # s)*)
    then show ?case
    proof (cases "a \<noteq> [] \<and> hd a = x")
      case True
      assume P3:"a \<noteq> [] \<and> hd a = x"
      then have s1:"xs \<in> set ((tl a) # (map tl (filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)))" using P2 by simp
      then show ?thesis
      proof (cases "xs \<in> set [(tl a)]")
        case True
        then have "tl a = xs" by simp
        then have "x#xs =a" using P3 hd_Cons_tl by blast
        then show ?thesis by simp
      next
        case False
        then have "xs\<in>set (map tl (filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))" using s1 by simp
        then have "x # xs \<in> set s" using P1 by simp
        then show ?thesis by simp
      qed
    next
      case False
      then have "(filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) (a # s)) = (filter(\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s)" by simp
      then show ?thesis using P1 P2 by simp
    qed
  qed
qed


end