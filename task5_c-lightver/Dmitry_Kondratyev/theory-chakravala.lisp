(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/typed-lists/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

(defrule lemma
    (implies
        (and
            (integerp
                m
            )
            (integerp
                i
            )
            (equal
                (+
                    m
                    i
                    (-
                        (*
                            k
                            (floor
                                (+
                                    m
                                    i
                                )
                                k
                            )
                        )
                    )
                )
                0
            )
        )
        (integerp
            (/
                (+
                    i
                    m
                )
                k
            )            
        )
    )
    :rule-classes nil
)

(defund floor-rational (i j)
    (LET* ((Q (* I (/ J)))
              (N (NUMERATOR Q))
              (D (DENOMINATOR Q)))
             (COND ((EQUAL D 1) N)
                   ((< N 0)
                    (+ (- (NONNEGATIVE-INTEGER-QUOTIENT (- N) D))
                       -1))
                   (T (NONNEGATIVE-INTEGER-QUOTIENT N D)))
    )
)

(defrule lemma-0
    (=
        (floor i j)
        (floor-rational i j)
    )
    :rule-classes nil
    :use
    (
        (:definition floor)
        (:definition floor-rational)
    )
)

(defrule lemma-1
    (=
        (floor i j)
        (if
            (integerp
                (/
                    i
                    j
                )
            )
            (/
                i
                j
            )
            (floor-rational
                i
                j
            )
         )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        (:definition floor)
        (:definition floor-rational)
    )
)

(defruled lemma-floor-0
    (=
        (floor-rational i j)
        (LET* ((Q (* I (/ J)))
              (N (NUMERATOR Q))
              (D (DENOMINATOR Q)))
             (COND ((EQUAL D 1) N)
                   ((< N 0)
                    (+ (- (NONNEGATIVE-INTEGER-QUOTIENT (- N) D))
                       -1))
                   (T (NONNEGATIVE-INTEGER-QUOTIENT N D)))
    )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        (:definition floor-rational)
    )
)

(defrule lemma-floor
    (implies
        (integerp i)
        (=
            (floor-rational
                i
                1
            )
            i
        )
    )
    :rule-classes ((:rewrite :match-free :all))
    :enable
    (
        lemma-floor-0
    )
)

(defrule lemma-2
    (implies
        (and
            (integerp
                m
            )
            (integerp
                i
            )
            (equal
                (+
                    m
                    i
                    (-
                        (*
                            k
                            (floor-rational
                                (+
                                    m
                                    i
                                )
                                k
                            )
                        )
                    )
                )
                0
            )
        )
        (integerp
            (/
                (+
                    i
                    m
                )
                k
            )            
        )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        (:instance
            lemma
        )
        (:instance
            lemma-0
        )
    )
)

(defrule lemma-3
    (=
        (+
            (*
                i
                k
            )
            (*
                m
                k
            )
        )
        (*
            (+
                i
                m
            )
            k
        )
    )
    :rule-classes nil
)

(defrule lemma-4
    (=
        (+
            (*
                a
                i
                k
            )
            (*
                a
                m
                k
            )
        )
        (*
            a
            (+
                i
                m
            )
            k
        )
    )
    :rule-classes nil
)

(defrule lemma-5
    (implies
        (and
            (integerp
                a
            )
            (integerp
                (+
                    (*
                        i
                        k
                    )
                    (*
                        m
                        k
                    )
                )
            )
        )
        (integerp
            (+
                (*
                    a
                    i
                    k
                )
                (*
                    a
                    m
                    k
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        lemma-3
        lemma-4
    )
)

(defrule lemma-6
    (=
        (+
            (-
                (*
                    n
                    k
                )
            )
            (*
                (expt m 2)
                k
            )
        )
        (*
            (-
                (expt m 2)
                n
            )
            k
        )                
    )
    :rule-classes nil
)

(defruled lemma-7
    (=
        (+
            (-
                (*
                    n
                    k
                )
            )
            (*
                (expt i 2)
                k
            )
        )
        (*
            (-
                (expt i 2)
                n
            )
            k
        )                
    )
    :rule-classes ((:rewrite :match-free :all))
)

(defrule lemma-8
    (implies
        (integerp
            n
        )
        (=
            (*
                (-
                    (expt i 2)
                    n
                )
                k
            )
            (*
                (+
                    (expt i 2)
                    (expt m 2)
                    (-
                        (expt m 2)
                    )
                    (-
                        n
                    )
                )
                k
            )
        )
    )
    :rule-classes nil
)

(defrule lemma-9
    (=
        (*
            (+
                (expt i 2)
                (expt m 2)
                (-
                    (expt m 2)
                )
                (-
                    n
                )
            )
            k
        )
        (+
            (*
                (-
                    (expt i 2)
                    (expt m 2)
                )
                k
            )
            (*
                (-
                    (expt m 2)
                    n
                )
                k
            )
        )        
    )
    :rule-classes nil
)

(defrule lemma-10
    (=
        (+
            (*
                (-
                    (expt i 2)
                    (expt m 2)
                )
                k
            )
            (*
                (-
                    (expt m 2)
                    n
                )
                k
            )
        )
        (+
            (*
                (-
                    i
                    m
                )
                (*
                    (+
                        i
                        m
                    )
                    k
                )
            )
            (*
                (-
                    (expt m 2)
                    n
                )
                k
            )
        )        
    )
    :rule-classes nil
)

(defrule lemma-11
    (implies
        (integerp
            n
        )
        (=
            (+
                (-
                    (*
                        n
                        k
                    )
                )
                (*
                    (expt i 2)
                    k
                )
            )
            (+
                (*
                    (-
                        i
                        m
                    )
                    (*
                        (+
                            i
                            m
                        )
                        k
                    )
                )
                (*
                    (-
                        (expt m 2)
                        n
                    )
                    k
                )
            )        
        )
    )
    :rule-classes nil
    :use
    (
        lemma-7
        lemma-8
        lemma-9
        lemma-10
    )
)

(defrule lemma-12
    (implies
        (integerp
            (+
                (*
                    i
                    k
                )
                (*
                    m
                    k
                )
            )
        )
        (integerp
            (*
                (+
                    i
                    m
                )
                k
            )
        )
    )
    :rule-classes nil
    :use
    (
        lemma-3
    )
)

(defrule lemma-13
    (implies
        (integerp
            (+
                (-
                    (*
                        n
                        k
                    )
                )
                (*
                    (expt m 2)
                    k
                )
            )
        )
        (integerp
            (*
                (-
                    (expt m 2)
                    n
                )
                k
            )
        )        
    )
    :rule-classes nil
    :use
    (
        lemma-6
    )
)

(defrule lemma-14
    (implies
        (integerp
            n
        )
        (=
            (integerp
                (+
                    (-
                        (*
                            n
                            k
                        )
                    )
                    (*
                        (expt i 2)
                        k
                    )
                )
            )
            (integerp
                (+
                    (*
                        (-
                            i
                            m
                        )
                        (*
                            (+
                                i
                                m
                            )
                            k
                        )
                    )
                    (*
                        (-
                            (expt m 2)
                            n
                        )
                        k
                    )
                )
            )            
        )
    )
    :rule-classes nil
    :use
    (
        lemma-11
    )
)

(defrule lemma-15
    (implies
        (and
            (integerp
                m
            )
            (integerp
                i
            )
            (integerp
                (*
                    (+
                        i
                        m
                    )
                    k
                )
            )
            (integerp
                (*
                    (-
                        (expt m 2)
                        n
                    )
                    k
                )
            )
        )
        (integerp
            (+
                (*
                    (-
                        i
                        m
                    )
                    (*
                        (+
                            i
                            m
                        )
                        k
                    )
                )
                (*
                    (-
                        (expt m 2)
                        n
                    )
                    k
                )
            )
        )
    )
    :rule-classes nil
)

(defrule lemma-16
    (implies
        (and
            (integerp
                m
            )
            (integerp
                i
            )
            (integerp
                n
            )
            (integerp
                (*
                    (+
                        i
                        m
                    )
                    k
                )
            )
            (integerp
                (*
                    (-
                        (expt m 2)
                        n
                    )
                    k
                )
            )
        )
        (integerp
            (+
                (-
                    (*
                        n
                        k
                    )
                )
                (*
                    (expt i 2)
                    k
                )
            )
        )
    )
    :rule-classes nil
    :use
    (
        lemma-14
        lemma-15
    )
)

(defrule lemma-17
    (implies
        (and
            (integerp
                m
            )
            (integerp
                i
            )
            (integerp
                n
            )
            (integerp
                (+
                    (-
                        (*
                            n
                            k
                        )
                    )
                    (*
                        (expt m 2)
                        k
                    )
                )
            )
            (integerp
                (+
                    (*
                        i
                        k
                    )
                    (*
                        m
                        k
                    )
                )
            )
        )
        (integerp
            (+
                (-
                    (*
                        n
                        k
                    )
                )
                (*
                    (expt i 2)
                    k
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        lemma-12
        lemma-13
        lemma-16
    )
)

(defrule lemma-18
    (=
        (+
            (-
                (*
                    n
                    (/
                        (+
                            (-
                                (*
                                    n
                                    k
                                )
                            )
                            (*
                                (expt i 2)
                                k
                            )
                        )
                    )
                )
            )
            (*
                (expt i 2)
                (/
                    (+
                        (-
                            (*
                                n
                                k
                            )
                        )
                        (*
                            (expt i 2)
                            k
                        )
                    )
                )
            )
        )
        (*
            (-
                (expt i 2)
                n
            )
            (/
                (+
                    (-
                        (*
                            n
                            k
                        )
                    )
                    (*
                        (expt i 2)
                        k
                    )
                )
            )
        )
    )
    :rule-classes nil
    :use
    (
        (:instance
            lemma-7
            (k
                (/
                    (+
                        (-
                            (*
                                n
                                k
                            )
                        )
                        (*
                            (expt i 2)
                            k
                        )
                    )
                )                
            )
        )
    )
)

(defrule lemma-19
    (=
        (*
            (-
                (expt i 2)
                n
            )
            (/
                (+
                    (-
                        (*
                            n
                            k
                        )
                    )
                    (*
                        (expt i 2)
                        k
                    )
                )
            )
        )
        (*
            (-
                (expt i 2)
                n
            )
            (/
                (*
                    (-
                        (expt i 2)
                        n
                    )
                    k
                )
            )
        )
    )
    :rule-classes nil
    :enable
    (
        lemma-7
    )
)

(defrule lemma-20
    (=
        (+
            (-
                (*
                    n
                    (/
                        (+
                            (-
                                (*
                                    n
                                    k
                                )
                            )
                            (*
                                (expt i 2)
                                k
                            )
                        )
                    )
                )
            )
            (*
                (expt i 2)
                (/
                    (+
                        (-
                            (*
                                n
                                k
                            )
                        )
                        (*
                            (expt i 2)
                            k
                        )
                    )
                )
            )
        )
        (*
            (-
                (expt i 2)
                n
            )
            (/
                (*
                    (-
                        (expt i 2)
                        n
                    )
                    k
                )
            )
        )
    )
    :rule-classes nil
    :use
    (
        lemma-18
        lemma-19
    )
)

(defrule lemma-21
    (=
        (*
            e
            (/
                (*
                    e
                    k
                )
            )
        )
        (*
            (/
                e
                e
            )
            (/
                k
            )
        )            
    )
    :rule-classes nil
)

(defrule lemma-22
    (implies
        (and
            (integerp
                e
            )
            (not
                (equal
                    e
                    0
                )
            )
        )
        (=
            (/
                e
                e
            )
            1        
        )
    )
    :rule-classes nil
)

(defrule lemma-23
    (implies
        (and
            (integerp
                e
            )
            (not
                (equal
                    e
                    0
                )
            )
        )
        (=
            (*
                (/
                    e
                    e
                )
                (/
                    k
                )
            )
            (/
                k
            )        
        )
    )
    :rule-classes nil
    :use
    (
        lemma-22
    )
)

(defrule lemma-24
    (implies
        (and
            (integerp
                e
            )
            (not
                (equal
                    e
                    0
                )
            )
        )
        (=
            (*
                e
                (/
                    (*
                        e
                        k
                    )
                )
            )
            (/
                k
            )            
        )
    )
    :rule-classes nil
    :use
    (
        lemma-21
        lemma-23
    )
)

(defrule lemma-25
    (implies
        (and
            (integerp
                n
            )
            (not
                (equal
                    (-
                        (expt i 2)
                        n
                    )
                    0
                )
            )
        )
        (=
            (*
                (-
                    (expt i 2)
                    n
                )
                (/
                    (*
                        (-
                            (expt i 2)
                            n
                        )
                        k
                    )
                )
            )
            (/
                k
            )            
        )
    )
    :rule-classes nil
    :use
    (
        (:instance
            lemma-24
            (
                e
                (-
                    (expt i 2)
                    n
                )
            )
        )
    )
)

(defrule lemma-26
    (implies
        (and
            (integerp
                n
            )
            (not
                (equal
                    (-
                        (expt i 2)
                        n
                    )
                    0
                )
            )
        )
        (=
            (+
                (-
                    (*
                         n
                        (/
                            (+
                                (-
                                    (*
                                        n
                                        k
                                    )
                                )
                                (*
                                    (expt i 2)
                                    k
                                )
                            )
                        )
                    )
                )
                (*
                    (expt i 2)
                    (/
                        (+
                            (-
                                (*
                                    n
                                    k
                                )
                            )
                            (*
                                (expt i 2)
                                k
                            )
                        )
                    )
                )
            )
            (/
                k
            )
        )
    )
    :rule-classes nil
    :use
    (
        lemma-20
        lemma-25
    )
)

(defrule lemma-27
    (implies
        (and
            (integerp
                n
            )
            (not
                (equal
                    (-
                        (expt i 2)
                        n
                    )
                    0
                )
            )
        )
        (=
            (integerp
                (+
                    (-
                        (*
                            n
                            (/
                                (+
                                    (-
                                        (*
                                            n
                                            k
                                        )
                                    )
                                    (*
                                        (expt i 2)
                                        k
                                    )
                                )
                            )
                        )
                    )
                    (*
                        (expt i 2)
                        (/
                            (+
                                (-
                                    (*
                                        n
                                        k
                                    )
                                )
                                (*
                                    (expt i 2)
                                    k
                                )
                            )
                        )
                    )
                )
            )
            (integerp
                (/
                    k
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
    :use
    (
        lemma-26
    )
)

(defruled lemma-28
    (=
        (=	
	        (+
			    m
				p
                (*
                    n
					b
                    k
                )
			)
            (*
                a
                k
            )
        )
		(=
            (+
                m
                p
                (-
				    (*
						(+
						    a
							(-
							    (*
								    n
								    b
							    )
							)
						)
						k
					)
				)
            )
            0
        )
    )
    :rule-classes ((:rewrite :match-free :all))
)

(defruled lemma-29
    (=
        (=	
	        (+
			    m
				p
                (*
                    n
					b
                    (floor
					    (+
						    m
							p
						)
						(+
						    a
							(-
							    (*
								    n
								    b
							    )
							)
						)						
					)
                )
			)
            (*
                a
                (floor
					(+
						m
						p
			        )
					(+
						a
						(-
							(*
								n
								b
							)
						)
					)						
			    )
            )
        )
		(=
            (+
                m
                p
                (-
				    (*
						(+
						    a
							(-
							    (*
								    n
								    b
							    )
							)
						)
                        (floor
					        (+
						        m
							    p
						    )
						    (+
						        a
							    (-
							        (*
								        n
								        b
							        )
							    )
						    )						
					    )
					)
				)
            )
            0
        )
    )
    :rule-classes ((:rewrite :match-free :all))
	:enable
	(
	    lemma-28
	)
)

(defruled lemma-30
    (implies
	    (and
		    (integerp
			    m
			)
		    (integerp
			    p
			)
            (=	
	            (+
			        m
				    p
                    (*
                        n
					    b
                        (floor
					        (+
						        m
							    p
						    )
						    (+
						        a
							    (-
							        (*
								        n
								        b
							        )
							    )
						    )				
					    )
                    )
			    )
                (*
                    a
                    (floor
					    (+
						    m
						    p
			            )
					    (+
						    a
						    (-
							    (*
								    n
								    b
							    )
						    )
					    )				
			        )
                )
			)
        )
		(integerp
            (/
			    (+
                    m
                    p
				)
				(+
				    a
					(-
						(*
						    n
							b
						)
					)
				)
		    )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
	:enable
	(
	    lemma-29
	)
	:use
	(
	    (:instance
		    lemma-2
			(
			    i
				p
			)
			(
			    k
			    (+
				    a
					(-
						(*
							n
							b
						)
					)
			    )				
			)
		)
	)
)

(defruled lemma-31
    (=
        (/
			(+
                m
                p
		    )
		    (+
				a
		        (-
					(*
						n
						b
					)
			    )
		    )
		)
        (+
            (*
                m
				(/
		            (+
				        a
		                (-
					        (*
						        n
						        b
					        )
			            )
		            )
				)
            )
            (*
                p
				(/
		            (+
				        a
		                (-
					        (*
						        n
						        b
					        )
			            )
		            )
				)
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
)

(defruled lemma-32
    (implies
	    (and
		    (integerp
			    m
			)
		    (integerp
			    p
			)
            (=	
	            (+
			        m
				    p
                    (*
                        n
					    b
                        (floor
					        (+
						        m
							    p
						    )
						    (+
						        a
							    (-
							        (*
								        n
								        b
							        )
							    )
						    )				
					    )
                    )
			    )
                (*
                    a
                    (floor
					    (+
						    m
						    p
			            )
					    (+
						    a
						    (-
							    (*
								    n
								    b
							    )
						    )
					    )				
			        )
                )
			)
        )
		(integerp
            (+
                (*
                    m
				    (/
		                (+
				            a
		                    (-
					            (*
						            n
						            b
					            )
			                )
		                )
				    )
                )
                (*
                    p
				    (/
		                (+
				            a
		                    (-
					            (*
						            n
						            b
					            )
			                )
		                )
				    )
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-30
		lemma-31
	)
)

(defruled lemma-33
    (implies
	    (and
		    (integerp
			    m
			)
		    (integerp
			    p
			)
            (=	
	            (+
			        m
				    p
                    (*
                        n
					    b
                        (floor-rational
					        (+
						        m
							    p
						    )
						    (+
						        a
							    (-
							        (*
								        n
								        b
							        )
							    )
						    )				
					    )
                    )
			    )
                (*
                    a
                    (floor-rational
					    (+
						    m
						    p
			            )
					    (+
						    a
						    (-
							    (*
								    n
								    b
							    )
						    )
					    )				
			        )
                )
			)
        )
		(integerp
            (+
                (*
                    m
				    (/
		                (+
				            a
		                    (-
					            (*
						            n
						            b
					            )
			                )
		                )
				    )
                )
                (*
                    p
				    (/
		                (+
				            a
		                    (-
					            (*
						            n
						            b
					            )
			                )
		                )
				    )
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-0
		lemma-32
	)
)

(defrule lemma-34
    (implies
	    (and
		    (integerp
			    m
			)
		    (integerp
			    p
			)
            (=	
	            (+
			        m
				    p
                    (*
                        n
					    (expt b 2)
                        (floor-rational
					        (+
						        m
							    p
						    )
						    (+
						        (expt a 2)
							    (-
							        (*
								        n
								        (expt b 2)
							        )
							    )
						    )				
					    )
                    )
			    )
                (*
                    (expt a 2)
                    (floor-rational
					    (+
						    m
						    p
			            )
					    (+
						    (expt a 2)
						    (-
							    (*
								    n
								    (expt b 2)
							    )
						    )
					    )				
			        )
                )
			)
        )
		(integerp
            (+
                (*
                    m
				    (/
		                (+
				            (expt a 2)
		                    (-
					            (*
						            n
						            (expt b 2)
					            )
			                )
		                )
				    )
                )
                (*
                    p
				    (/
		                (+
				            (expt a 2)
		                    (-
					            (*
						            n
						            (expt b 2)
					            )
			                )
		                )
				    )
                )
            )
        )
    )
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-33
			(a (expt a 2))
			(b (expt b 2))
		)
	)
)

(defruled lemma-35
	(=
		(+
			(-
				(*
					a
					(/
						k
					)
				)
			)
			(*
				b
				(/
					k
				)
			)
		)
		(*
			(/
				k
			)
			(+
				(-
					a
				)
				b
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
)

(defruled lemma-36
	(=
		(/
			(+
				(-
					(*
						a
						(/
							k
						)
					)
				)
				(*
					b
					(/
						k
					)
				)
			)
		)
		(*
			k
			(/	
				(+
					(-
						a
					)
					b
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
    :enable
	(
	    lemma-35
	)
)

(defruled lemma-aux-36
	(=
	    (*
		    h
			i
			(/
				(+
					(-
						(*
							a
							(/
								k
							)
						)
					)
					(*
						b
						(/
							k
						)
					)
				)
			)
		)
		(*
		    h
			i
			k
			(/	
				(+
					(-
						a
					)
					b
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
    :use
	(
	    lemma-36
	)
)

(defrule lemma-37
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
				(/
					k
				)
				(/
					(+
						(-
							(*
								a
								(/
									k
								)
							)
						)
						(*
							b
							(/
								k
							)
						)
					)
				)
			)
			(/
				(+
					(-
						a
					)
					b
				)
			)
		)
	)
    :rule-classes nil
	:enable
	(
	    lemma-36
	)
)

(defrule lemma-38
    (implies
	    (and
	        (integerp
		        k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
				(/
					k
				)
				(/
					(+
						(-
							(*
								a
								(/
									k
								)
							)
						)
						(*
							b
							(/
								k
							)
						)
					)
				)
			)
			(/
				(+
					(-
						a
					)
					b
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-37
	)
)

(defrule lemma-39
    (implies
	    (and
	        (integerp
		        k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
			    c
				(/
					k
				)
				(/
					(+
						(-
							(*
								a
								(/
									k
								)
							)
						)
						(*
							b
							(/
								k
							)
						)
					)
				)
			)
			(*
			    c
			    (/
				    (+
					    (-
						     a
					    )
					    b
				    )
			    )
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-38
	)
)

(defrule lemma-40
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
			    c
				d
				(/
					k
				)
				(/
					(+
						(-
							(*
								a
								(/
									k
								)
							)
						)
						(*
							b
							(/
								k
							)
						)
					)
				)
			)
			(*
			    c
				d
			    (/
				    (+
					    (-
						    a
					    )
					    b
				    )
			    )
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-38
	)
)

(defrule lemma-41
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			h
			(+
			    (*
				    a
					m
					(/
					    k
					)
				)
			    (-
					(*
						b
						n
						(/
						    k
						)
					)
				)
			)
		)
	)
    :rule-classes nil
)

(defruled lemma-41-aux
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(+
			    (*
				    a
					m
					(/
					    k
					)
				)
			    (-
					(*
						b
						n
						(/
						    k
						)
					)
				)
			)
			h
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-41
	)
)

(defrule lemma-42
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(+
			    (*
				    a
					m
					(/
					    k
					)
				)
			    (-
					(*
						b
						n
						(/
						    k
						)
					)
				)
			)
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-43
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			h
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-41
		lemma-42
	)
)

(defrule lemma-44-aux
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				i
				z
			)
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				i
				z				
			)
		)
	)
    :rule-classes nil
	:use
	(
		lemma-43
	)
)

(defrule lemma-44
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				i
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				i
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)				
			)
		)
	)
    :rule-classes nil
	:use
	(
		(:instance
		    lemma-44-aux
			(
			    z
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
		)
	)
)

(defruled lemma-45
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				i
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				i
				(*
					k
					(/
						(+
							(-
								(*
									x
								)
							)
							(*
								y
							)
						)
					)
				)				
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
		lemma-44
		(:instance
		    lemma-36
			(
			    a
				x
			)
			(
			    b
				y
			)
		)
	)
)

(defruled lemma-46
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
				(/
					k
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				i
				(*
					k
					(/
						(+
							(-
								(*
									x
								)
							)
							(*
								y
							)
						)
					)
				)				
			)
			(*
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				i
				(/
					(+
						(-
							(*
								x
							)
						)
						(*
							y
						)
					)
				)				
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
)

(defrule lemma-47
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				i
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
				(+
					(*
						a
						m
				    )
					(-
					    (*
					        b
						    n
					    )
					)
				)
				i
				(/	
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-45
	    lemma-46
	)
)

(defrule lemma-48
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			v
			(+
			    (*
				    b
					m
					(/
					    k
					)
				)
			    (-
					(*
						a
						(/
						    k
						)
					)
				)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-49
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(+
			    (*
				    b
					m
					(/
					    k
					)
				)
			    (-
					(*
						a
						(/
						    k
						)
					)
				)
			)
			(*
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-50
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			v
			(*
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-48
		lemma-49
	)
)

(defrule lemma-51-aux
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				n
				v
				z
			)
			(*
			    n
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
				z				
			)
		)
	)
    :rule-classes nil
	:use
	(
		lemma-50
	)
)

(defrule lemma-51
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				n
				v
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
			    n
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)				
			)
		)
	)
    :rule-classes nil
	:use
	(
		(:instance
		    lemma-51-aux
			(
			    z
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
		)
	)
)

(defruled lemma-52
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				n
				v
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
			    n
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
				(*
					k
					(/
						(+
							(-
								(*
									x
								)
							)
							(*
								y
							)
						)
					)
				)				
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
		lemma-51
		(:instance
		    lemma-36
			(
			    a
				x
			)
			(
			    b
				y
			)
		)
	)
)

(defruled lemma-53
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
		)
		(=
			(*
			    n
				(/
					k
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
				(*
					k
					(/
						(+
							(-
								(*
									x
								)
							)
							(*
								y
							)
						)
					)
				)				
			)
			(*
			    n
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
				(/
					(+
						(-
							(*
								x
							)
						)
						(*
							y
						)
					)
				)				
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
)

(defrule lemma-54
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				n
				v
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
			    n
				(+
					(*
						b
						m
				    )
					(-
					    a
					)
				)
				(/	
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-52
	    lemma-53
	)
)

(defrule lemma-55
	(=
	    (*
		    a
		    y
		)
		(+
			(-
			    (*
				    a
				    x
				)
			)
			(*
			    a
			    y
			)
			(*
			    a
			    x
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-56
	(=
	    (*
		    a
		    y
		)
		(+
		    (*
			    a
				(+
					(-
						x
					)
					y
				)
			)
			(*
			    a
			    x
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-55
	)
)

(defrule lemma-57
	(=
		(*
			(*
				a
				y
			)
			(/
				(+
					(-
						x
					)
					y
				)
			)
		)
		(*
			(+
				(*
					a
					(+
						(-
							x
						)
						y
					)
				)
				(*
					a
					x
				)
			)
			(/
				(+
					(-
						x
					)
					y
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-56
	)
)

(defrule lemma-58
    (=
		(*
			(+
				a
				b
			)
			c
		)
		(+
			(*
				a
				c
			)
			(*
			    b
				c
			)
		)
	)
	:rule-classes nil
)

(defrule lemma-59
	(=
		(*
			(+
				(+
					(-
						x
					)
					y
				)
				x
			)
			(/
				(+
					(-
						x
					)
					y
				)
			)
		)
		(+
			(*
				(+
					(-
						x
					)
					y
				)					
				(/
					(+
						(-
							x
						)
						y
					)
				)				
			)
			(*
				x
				(/
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)	
    :rule-classes nil
	:use
	(
	    (:instance
		    lemma-58
			(
			    a
				(+
					(-
						x
					)
					y
				)
			)
			(
			    b
				x
			)
			(
			    c
				(/
					(+
						(-
							x
						)
						y
					)
				)				
			)
		)
	)
)

(defrule lemma-60
	(=
		(*
			(+
			    (*
				    a
					(+
						(-
							x
						)
						y
					)
				)
				(*
				    a
				    x
				)
			)
			(/
				(+
					(-
						x
					)
					y
				)
			)
		)
		(+
			(*
			    a
				(+
					(-
						x
					)
					y
				)					
				(/
					(+
						(-
							x
						)
						y
					)
				)				
			)
			(*
			    a
				x
				(/
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)	
    :rule-classes nil
	:use
	(
	    (:instance
		    lemma-58
			(
			    a
				(*
				    a
					(+
						(-
							x
						)
						y
					)
				)
			)
			(
			    b
				(*
				    a
				    x
				)
			)
			(
			    c
				(/
					(+
						(-
							x
						)
						y
					)
				)				
			)
		)
	)
)

(defrule lemma-61
	(=
		(*
			(*
				a
				y
			)
			(/
				(+
					(-
						x
					)
					y
				)
			)
		)
		(+
			(*
			    a
				(+
					(-
						x
					)
					y
				)					
				(/
					(+
						(-
							x
						)
						y
					)
				)				
			)
			(*
			    a
				x
				(/
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-57
		lemma-60
	)
)

(defrule lemma-62
    (implies
	    (and
		    (integerp x)
			(acl2-numberp y)
			(not (equal x y))
		)
		(=
			(+
				(*
					a
					(+
						(-
							x
						)
						y
					)					
					(/
						(+
							(-
								x
							)
							y
						)
					)				
				)
				(*
					a
					x
					(/
						(+
							(-
								x
							)
							y
						)
					)
				)
			)
			(+
				a
				(*
					a
					x
					(/
						(+
							(-
								x
							)
							y
						)
					)
				)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-63
    (implies
	    (and
		    (integerp x)
			(acl2-numberp y)
			(not (equal x y))
		)
		(=
			(*
				(*
					a
					y
				)
				(/
					(+
						(-
							x
						)
						y
					)
				)
			)
			(+
				a
				(*
					a
					x
					(/
						(+
							(-
								x
							)
							y
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-61
		lemma-62
	)
)

(defrule lemma-64
    (implies
	    (and
		    (integerp x)
			(acl2-numberp y)
			(not (equal x y))
		)
		(=
			(+
				a
				(*
					a
					x
					(/
						(+
							(-
								x
							)
							y
						)
					)
				)
			)
			(*
				(*
					a
					y
				)
				(/
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
		lemma-63
	)
)

(defrule lemma-65
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				(/
					(+
						(-
							(*
								x
								(/
									k
								)
							)
						)
						(*
							y
							(/
								k
							)
						)
					)
				)
			)
			(*
				(+
					(*
						a
						m
				    )
					(-
					    (*
					        b
						    n
					    )
					)
				)
				(/	
					(+
						(-
							x
						)
						y
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-47
			(
			    i
				1
			)
		)
	)
)

(defrule lemma-66
    (implies
	    (= a b)
		(= (* a a) (* b b))
	)
    :rule-classes nil
)

(defrule lemma-67
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
			)
			(*
				(*
				    a
					m
					(/
					    k
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    (:instance
		    lemma-66
			(
			    a
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)				
			)
			(
			    b
				(*
				    a
					m
					(/
					    k
					)
				)				
			)
		)
	)
)

(defrule lemma-68
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
				h
				h
			)
			(*
				(+
					(*
						a
						m
						(/
							k
						)
					)
					(-
						(*
							b
							n
							(/
								k
							)
						)
					)
				)
				(+
					(*
						a
						m
						(/
							k
						)
					)
					(-
						(*
							b
							n
							(/
								k
							)
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-41
	    (:instance
		    lemma-66
			(
			    a
				h				
			)
			(
			    b
				(+
					(*
						a
						m
						(/
							k
						)
					)
					(-
						(*
							b
							n
							(/
								k
							)
						)
					)
				)			
			)
		)
	)
)

(defrule lemma-69
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(expt
				h
				2
			)
			(*
				(+
					(*
						a
						m
						(/
							k
						)
					)
					(-
						(*
							b
							n
							(/
								k
							)
						)
					)
				)
				(+
					(*
						a
						m
						(/
							k
						)
					)
					(-
						(*
							b
							n
							(/
								k
							)
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-68
	)
)

(defruled lemma-70
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(expt
				h
				2
			)
			(*
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(/
				    k
				)
				(/
				    k
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-42
		lemma-68
	)
)

(defrule lemma-71
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
			    v
				v
			)
			(*
				(*
					(/
						k
					)
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(/
						k
					)
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-50
	    (:instance
		    lemma-66
			(
			    a
				v				
			)
			(
			    b
				(*
					(/
						k
					)
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)			
			)
		)
	)
)

(defrule lemma-72
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
			    v
				v
			)
			(*
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(/
					k
				)
				(/
					k
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-71
	)
)

(defrule lemma-73
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(expt v 2)
			(*
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(/
					k
				)
				(/
					k
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-72
	)
)

(defruled lemma-74
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
			(*
			    n
			    (expt v 2)
			)
			(*
			    n
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(/
					k
				)
				(/
					k
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-73
	)
)

(defruled lemma-75
    (implies
	    (and
	        (integerp
		         k
		    )
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    k
						)
					)
				)
				(*
				    a
					m
					(/
					    k
					)
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    k
						)
					)
				)
				(*
				    b
					m
					(/
					    k
					)
				)
			)
		)
		(=
		    (+
				(expt
					h
					2
				)
				(-
					(*
						n
						(expt v 2)
					)
				)
			)
			(+
				(*
					(+
						(*
							a
							m
						)
						(-
							(*
								b
								n
							)
						)
					)
					(+
						(*
							a
							m
						)
						(-
							(*
								b
								n
							)
						)
					)
					(/
						k
					)
					(/
						k
					)
				)
				(-
					(*
						n
						(*
							(+
								(*
									b
									m
								)
								(-
									a
								)
							)
						)
						(*
							(+
								(*
									b
									m
								)
								(-
									a
								)
							)
						)
						(/
							k
						)
						(/
							k
						)
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-70
	    lemma-74
	)
)

(defrule lemma-76
    (=
(EQUAL (+ (EXPT H 2)
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B I N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B M N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
                (+ (* N (EXPT V 2))
                   (* (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H I
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M N (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))))
(EQUAL (+ (EXPT H 2) (- (* N (EXPT V 2))))
        (+
		        (-
				(+
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B I N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B M N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))))
                   (* (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H I
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M N (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))))
	)
   :rule-classes nil
)

(defruled lemma-77
    (implies
	    (and
	        (integerp
		         k
		    )
			(EQUAL (+ (* A A) (- (* N B B))) K)
			(not
			    (=
				    k
					0
				)
			)
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
		    (+
				(expt
					h
					2
				)
				(-
					(*
						n
						(expt v 2)
					)
				)
			)
			(+
				(*
					(+
						(*
							a
							m
						)
						(-
							(*
								b
								n
							)
						)
					)
					(+
						(*
							a
							m
						)
						(-
							(*
								b
								n
							)
						)
					)
					(/
						(+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
					(/
						(+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
				(-
					(*
						n
						(*
							(+
								(*
									b
									m
								)
								(-
									a
								)
							)
						)
						(*
							(+
								(*
									b
									m
								)
								(-
									a
								)
							)
						)
						(/
							(+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
						(/
							(+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		     lemma-75
			      (k
				  (+ (EXPT A 2) (- (* N (EXPT B 2))))
				  )
				  
		)
	)
)

(defrule lemma-78
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT H 2)
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B I N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B M N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
(+ 
		(*
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(/
				    (+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(/
				    (+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
			)
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B I N
			v
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B M N
			v
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))))
	
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-70
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-78-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT H 2)
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 M P (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B M N V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B N P V
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
(+ 
		(*
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
				(/
				    (+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(/
				    (+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
			)
                   (* N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT A 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 M P (EXPT A 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 B M N
			v
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 B N P
			v
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))))
	
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-70
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-79
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (* N (EXPT V 2))
                   (* (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H I
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 A B M N
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M N (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2)))
							
(+
			(*
			    n
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
			)
                   (* (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A
				   			H
				   I
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A
				   			H
				   M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 A B M N
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 I M N (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2)))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-74
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-79-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (* N (EXPT V 2))
                   (* (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A H P
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 A B M N
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 M N P (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2)))
							
(+
			(*
			    n
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(*
					(+
						(*
							b
							m
						)
						(-
							a
						)
					)
				)
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
			)
                   (* (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A
				   			H
				   M
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A
				   			H
				   P
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT M 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 A B M N
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2))
                   (* 2 M N P (EXPT B 2)
                      (EXPT (+ (EXPT A 2) (- (* N (EXPT B 2))))
                            -2)))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-74
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-80
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ N (* 2 B I N V)
                   (* 2 B M N V)
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 I M (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
							
(+ N (* 2 B I N
			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
)
                   (* 2 B M N
			v
)
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 I M (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-50
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-80-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ N (* 2 B M N V)
                   (* 2 B N P V)
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 M P (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
							
(+ N (* 2 B M N
			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
)
                   (* 2 B N P
			v
)
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 M P (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-50
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-81
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ N (* 2 B M N V)
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 I M (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
							
(+ N (* 2 B M N
			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
)
                   (* (EXPT A 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 I M (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-50
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-81-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2)))) 0))
			(integerp v)
			(equal
				(+
					v
					(*
						a
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    b
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ N (* 2 B N P V)
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 M P (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))
							
(+ N (* 2 B N P
			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						b
						m
					)
					(-
						a
					)
				)
			)
)
                   (* (EXPT A 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* (EXPT B 2)
                      (EXPT N 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 (EXPT A 2)
                      (EXPT M 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 M P (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2)))))))



	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-50
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-82
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT I 2)
                   (* 2 A H I)
                   (* 2 A H M)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B I N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
(+ (EXPT I 2)
                   (* 2 A
				   			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
				   I)
                   (* 2 A H M)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B I N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-43
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-82-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT P 2)
                   (* 2 A H M)
                   (* 2 A H P)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B N P
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
(+ (EXPT P 2)
                   (* 2 A
				   			(*
				(/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
				   M)
                   (* 2 A H P)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B N P
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-43
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-83
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT I 2)
                   (* 2 A H M)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
(+ (EXPT I 2)
                   (* 2 A (*
				   (/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
				   M)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT I 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B M N
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-43
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-83-aux
    (implies
	    (and
	        (integerp
		         (+ (EXPT A 2) (- (* N (EXPT B 2))))
		    )
			(NOT (EQUAL  (+ (EXPT A 2) (- (* N (EXPT B 2))))  0))
			(integerp h)
			(equal
				(+
					h
					(*
						b
						n
						(/
						    (+ (EXPT A 2) (- (* N (EXPT B 2))))
						)
					)
				)
				(*
				    a
					m
					(/
					    (+ (EXPT A 2) (- (* N (EXPT B 2))))
					)
				)
			)
		)
		(=
(+ (EXPT P 2)
                   (* 2 A H S)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B N P
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
(+ (EXPT P 2)
                   (* 2 A (*
				   (/
					(+ (EXPT A 2) (- (* N (EXPT B 2))))
				)
				(+
					(*
						a
						m
					)
					(-
						(*
							b
							n
						)
					)
				)
			)
				   S)
                   (* N (EXPT A 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* N (EXPT B 2)
                      (EXPT P 2)
                      (/ (+ (EXPT A 2) (- (* N (EXPT B 2))))))
                   (* 2 A B N P
                      (/ (+ (EXPT A 2)
                            (- (* N (EXPT B 2)))))))
	
	)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		    lemma-43
			(k (+ (EXPT A 2) (- (* N (EXPT B 2)))))
		)
	)
)

(defrule lemma-84
	(=
		(*
			n
			(+
				(expt a 2)
				(-
					(*
						n
						(expt b 2)
					)
				)
			)
		)
	    (+
			(*
			    n
				(expt a 2)
			)
			(-
			    (*
				    n
					n
					(expt b 2)
				)
			)
		)
	)
    :rule-classes nil
)

(defruled lemma-85
	(=
		(*
			n
			(+
				(expt a 2)
				(-
					(*
						n
						(expt b 2)
					)
				)
			)
		)
	    (+
			(*
			    n
				(expt a 2)
			)
			(-
			    (*
				    (expt b 2)
				    (expt n 2)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	   lemma-84
	)
)

(defruled lemma-85-aux
	(=
	    (+
			(*
			    n
				(expt a 2)
			)
			(-
			    (*
				    (expt b 2)
				    (expt n 2)
				)
			)
		)
		(*
			n
			(+
				(expt a 2)
				(-
					(*
						n
						(expt b 2)
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	   lemma-85
	)
)

(defruled lemma-86
	(=
	    (*
			(expt i 2)
			(+
				(expt a 2)
				(-
					(*
						n
						(expt b 2)
					)
				)
			)
		)
	    (+
			(*
			    (expt i 2)
				(expt a 2)
			)
			(-
			    (*
				    (expt i 2)
					n
				    (expt b 2)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    (:instance
		lemma-58
		(c
		    (expt i 2)
		)
		(a
		    (expt a 2)
		)
		(b
		    (-
			    (*
				    n
					(expt b 2)
				)
			)
		)
		)
	)
)

(defrule lemma-87
    (implies
	    (= a b)
	    (=
	        (+
			    a
			    c
		    )
		    (+
		        b
			    c
		    )
	    )
	)
    :rule-classes nil
)

(defrule lemma-88
	(=
		(+
			(*
				n
				(expt a 2)
			)
			(-
			    (*
			        (expt b 2)
				    (expt n 2)
                )
			)
			(+
				(*
					(expt b 2)
					(expt n 2)
				)			
				(*
					(expt a 2)
					(expt i 2)
				)
			)
		)
		(+
		    (*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
		    )
			(+
				(*
					(expt b 2)
					(expt n 2)
				)			
				(*
					(expt a 2)
					(expt i 2)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-85
	    (:instance
		lemma-87
		(a
			(+
				(*
					n
					(expt a 2)
				)
				(-
					(*
						(expt b 2)
						(expt n 2)
					)
				)
			)
		)
		(b
		    (*
			n
			(+
				(expt a 2)
				(-
					(*
						n
						(expt b 2)
					)
				)
			)
			)
		)
		(c
		   (+
				(*
					(expt b 2)
					(expt n 2)
				)			
				(*
					(expt a 2)
					(expt i 2)
				)
			)
		)
		)
	)
)

(defrule lemma-89
	(=
		(+
			(*
				n
				(expt a 2)
			)
			(-
			    (*
			        (expt b 2)
				    (expt n 2)
                )
			)
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
		    (*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
		    )
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-88
	)
)

(defrule lemma-90
	(=
		(+
			(*
				n
				(expt a 2)
			)
			(-
			    (*
			        (expt b 2)
				    (expt n 2)
                )
			)
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
			(*
				n
				(expt a 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-91
	(=
		(+
			(*
				n
				(expt a 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
		    (*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
		    )
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-89
		lemma-90
	)
)

(defrule lemma-92
	(=
		(+
			(*
				n
				(expt a 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
			(*
				(expt a 2)
				(expt i 2)
			)
			(-
			    (*
				    n
					(expt b 2)
					(expt i 2)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
			)
			(*
				n
				(expt a 2)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-93
	(=
		(+
		    (*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
		    )
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
			(*
				(expt a 2)
				(expt i 2)
			)
			(-
			    (*
				    n
					(expt b 2)
					(expt i 2)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
			)
			(*
				n
				(expt a 2)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-91
		lemma-92
	)
)

(defrule lemma-94
	(=
		(+
			(*
				(expt a 2)
				(expt i 2)
			)
			(-
			    (*
				    n
					(expt b 2)
					(expt i 2)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
			)
			(*
				n
				(expt a 2)
			)
		)
		(+
			(*
				(expt i 2)
				(+
				    (expt a 2)
					(-
					    (*
						    n
					        (expt b 2)
						)
					)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
			)
			(*
				n
				(expt a 2)
			)
		)
	)
    :rule-classes nil
)

(defrule lemma-95
	(=
		(+
		    (*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
		    )
			(*
				(expt b 2)
				(expt n 2)
			)			
			(*
				(expt a 2)
				(expt i 2)
			)
		)
		(+
			(*
				(expt i 2)
				(+
				    (expt a 2)
					(-
					    (*
						    n
					        (expt b 2)
						)
					)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
			)
			(*
				n
				(expt a 2)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-93
		lemma-94
	)
)

(defrule lemma-96
	(=
	    (*
			(+
				(*
					n
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
				(*
					(expt b 2)
					(expt n 2)
				)			
				(*
					(expt a 2)
					(expt i 2)
				)
			)
			(/
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
			)
		)
		(*
			(+
				(*
					(expt i 2)
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
				(*
					n
					(expt b 2)
					(expt i 2)
				)
				(*
					n
					(expt a 2)
				)
			)
			(/
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-95
	)
)

(defrule lemma-97
    (=
		(*
			(+
				a
				b
				c
			)
			d
		)
		(+
			(*
				a
				d
			)
			(*
			    b
				d
			)
			(*
			    c
				d
			)
		)
	)
	:rule-classes nil
)

(defrule lemma-98
	(=
		(+
			(*
				n
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
			(*
				(expt b 2)
				(expt n 2)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)			
			(*
				(expt a 2)
				(expt i 2)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
		)
		(+
			(*
				(expt i 2)
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
			(*
				n
				(expt b 2)
				(expt i 2)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
			(*
				n
				(expt a 2)
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-96
		(:instance
		    lemma-97
			(a
			    (*
					n
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
			(b
				(*
					(expt b 2)
					(expt n 2)
				)
			)
			(c
			    (*
					(expt a 2)
				    (expt i 2)
				)
			)
			(d
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)			
			)
		)
		(:instance
		    lemma-97
			(a
			    (*
					(expt i 2)
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)
			)
			(b
				(*
					n
					(expt b 2)
					(expt i 2)
				)
			)
			(c
			    (*
					n
					(expt a 2)
				)
			)
			(d
				(/
					(+
						(expt a 2)
						(-
							(*
								n
								(expt b 2)
							)
						)
					)
				)			
			)
		)
	)
)

(defrule lemma-99
    (implies
		(not
			(=
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
			    0
			)
		)
		(=
			(+
				n
				(*
					(expt b 2)
					(expt n 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)			
				(*
					(expt a 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
			(+
				(expt i 2)
				(*
					n
					(expt b 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
				(*
					n
					(expt a 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
		)
	)
    :rule-classes nil
	:use
	(
	    lemma-98
	)
)

(defrule lemma-100
    (=
	    (+
		    a
			b
			c
		)
	    (+
		    a
			c
			b
		)
	)
    :rule-classes nil
)

(defrule lemma-101
    (implies
		(not
			(=
				(+
					(expt a 2)
					(-
						(*
							n
							(expt b 2)
						)
					)
				)
			    0
			)
		)
		(=
			(+
				n			
				(*
					(expt a 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
				(*
					(expt b 2)
					(expt n 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
			(+
				(expt i 2)
				(*
					n
					(expt a 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
				(*
					n
					(expt b 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
		)
	)
    :rule-classes ((:rewrite :match-free :all))
	:use
	(
	    lemma-99
		(:instance
		    lemma-100
			(a
			    n
			)
			(b
				(*
					(expt b 2)
					(expt n 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
			(c
				(*
					(expt a 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
		)
		(:instance
		    lemma-97
			(a
			    (expt i 2)
			)
			(b
				(*
					n
					(expt b 2)
					(expt i 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
			(c
				(*
					n
					(expt a 2)
					(/
						(+
							(expt a 2)
							(-
								(*
									n
									(expt b 2)
								)
							)
						)
					)
				)
			)
		)
	)
)