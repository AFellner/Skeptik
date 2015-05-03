(set .c1 (eq_reflexive :conclusion ((= c_3 c_3))))
(set .c2 (eq_congruent :conclusion ((not (= c_3 c_3)) (not (= c_4 (f1 c_2 c_3))) (= (f1 c_4 c_3) (f1 (f1 c_2 c_3) c_3)))))
(set .c3 (eq_congruent :conclusion ((not (= c_4 (f1 c_2 c_3))) (not (= c_3 c_3)) (= (f1 c_3 (f1 c_2 c_3)) (f1 c_3 c_4)))))
(set .c4 (eq_congruent :conclusion ((not (= (f1 c_3 c_0) c_2)) (not (= c_3 c_3)) (= (f1 c_3 c_2) (f1 c_3 (f1 c_3 c_0))))))
(set .c5 (eq_reflexive :conclusion ((= c_0 c_0))))
(set .c6 (eq_congruent :conclusion ((not (= c_0 c_0)) (not (= (f1 c_3 c_3) c_0)) (= (f1 c_0 c_0) (f1 (f1 c_3 c_3) c_0)))))
(set .c7 (eq_transitive :conclusion ((not (= (f1 c_3 c_2) (f1 c_3 (f1 c_3 c_0)))) (not (= (f1 c_3 (f1 c_3 c_0)) (f1 (f1 c_3 c_3) c_0))) (not (= (f1 c_0 c_0) (f1 (f1 c_3 c_3) c_0))) (= (f1 c_0 c_0) (f1 c_3 c_2)))))
(set .c8 (eq_congruent :conclusion ((not (= c_3 c_3)) (not (= (f1 c_0 c_0) (f1 c_3 c_2))) (= (f1 (f1 c_0 c_0) c_3) (f1 (f1 c_3 c_2) c_3)))))
(set .c9 (eq_congruent :conclusion ((not (= c_3 c_3)) (not (= (f1 c_3 c_3) c_0)) (= (f1 c_0 c_3) (f1 (f1 c_3 c_3) c_3)))))
(set .c10 (th_resolution :clauses (.c1 .c9) :conclusion ((not (= (f1 c_3 c_3) c_0)) (= (f1 c_0 c_3) (f1 (f1 c_3 c_3) c_3)))))
(set .c11 (eq_congruent :conclusion ((not (= (f1 c_3 c_3) c_0)) (not (= c_3 c_3)) (= (f1 c_3 c_0) (f1 c_3 (f1 c_3 c_3))))))
(set .c12 (th_resolution :clauses (.c1 .c11) :conclusion ((not (= (f1 c_3 c_3) c_0)) (= (f1 c_3 c_0) (f1 c_3 (f1 c_3 c_3))))))