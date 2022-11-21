; Begin SMT Formulation

; Define Horizontal Edge Cost
(declare-const COST_h1 (_ BitVec 4))
(assert (= COST_h1 (_ bv2 4)))

; Define Vertical Edge Cost
(declare-const COST_v1 (_ BitVec 4))
(declare-const COST_v2 (_ BitVec 4))
(assert (= COST_v1 (_ bv6 4)))
(assert (= COST_v2 (_ bv3 4)))

; Define Steiner Point Cost
(declare-const COST_sp (_ BitVec 4))
(assert (= COST_sp (_ bv1 4)))


; Define Edges
;; r1
(declare-const E_r1c1_r1c2 Bool)
(declare-const E_r1c1_r2c1 Bool)
(declare-const E_r1c2_r2c2 Bool)
;; r2
(declare-const E_r2c1_r2c2 Bool)
(declare-const E_r2c1_r3c1 Bool)
(declare-const E_r2c2_r3c2 Bool)
;; r3
(declare-const E_r3c1_r3c2 Bool)

; Define Vertices (Driver, Sinks, Steiner)
(declare-const V_r1c1 Bool)
(declare-const V_r1c2 Bool)
(declare-const V_r2c1 Bool)
(declare-const V_r2c2 Bool)
(declare-const V_r3c1 Bool)
(declare-const V_r3c2 Bool)

; Assert Driver and sinks vertices are used
(assert (= V_r3c1 true))
(assert (= V_r2c2 true))
(assert (= V_r1c1 true))

; Assert if a vertex is used, at least one connected edge is used as well
(assert (ite (= V_r1c1 true) ((_ at-least 1) E_r1c1_r1c2 E_r1c1_r2c1) (= 1 1)))
(assert (ite (= V_r1c2 true) ((_ at-least 1) E_r1c1_r1c2 E_r1c2_r2c2) (= 1 1)))
(assert (ite (= V_r2c1 true) ((_ at-least 1) E_r1c1_r2c1 E_r2c1_r2c2 E_r2c1_r3c1) (= 1 1)))
(assert (ite (= V_r2c2 true) ((_ at-least 1) E_r1c2_r2c2 E_r2c1_r2c2 E_r2c2_r3c2) (= 1 1)))
(assert (ite (= V_r3c1 true) ((_ at-least 1) E_r2c1_r3c1 E_r3c1_r3c2) (= 1 1)))
(assert (ite (= V_r3c2 true) ((_ at-least 1) E_r2c2_r3c2 E_r3c1_r3c2) (= 1 1)))


; Assert if an edge is used, the two immediate vertices is used as well
;; r1
(assert (ite (= E_r1c1_r1c2 true) (and (= V_r1c1 true) (= V_r1c2 true)) (= 1 1)))
(assert (ite (= E_r1c1_r2c1 true) (and (= V_r1c1 true) (= V_r2c1 true)) (= 1 1)))
(assert (ite (= E_r1c2_r2c2 true) (and (= V_r1c2 true) (= V_r2c2 true)) (= 1 1)))
;; r2
(assert (ite (= E_r2c1_r2c2 true) (and (= V_r2c1 true) (= V_r2c2 true)) (= 1 1)))
(assert (ite (= E_r2c1_r3c1 true) (and (= V_r2c1 true) (= V_r3c1 true)) (= 1 1)))
(assert (ite (= E_r2c2_r3c2 true) (and (= V_r2c2 true) (= V_r3c2 true)) (= 1 1)))
;; r3
(assert (ite (= E_r3c1_r3c2 true) (and (= V_r3c1 true) (= V_r3c2 true)) (= 1 1)))

; Max steiner points is n - 1
(assert ((_ at-most 2) V_r1c2 V_r1c2 V_r2c1 V_r3c2))

; Minimize steiner points use (also can model over every single points)
(minimize   (bvadd  (ite ( = V_r1c1 true) COST_sp (_ bv0 4))
                    (ite ( = V_r1c2 true) COST_sp (_ bv0 4))
                    (ite ( = V_r2c1 true) COST_sp (_ bv0 4))
                    (ite ( = V_r3c2 true) COST_sp (_ bv0 4))
            )
)

; Minimize total wirelength (this is bad cuz i assume total wl)
;; Horizontal wirelength
;;; less than h1
(assert (bvsle
            (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 4))
            )
            (bvadd  COST_h1)
        )
)
;;; not equal to 0
(assert (not(=
            (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 4))
            )
            (_ bv0 4)
        ))
)
;;; minimize horizontal wirelength
(minimize   (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 4))
            )
)

;; Vertical wirelength
;;; less than v1 + v2
(assert (bvsle
            (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 4))
            )
            (bvadd  COST_v1 COST_v2)
        )
)
;;; not equal to 0
(assert (not(=
            (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 4))
            )
            (_ bv0 4)
        ))
)
;;; minimize vertical wirelength
(minimize   (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 4))
            )
)
(check-sat)
(get-model)
(get-objectives)