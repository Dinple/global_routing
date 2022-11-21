; Begin SMT Formulation

; Define Horizontal Edge Cost
(declare-const COST_h1 (_ BitVec 4))
(declare-const COST_h2 (_ BitVec 4))
(assert (= COST_h1 (_ bv2 4)))
(assert (= COST_h2 (_ bv1 4)))

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
(declare-const E_r1c2_r1c3 Bool)
(declare-const E_r1c1_r2c1 Bool)
(declare-const E_r1c2_r2c2 Bool)
(declare-const E_r1c3_r2c3 Bool)
;; r2
(declare-const E_r2c1_r2c2 Bool)
(declare-const E_r2c2_r2c3 Bool)
(declare-const E_r2c1_r3c1 Bool)
(declare-const E_r2c2_r3c2 Bool)
(declare-const E_r2c3_r3c3 Bool)
;; r3
(declare-const E_r3c1_r3c2 Bool)
(declare-const E_r3c2_r3c3 Bool)

; Define Vertices (Driver, Sinks, Steiner)
(declare-const V_r1c1 Bool)
(declare-const V_r1c2 Bool)
(declare-const V_r1c3 Bool)
(declare-const V_r2c1 Bool)
(declare-const V_r2c2 Bool)
(declare-const V_r2c3 Bool)
(declare-const V_r3c1 Bool)
(declare-const V_r3c2 Bool)
(declare-const V_r3c3 Bool)

; Assert Driver and sinks vertices are used
(assert (= V_r3c1 true))
(assert (= V_r2c2 true))
(assert (= V_r1c3 true))

; Assert if a vertex is used, at least one adjacent edge is used as well
(assert (ite (= V_r1c1 true) ((_ at-least 1) E_r1c1_r1c2 E_r1c1_r2c1) (= 1 1)))
(assert (ite (= V_r1c2 true) ((_ at-least 1) E_r1c1_r1c2 E_r1c2_r1c3 E_r1c2_r2c2) (= 1 1)))
(assert (ite (= V_r1c3 true) ((_ at-least 1) E_r1c2_r1c3 E_r1c3_r2c3) (= 1 1)))
(assert (ite (= V_r2c1 true) ((_ at-least 1) E_r1c1_r2c1 E_r2c1_r2c2 E_r2c1_r3c1) (= 1 1)))
(assert (ite (= V_r2c2 true) ((_ at-least 1) E_r1c2_r2c2 E_r2c1_r2c2 E_r2c2_r2c3 E_r2c2_r3c2) (= 1 1)))
(assert (ite (= V_r2c3 true) ((_ at-least 1) E_r1c3_r2c3 E_r2c2_r2c3 E_r2c3_r3c3) (= 1 1)))
(assert (ite (= V_r3c1 true) ((_ at-least 1) E_r2c1_r3c1 E_r3c1_r3c2) (= 1 1)))
(assert (ite (= V_r3c2 true) ((_ at-least 1) E_r2c2_r3c2 E_r3c1_r3c2 E_r3c2_r3c3) (= 1 1)))
(assert (ite (= V_r3c3 true) ((_ at-least 1) E_r2c3_r3c3 E_r3c2_r3c3) (= 1 1)))


; Assert if an edge is used, the two immediate vertices is used as well
;; r1
(assert (ite (= E_r1c1_r1c2 true) (and (= V_r1c1 true) (= V_r1c2 true)) (= 1 1)))
(assert (ite (= E_r1c2_r1c3 true) (and (= V_r1c2 true) (= V_r1c3 true)) (= 1 1)))
(assert (ite (= E_r1c1_r2c1 true) (and (= V_r1c1 true) (= V_r2c1 true)) (= 1 1)))
(assert (ite (= E_r1c2_r2c2 true) (and (= V_r1c2 true) (= V_r2c2 true)) (= 1 1)))
(assert (ite (= E_r1c3_r2c3 true) (and (= V_r1c3 true) (= V_r2c3 true)) (= 1 1)))
;; r2
(assert (ite (= E_r2c1_r2c2 true) (and (= V_r2c1 true) (= V_r2c2 true)) (= 1 1)))
(assert (ite (= E_r2c2_r2c3 true) (and (= V_r2c2 true) (= V_r2c3 true)) (= 1 1)))
(assert (ite (= E_r2c1_r3c1 true) (and (= V_r2c1 true) (= V_r3c1 true)) (= 1 1)))
(assert (ite (= E_r2c2_r3c2 true) (and (= V_r2c2 true) (= V_r3c2 true)) (= 1 1)))
(assert (ite (= E_r2c3_r3c3 true) (and (= V_r2c3 true) (= V_r3c3 true)) (= 1 1)))
;; r3
(assert (ite (= E_r3c1_r3c2 true) (and (= V_r3c1 true) (= V_r3c2 true)) (= 1 1)))
(assert (ite (= E_r3c2_r3c3 true) (and (= V_r3c2 true) (= V_r3c3 true)) (= 1 1)))

; Max steiner points is n - 1
(assert ((_ at-most 2) V_r1c1 V_r1c2 V_r2c1 V_r2c3 V_r3c2 V_r3c3))

; Minimize steiner points use (also can model over every single points)
(minimize   (bvadd  (ite ( = V_r1c1 true) COST_sp (_ bv0 4))
                    (ite ( = V_r1c2 true) COST_sp (_ bv0 4))
                    (ite ( = V_r2c1 true) COST_sp (_ bv0 4))
                    (ite ( = V_r2c3 true) COST_sp (_ bv0 4))
                    (ite ( = V_r3c2 true) COST_sp (_ bv0 4))
                    (ite ( = V_r3c3 true) COST_sp (_ bv0 4))
            )
)

; Minimize total wirelength (this is bad cuz i assume total wl)
;; Horizontal wirelength
(assert (bvsle
            (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r1c2_r1c3 true) COST_h2 (_ bv0 4))
                    (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r2c2_r2c3 true) COST_h2 (_ bv0 4))
                    (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r3c2_r3c3 true) COST_h2 (_ bv0 4))
            )
            (bvadd  COST_h1 COST_h2)
        )
)
(minimize   (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r1c2_r1c3 true) COST_h2 (_ bv0 4))
                    (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r2c2_r2c3 true) COST_h2 (_ bv0 4))
                    (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 4))
                    (ite ( = E_r3c2_r3c3 true) COST_h2 (_ bv0 4))
            )
)

;; Vertical wirelength
(assert (bvsle
            (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c3_r2c3 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c3_r3c3 true) COST_v2 (_ bv0 4))
            )
            (bvadd  COST_v1 COST_v2)
        )
)
(minimize   (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r1c3_r2c3 true) COST_v1 (_ bv0 4))
                    (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 4))
                    (ite ( = E_r2c3_r3c3 true) COST_v2 (_ bv0 4))
            )
)
(check-sat)
(get-model)
(get-objectives)