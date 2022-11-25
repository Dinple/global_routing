; Begin SMT Formulation

; Define Total Edges Cost
(declare-const COST_Edge (_ BitVec 8))

; Define Total Vertex Cost
(declare-const COST_Vertex (_ BitVec 8))

; Define Total Wirelength Cost
(declare-const COST_WL (_ BitVec 8))

; Define Horizontal Edge Cost
(declare-const COST_H (_ BitVec 8))
(declare-const COST_h1 (_ BitVec 8))
(declare-const COST_h2 (_ BitVec 8))
(assert (= COST_h1 (_ bv2 8)))
(assert (= COST_h2 (_ bv1 8)))

; Define Vertical Edge Cost
(declare-const COST_V (_ BitVec 8))
(declare-const COST_v1 (_ BitVec 8))
(declare-const COST_v2 (_ BitVec 8))
(assert (= COST_v1 (_ bv6 8)))
(assert (= COST_v2 (_ bv3 8)))

; Define Steiner Point Cost
(declare-const COST_sp (_ BitVec 8))
(assert (= COST_sp (_ bv1 8)))

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
(assert (= V_r1c1 true))

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
(assert ((_ at-most 3) V_r1c1 V_r2c1 V_r2c3 V_r3c2 V_r3c3))

;; Horizontal wirelength
(assert (=      COST_H
                (bvadd  (ite ( = E_r1c1_r1c2 true) COST_h1 (_ bv0 8))
                        (ite ( = E_r1c2_r1c3 true) COST_h2 (_ bv0 8))
                        (ite ( = E_r2c1_r2c2 true) COST_h1 (_ bv0 8))
                        (ite ( = E_r2c2_r2c3 true) COST_h2 (_ bv0 8))
                        (ite ( = E_r3c1_r3c2 true) COST_h1 (_ bv0 8))
                        (ite ( = E_r3c2_r3c3 true) COST_h2 (_ bv0 8))
                )
        )

)
;;; not less than equal to some this "heuristic value"

;;; not equal to 0
(assert (not(=
            COST_H
            (_ bv0 8)
        ))
)

;;(minimize   COST_H)

;; Vertical wirelength
(assert (=      COST_V
                (bvadd  (ite ( = E_r1c1_r2c1 true) COST_v1 (_ bv0 8))
                        (ite ( = E_r1c2_r2c2 true) COST_v1 (_ bv0 8))
                        (ite ( = E_r1c3_r2c3 true) COST_v1 (_ bv0 8))
                        (ite ( = E_r2c1_r3c1 true) COST_v2 (_ bv0 8))
                        (ite ( = E_r2c2_r3c2 true) COST_v2 (_ bv0 8))
                        (ite ( = E_r2c3_r3c3 true) COST_v2 (_ bv0 8))
                )
        )
)
;;; not less than equal to some this "heuristic value"

;;; not equal to 0
(assert (not(=
            COST_V
            (_ bv0 8)
        ))
)

;;(minimize   COST_V)

; Minimize total wirelength (shouldnt consider V/H separately)
(assert (=      COST_WL
                (bvadd  COST_H
                        COST_V
                )
        )
)

(minimize   COST_WL)

; Minimize total edges used (no length considered, unit cost 1 per edge)
(assert (=      COST_Edge
                (bvadd  (ite ( = E_r1c1_r1c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r1c2_r1c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r2c1_r2c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r2c2_r2c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r3c1_r3c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r3c2_r3c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r1c1_r2c1 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r1c2_r2c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r1c3_r2c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r2c1_r3c1 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r2c2_r3c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = E_r2c3_r3c3 true) (_ bv1 8) (_ bv0 8))
                )
        )
)

; Minimize total vertices used 
(assert (=      COST_Vertex
                (bvadd  (ite ( = V_r1c1 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r1c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r1c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r2c1 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r2c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r2c3 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r3c1 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r3c2 true) (_ bv1 8) (_ bv0 8))
                        (ite ( = V_r3c3 true) (_ bv1 8) (_ bv0 8))
                )
        )

)
(minimize   COST_Vertex)
(minimize   COST_Edge)

; Connectivity Property |E| = |V| - 1
(assert (=      COST_Edge
                (bvsub  COST_Vertex (_ bv1 8))
        )
)

(check-sat)
(get-model)
(get-objectives)