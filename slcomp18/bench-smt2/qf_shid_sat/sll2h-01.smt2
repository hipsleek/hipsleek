(set-logic QF_SHLID)

(set-info :source |
Jens Katelaan, Harrsh, https://github.com/katelaan/harrsh/
|)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status sat)
(set-info :version "2018-06-18")

;; SLL from x1 to x2 where all nodes contain an additional pointer to x1
;; and singly-linked lists with additional pointer field as third arg


; Sorts for locations, one by cell sort
(declare-sort RefSll2h_t 0)

; Types of cells in the heap

(declare-datatypes (
	(Sll2h_t 0)
	) (
	((c_Sll2h_t (next RefSll2h_t) (head RefSll2h_t) ))
	)
)

; Type of heap
(declare-heap (RefSll2h_t Sll2h_t) 
)

;; Singly-linked lists with additional pointer field as third arg
(define-fun-rec sllpf ((in RefSll2h_t)(out RefSll2h_t) (head RefSll2h_t)) Bool
	(or 
		(and 
			(= in out)
			(_ emp RefSll2h_t Sll2h_t)
		)

		(exists ((u RefSll2h_t))
	 
		(sep 
			(pto in (c_Sll2h_t u head))
			(sllpf u out head)
		)
		)
	)
)

;; SLL from x1 to x2
;; where all nodes contain an additional pointer to x1
(define-fun-rec sllh ((in RefSll2h_t)(out RefSll2h_t)) Bool
	(sllpf in out in)
)

(check-sat) 
;; variables
(declare-const x0 RefSll2h_t)

(assert (sllh x0 (as nil RefSll2h_t))
)

(check-sat)

