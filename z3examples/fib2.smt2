(declare-rel fib (Int Int))
(declare-var n Int)
(declare-var m Int)
(declare-var p Int)

(rule (=> (<= n 0) (fib n 0)))
(rule (=> (and (<= n 2) (>= n 1)) (fib n 1)))
(rule (=> (and (> n 2) (fib (- n 1) m) (fib (- n 2) p)) (fib n (+ m p))))

; fib 0 0 is true
(query (fib 0 0) :print-certificate true)
; fib n m, m is always greater than or equal to zero
(query (and (fib n m) (< m 0)) :print-certificate true)
; fib n+1 p and fib n m and p <= m is satisfied only by fib 1 1 and fib 2 1
(query (and (fib (+ n 1) p) (fib n m) (<= p m)) :print-certificate true)
; fib n+1 p and fib n m and n > 1 should imply p is greater than m 
(query (and (fib (+ n 1) p) (fib n m) (> n 1) (<= p m)) :print-certificate true)
