(define-sort Bag (T) (Array Int T Int))

(declare-const bag-allzero (Bag (Int)))
(assert (= bag-allzero ((as const (Bag (Int))) 0)))

(declare-const bag-allone (Bag (Int)))
(assert (= bag-allone ((as const (Bag (Int))) 1)))

(define-fun bag-union ((x (Bag (Int))) (y (Bag (Int)))) (Bag (Int))
((_ map (+ (Int Int) Int)) x y))
  
(define-fun bag-intersect ((x (Bag (Int))) (y (Bag (Int)))) (Bag (Int))
((_ map (ite (Bool Int Int) Int)) ((_ map (< (Int Int) Bool)) x y) x y))
  
(define-fun bag-diff ((x (Bag (Int))) (y (Bag (Int)))) (Bag (Int))
((_ map (ite (Bool Int Int) Int)) ((_ map (> (Int Int) Bool)) ((_ map (- (Int Int) Int)) x y) bag-allzero) 
((_ map (- (Int Int) Int)) x y) bag-allzero))

(define-fun bag-isset ((x (Bag Int))) Bool
(= (bag-union x bag-allzero) (bag-intersect x bag-allone)))
 
(declare-const s1 (Bag (Int)))
(declare-const s2 (Bag (Int)))
(declare-const s3 (Bag (Int)))
(declare-const s4 (Bag (Int)))
(declare-const s5 (Bag (Int)))
(declare-const s6 (Bag (Int)))
(push)
(assert (= s3 (bag-union s1 s2)))
(assert (= s4 (bag-intersect s1 s2)))
(assert (= s5 (bag-diff s1 s2)))
(assert (= (select s1 0 0) 5))
(assert (= (select s2 0 0) 3))
(assert (= (select s2 1 2) 4))
(assert (= (select s3 0 0) 8))
(assert (= (select s3 1 2) 4))
(assert (= (select s4 0 0) 3))
(assert (= (select s5 0 0) 2))
(assert (= (select s6 0 0) 1))
(assert (= (select s6 1 0) 1))
(assert (bag-isset s6))
(check-sat)
(get-model)
(pop)