hip_include 'node.ss'

ll<n> == self=null & n=0
    or self::node<_, q> * q::ll<n-1>
    inv n>=0;

pred_sess ll2<n> == A -> B : self = null & n = 0 ;; C -> D : emp; 
