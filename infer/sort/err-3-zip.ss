/* selection sort */

data node {
	int val; 
	node next; 
}

ll<> == self=null
  or self::node<_,p> * p::ll<>
inv true;

llN<n> == self=null & n=0
  or self::node<v,p> * p::llN<n-1>
inv n>=0;


node zip(node x, node y)
  requires x::llN<a> * y::llN<b> & a<=b
  ensures  res::llN<a> ;
{
  if (x==null) return null;
  else {
    bind x to (xv,xn) in
    {
      bind y to (yv,yn) in
      { xv = xv+yv;
      xn = zip(xn,yn);
      }
    }
    return x;
  }
}
/*
--pip has extra {..} for bind
{
{(131, ):if (x == null) { 
  (131, ):(139, ):return null;
}
else { 
  (131, ):{(132, ):bind x to (xv, xn) in { {(133, ):bind y to (yv, yn) in { {xv = xv + yv;
xn = (137, ):zip(xn, yn);}
 }}
 };
(138, ):return x;}
;
}}
}


--pcp DONE
 translation can optimize on the return
  node v_node_30_542;
  v_node_30_542 = x;
  138::return v_node_30_542
  }]

 */









