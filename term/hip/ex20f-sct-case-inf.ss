void loo (ref int x, ref int y,int a, int b)
 infer [@term]
 requires true
  ensures true;
/*
 case {
   x>0 | y>0 -> 
    case {
     a=b -> requires Term[x]
       ensures true;
     a!=b -> requires MayLoop
             ensures true;
     }
   x<=0 & y<=0 ->
     requires Term[] ensures true;
 }
*/
{
  if (x>0 || y>0) {
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex20f.ss

(==tpdispatcher.ml#2785==)
case_split_init@1
case_split_init inp1 :?
case_split_init inp2 :?
case_split_init@1 EXIT:[	loo: [[4] y<=0 & x<=0@B,[5] y<=0 & 1<=x@R,[6] 1<=x & 1<=y@R,[7] x<=0 & 1<=y@R]


# can we derive the following case-specs
  instead?


void loo (ref int x, ref int y,int a, int b)
 case {
   x>0 | y>0 -> 
    case {
     a=b -> 
      case {
       x>0 -> requires Term[x]
              ensures true;
       x<=0 -> requires Term[y]
       ensures true;
      }
     a!=b -> requires MayLoop
             ensures true;
     }
   x<=0 & y<=0 ->
     requires Term[] ensures true;
 }
]

 */
