data cell{
 int fst;
}

relation P(ann v).
  relation Q(ann v1,ann v2).



int foo1(int n,cell x, cell y)
  infer [Q]
  requires x::cell<v>@a * y::cell<w>@c & Q(a,c)
  ensures  x::cell<v>@b * y::cell<w>@d  ;
{
 if (n<0) return x.fst;
 return n;
}



/*

#in this case c should be "strenghten" to @A?

foo1$int~cell~cell
 EBase exists (Expl)[](Impl)[a; v; c; w](ex)[]x::cell<v>@a * y::cell<w>@c&
       a=@L & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1477,w_1478,b_1479,d_1480: x::cell<v_1477>@b_1479 * 
           y::cell<w_1478>@d_1480&v_1477=v & w_1478=w&{FLOW,(4,5)=__norm#E}

*/
