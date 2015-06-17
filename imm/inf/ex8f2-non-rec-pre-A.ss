data cell{
 int fst;
}

relation P(ann v).
  relation Q(ann v1,ann v2).

  int foo1(int x,cell c)
  infer [P]
  requires c::cell<v>@a & P(a)
  ensures c::cell<w>@b ;
  /* infer [Q] */
  /* requires c::cell<v>@a */
  /* ensures c::cell<w>@b & Q(a,b); */
{
 if (x>0) return x+1;
 return x;
}

/*
how come no inf result? is it because rel obligation is empty? should it be true?

Checking procedure foo1$int~cell... 
Procedure foo1$int~cell SUCCESS.
*/


  int foo2(int x,cell c)
    infer [P,Q]
  requires c::cell<v>@a & P(a)
       ensures c::cell<w>@b & Q(a,b);
  /* infer [Q] */
  /* requires c::cell<v>@a */
  /* ensures c::cell<w>@b & Q(a,b); */
{
 if (x>0) return x+1;
 return x;
}

/*

since we have no rel oblg, thus a is not constrained, can we say a=@A? in our semantic this is weakening, no?

then post will be @L<:b --> strenghten to b=@A 

foo2$int~cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists w_1491,b_1492: c::cell<w_1491>@b_1492&a<:b_1492&
           {FLOW,(4,5)=__norm#E}[]
*/
