data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  requires c::cell<v>@a & a<:@L //a=@L
  ensures emp; //c::cell<w>@b & b=@L  ;
/*
  requires c::cell<v>@a & a=@L
  ensures emp; //c::cell<w>@b & b=@L  ;
*/
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}

/*
# ex8e1g.ss --esl

sleek file in ex8e2g.slk
[
 Label: [(,0 ); (,1 )]
 State:c::cell<v>@[@a, @a_1482]&c=c' & x'=v & (((a_1482<:@L & a<:@L & 
         2<=v) | (a_1482<:@L & v<=0 & a<:@L)))&{FLOW,(4,5)=__norm#E}[]
       es_pure: a_1482<:@L
       es_cond_path: [1; 0]
       es_var_measures 1: Some(MayLoop[]{})
       es_infer_vars_rel: []
 ]



*/
