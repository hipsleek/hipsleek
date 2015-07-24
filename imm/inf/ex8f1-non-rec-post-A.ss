data cell{
 int fst;
}

relation P(ann v).
  relation Q(ann v1,ann v2).

  int foo1(int x,cell c)
  infer [P]
  requires c::cell<v>@a & a=@A
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P(b);
{
 if (x>0) return x+1;
 return x;
}

/*
Post Inference result:
foo1$int~cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]emp&a=@A & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists w_1501,b_1502: emp&b_1502=@A&{FLOW,(4,5)=__norm#E}[]
*/



int foo3(int x,cell c)
  infer [Q]
  requires c::cell<v>@a 
  ensures c::cell<v>@b & Q(a,b);
{
 if (x<0) return 0;
 return x;
}

/**
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1521,b_1522: c::cell<v_1521>@b_1522&v_1521=v & 
           a<:b_1522&{FLOW,(4,5)=__norm#E}[]
           
*/

int foo2(int x,cell c)
  infer [P]
  requires c::cell<v>@a 
  ensures c::cell<v>@b & P(b);
{
 if (x<0) return 0;
 return x;
}

/**
Post Inference result:
foo2$int~cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1525,b_1526: c::cell<v_1525>@b_1526&v_1525=v&
           {FLOW,(4,5)=__norm#E}[]
           
*/

