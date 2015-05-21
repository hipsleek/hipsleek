relation P(int a).
  relation Q(int a,int r).

int foo(ref int a_5)
  infer [P,Q] requires P(a_5) ensures Q(res,a_5);
{
  if (a_5>10) {
    a_5 = 9;
    return a_5;
  } else {
    //assume false;
    return -1;
  }
}

/*
Post Inference result:
foo$int
 EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a_5]
           emp&((res=0-1 & a_5<=10) | (res=9 & 11<=a_5))&
           {FLOW,(4,5)=__norm#E}[]

update_with_td_fp call the simplify

And the simplifier will take out the free ones
(==omega.ml#960==)
Omega.simplify_ops@1859@1858@1857@1856@1855@1854@1853
Omega.simplify_ops inp1 : ((exists(res:res=0-1) & a_5<=10) | (exists(res:res=9) & 11<=a_5))
Omega.simplify_ops@1859 EXIT: (a_5<=10 | 11<=a_5)


*/
