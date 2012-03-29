data cell {int val;}

int sum (cell i, cell j)
  infer[v1,v2,v3,v4]
  requires i::cell<a>@v1*j::cell<b>@v2 * k::cell<c>@A
  ensures  i::cell<a>@v3*j::cell<b>@v4 & res=a+b;
{
  return i.val + j.val;
}

/*
PROBLEM : post correct but pre j::cell<b>@L incorrect..

!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v1; a; v2; b](ex)i::cell<a>@L[Orig] * j::cell<b>@L[Orig]&true&{FLOW,(20,21)=__norm}[]
                    EBase true&v1<=0 & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 3::
                              EXISTS(b_575: i::cell<b_575>@M[Orig]&b_575=b&
*/
void copy (cell i, cell j)
/*  infer[v1,v2]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  i::cell<b>@v1*j::cell<b>@v2; */

/*  infer[v3,v4]
  requires i::cell<a>@M*j::cell<b>@L
  ensures  i::cell<b>@v3*j::cell<b>@v4; */

 infer[v1,v2]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  i::cell<b>@M*j::cell<b>@I; //success? (if infered: v1 <- M, v2 <-L)
  //ensures  true;
{
  i.val=j.val;
}


/*
PROBLEM : inferred @L instead of @M
  v1<:@L  & v2<:@L & v1<:@M & v2<:@M
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v1; a; v2; b](ex)i::cell<a>@L[Orig] * 
                  j::cell<b>@L[Orig]&true&{FLOW,(20,21)=__norm}[]
*/
void swap (cell i, cell j)
  infer[v1,v2,v3,v4]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  i::cell<b>@v3*j::cell<a>@v4;
{
  int t = i.val;
  i.val = j.val;
  j.val = t;
}
