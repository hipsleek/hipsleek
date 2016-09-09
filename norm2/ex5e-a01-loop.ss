data cell {
  int val;
}

int test_fun (cell x, cell y, cell c)
  infer[@post_n]
  requires x::cell<m>*y::cell<n>*c::cell<k>
        ensures  x::cell<r1>*y::cell<r2>*c::cell<r3>;
{
    while (y.val < x.val) 
        infer[@post_n]
          requires x::cell<m>*y::cell<n>*c::cell<k>
          ensures   (exists r1,r2,r3: x::cell<r1>*y::cell<r2>*c::cell<r3>);
      {
            y.val = y.val + 1;
            c.val = c.val + 1;
      }
    return c.val;
}


/*
# norm2/ex5c.ss

!!! **pi.ml#779:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#780:>>REL POST:  post_1589(m,n,k,r1,r2,r3,flow)
!!! **pi.ml#781:>>POST:  r1=m & (((n>=r1 & n=r2 & k=r3) | (r1>=(1+n) & r1=r2 & n+r3=k+r1)))

=====

exists on post gives:

  exists (Impl)[m; n; k]x::cell<m>@M * y::cell<n>@M * c::cell<k>@M&
   MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists r1,r2,r3: x::cell<r1>@M * y::cell<r2>@M * c::cell<r3>@M&
     ((res=r3 & r1=m & m=r2 & r3=(r2-n)+k & n<r2) | 
      (res=r3 & r1=m & n=r2 & r3=k & m<=r2))&
     {FLOW,(4,5)=__norm#E}[])
     struct:EBase 
              (exists r1,r2,
              r3: x::cell<r1>@M * y::cell<r2>@M * c::cell<r3>@M&
              ((res=r3 & r1=m & m=r2 & r3=(r2-n)+k & n<r2) | 
               (res=r3 & r1=m & n=r2 & r3=k & m<=r2))&
              {FLOW,(4,5)=__norm#E}[])

=====
exists on pre:

!!! rels(b4)::[ post_1661(r1,r2,r3,m,n,k,res,flow)]
!!! pfs(b4)::[[ r3=res & r1<=r2]]
!!! rels(af)::[ post_1661(m,n,k,r1,r2,r3,res,flow)]
!!! pfs(af)::[[ r3=res & r1<=r2]]
!!! **pi.ml#779:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#780:>>REL POST:  post_1661(m,n,k,r1,r2,r3,res,flow)
!!! **pi.ml#781:>>POST:  r3=res & r1<=r2
!!! **pi.ml#782:>>REL PRE :  true
!!! **pi.ml#783:>>PRE :  true

*/
