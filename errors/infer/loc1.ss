int double (int n)
 requires true
 ensures res=2*n
 {
   if n=0 then 1
   else 2+double(n)
 }



int double2 (int n)
 requires true
 ensures res=2*n
 {
   if n=0 then 0
   else 3+double2(n)
 }
