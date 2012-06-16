data cell{int val;}
 
 // in the formulas in requires and ensures you can use also equalties for share variables and constants , examples of constants are @L, @R, @LL, @LR, @RR...
 
 
int read (cell x)
 requires [a,b] x::cell@s<v> & join (a,b,s) ensures x::cell@s<v>  & res = v &join (a,b,s) ;
 {
	return x.val;
 } 
 // this verification would fail when checking if the postcondition holds at the end of the method. 
 // at the end HIP will verify that x::cell@s<v> & join (a,b,s) & res = v |- x::cell@s<v>  & res = v &join (a,b,s)  -> and this fails
 
 
 int  sum3 (cell x, cell y, cell z)
   requires x::cell@a<v1> * y::cell@b<v2> * z::cell@c<v3> & join(a,b,c) ensures  x::cell@a<v1> * y::cell@b<v2> * z::cell@c<v3> & join(a,b,c) & res=v1+v2+v3;
   {
	return x.val+y.val+z.val;			// should also fail the post condition proving same reason as above
   }
 
 void read3call (cell x, cell y, cell z)
	requires x::cell@m<_> * y::cell@n<_> * z::cell@p<_> & join (m,n,p ) ensures true ;
	{
		int i = sum3(x,y,z); // fails in proving the precondition of read3 when doing the entailment x::cell@m<_> * y::cell@n<_> * z::cell@p<_> & join (m,n,p ) |-  x::cell@a<v1> * y::cell@b<v2> * z::cell@c<v3> & join(a,b,c)
	}
 