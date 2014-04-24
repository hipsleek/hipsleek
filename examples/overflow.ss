data inode {
	int val;
}

II<i> == self=i & -100<=i<=100 inv -100<=i<=100;

I<i> == self::inode<i> & -100<=i<=100 
	inv -100<=i<=100;
UI<i> == self::inode<i> & 0<=i<=200 
	inv 0<=i<=200;

inode id(inode x)
	requires x::UI<i> & i<=100
	ensures x::UI<i>*res::I<i> ;
{
    int k=x.val;
    return new inode(k);
}

int plus2(int x,int y)
	requires x::II<i>*y::II<j> & -100<=i+j<=100
	ensures res::II<i+j> ;
	requires x::II<i>*y::II<j> & i<=0 & -100<=i+j
	ensures res::II<i+j> ;
        requires -100<=x+y<=100
        ensures res=x+j;
{
        int k=x+y;
	return k;
}

inode plus(inode x, inode y)
	requires x::I<i>*y::I<j> & -100<=i+j<=100
	ensures x::I<i>*y::I<j>*res::I<i+j> ;
	//requires x::I<i>*y::I<j> & i>=0 & j<=0
	//ensures x::I<i>*y::I<j>*res::I<i+j> ;
	//requires x::I<i>*y::I<j> & i<=0 & j>=0
	//ensures x::I<i>*y::I<j>*res::I<i+j> ;
	requires x::I<i>*y::I<j> & i<=0 & -100<=i+j
	ensures x::I<i>*y::I<j>*res::I<i+j> ;
	requires x::I<i>*y::I<j> & i>=0 & i+j<=100
	ensures x::I<i>*y::I<j>*res::I<i+j> ;
	requires x::I<i>*y::I<j> & j<=0 & -100<=i+j
	ensures x::I<i>*y::I<j>*res::I<i+j> ;
	requires x::I<i>*y::I<j> & j>=0 & i+j<=100
	ensures x::I<i>*y::I<j>*res::I<i+j> ;
{
        int k=x.val+y.val;
	return new inode(k);
}

inode minus(inode x, inode y)
	requires x::I<i>*y::I<j> & -100<=i-j<=100
	ensures res::I<i-j> ;
	//requires x::I<i>*y::I<j> & 0<=j<=i
	//ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	//requires x::I<i>*y::I<j> & i<=0 & j<=0
	//ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	requires x::I<i>*y::I<j> & i>=0 & i-j<=100
	ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	requires x::I<i>*y::I<j> & i<=0 & i-j>=-100
	ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	requires x::I<i>*y::I<j> & -j<=0 & i-j>=-100
	ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	requires x::I<i>*y::I<j> & -j>=0 & i-j<=100
	ensures x::I<i>*y::I<j>*res::I<i-j>  ;
	//requires x::I<i>*y::I<j> & j<=i
	//ensures x::I<i>*y::I<j>*res::UI<i-j>  ;
{
        int k=x.val-y.val;
	return new inode(k);
}

int d2(int x) requires true ensures x-1<=2res<=x ;
inode div2(inode x)
	requires x::I<i>
	ensures x::I<i>*res::I<r> & i-1<=2r<=i ;
	//requires x::UI<i>
	//ensures x::UI<i>*res::UI<r> & i-1<=2r<=i ;
{
        int k=d2(x.val);
	return new inode(k);
}

inode mid(inode x, inode y)
	requires x::I<i>*y::I<j> & i<=j
        ensures x::I<i>*y::I<j> * res::I<r> & i+j-1<=2r<=i+j;
{
   if (x.val>=0) {
    inode k=minus(y,x);
    inode k2=div2(k);
    return plus(x,k2);
   } 
   else if (y.val>=0) {
         inode k=plus(x,y);
         return div2(k);
         }
        else {
         // same as top case
         inode k=minus(y,x);
         inode k2=div2(k);
         return plus(x,k2);
         };
}

inode mid2(inode x, inode y)
	requires x::I<i>*y::I<j> & 0<=i<=j
        ensures x::I<i>*y::I<j> * res::I<r> & i+j-1<=2r<=i+j;
{
   inode k=plus(y,x);
   inode k2=div2(k);
   return k2;
}
