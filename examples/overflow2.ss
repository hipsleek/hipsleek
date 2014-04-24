data inode {
	int val;
}

II<i> == self=i & -100<=i<=100 inv self=i & -100<=i<=100;

I<i> == self::inode<i> & -100<=i<=100 inv -100<=i<=100;
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

int plus(int x, int y)
	requires x::II<i>*y::II<j> & -100<=i+j<=100
	ensures res::II<i+j> ;
	requires x::II<i>*y::II<j> & i<=0 & -100<=i+j
	ensures res::II<i+j> ;
	requires x::II<i>*y::II<j> & i>=0 & i+j<=100
	ensures res::II<i+j> ;
	requires x::II<i>*y::II<j> & j<=0 & -100<=i+j
	ensures res::II<i+j> ;
	requires x::II<i>*y::II<j> & j>=0 & i+j<=100
	ensures res::II<i+j> ;
{
        int k=x+y;
	return k;
}

int minus(int x, int y)
	requires x::II<i>*y::II<j> & -100<=i-j<=100
	ensures res::II<i-j> ;
	requires x::II<i>*y::II<j> & i>=0 & i-j<=100
	ensures res::II<i-j>  ;
	requires x::II<i>*y::II<j> & i<=0 & i-j>=-100
	ensures res::II<i-j>  ;
	requires x::II<i>*y::II<j> & -j<=0 & i-j>=-100
	ensures res::II<i-j>  ;
	requires x::II<i>*y::II<j> & -j>=0 & i-j<=100
	ensures res::II<i-j>  ;
	//requires x::II<i>*y::II<j> & j<=i
	//ensures res::UI<i-j>  ;
{
        int k=x-y;
	return k;
}

int d2(int x) requires true ensures x-1<=2res<=x ;
int div2(int x)
	requires x::II<i>
	ensures res::II<r> & i-1<=2r<=i ;
	//requires x::UI<i>
	//ensures x::UI<i>*res::UI<r> & i-1<=2r<=i ;
{
        int k=d2(x);
	return k;
}

bool gtez(int x) 
     requires x::II<i>
     ensures x::II<i> & i>=0 & res or x::II<i> &i<0 & !res;
     //ensures x::II<i> & (i>=0 & res or i<0 & !res);
{
  return x>=0;
}

int mid(int x, int y)
	requires x::II<i>*y::II<j> & i<=j
        ensures res::II<r> & i+j-1<=2r<=i+j;
{
   if (gtez(x)) { //(x>=0) {
    dprint;
    int k=minus(y,x);
    int k2=div2(k);
    //assume false;
    return plus(x,k2);
   } 
   else if (gtez(y)) { 
   //else if (y>=0) {
         int k=plus(x,y);
         return div2(k);
         }
        else {
         // same as top case
         //assume false;
         int k=minus(y,x);
         int k2=div2(k);
         return plus(x,k2);
         };
}

/*
inode mid2(inode x, inode y)
	requires x::I<i>*y::I<j> & 0<=i<=j
        ensures x::I<i>*y::I<j> * res::I<r> & i+j-1<=2r<=i+j;
{
   inode k=plus(y,x);
   inode k2=div2(k);
   return k2;
}
*/
