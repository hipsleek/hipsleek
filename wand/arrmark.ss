relation markedzero(int[] a) == forall (i:(a[i] = 0)). 

void mark(int[] x,int i,int l)
requires dom(x,i,l)
ensures markedzero(x);
{
if(!(i<l)) return;
if(x[i] == 0) return;
x[i] = 0;
mark(x,i+1,l);
}
