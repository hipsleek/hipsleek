relation Q(int i,int r).
  relation P(bag s).


int foo(int i)
  requires true
  ensures Q(i,res);


void loop(ref int[] a,int i,int c)
  requires i<=c+1
  ensures forall(k:!(i<=k<=c)|Q(k,a'[k])) &
         forall(k:(i<=k<=c)|a'[k]=a[k]);
{
  if(i<=c) {
    a[i]=foo(i);
      loop(a,i+1,c);
        }
}
