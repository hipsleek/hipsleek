hip_include 'scontracts/mapprimitives.ss'

/* below succeeds - OK */
void foo1(mapping(int => int) proposals, int i, int m, int n)
  case {
    i<0  -> requires true
            ensures  true;
    i>=n & i>=0 ->
            requires [ts0] proposals::Map<ts0> &
                      forall(j: !(m<=j & j<m+n) | ts0[j]=0)
            ensures  (exists ts1: proposals::Map<ts1> &
                      forall(j: !(m<=j & j<m+n) | ts1[j]=0));
    i<n  & i>=0 ->
            requires [ts0] proposals::Map<ts0> &
                      forall(j: !(m<=j & j<m+i) | ts0[j]=0)
            ensures  (exists ts1: proposals::Map<ts1> &
                      forall(j: !(m<=j & j<=m+i) | ts1[j]=0));
  }
{
 if(0<=i && i<n)
 {
   proposals[m+i] = 0;
   foo1(proposals, i+1,m,n);
 }
}
