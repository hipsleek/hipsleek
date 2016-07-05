relation B(int n, int a, int r).

// benefit of inference
//  - automatic
//  - more precise outcome
// disadvantage
//  - code may be wrong
//  - too general (may be good to restrict scenario)

int del(int n, int a)
  infer @post [n,B]
  requires (1<=a<n)
  ensures  B(n,a,res); 
  //  1<=a & a<=res & 1+res=n
{  
  if (a==1) {
    acc2(n); 
    n=n-1;
    return n;
  } else {
    acc(n);
    return 1+del(n-1,a-1);
  }
}

void acc(int n)
  requires n>=1
  ensures true;

void acc2(int n)
  requires n>=2
  ensures true;
