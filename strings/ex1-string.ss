//x = "abcd\0" STR(0,4)
// this is for reading only ..
// can we perform an analysis to determine
//  if a string is being used for reading

// this is for reading only
pred_prim STR<n:int,k:int> inv 0<=n<=k;

// this is for reading and writing
// but does not detect overflow
// nor track updates..
pred_prim WSTR<> inv true;

                   /*
STR create_str("...")
   requires true
   ensures res=STR(0,k) & k= len("...")
                   */

STR incStr(STR x)
  requires x::STR<n,k>@L & n<k & Term[]
  ensures res::STR<n+1,k>;
  requires x::STR<n,k>@L & n=k & Term[]
  ensures res::WSTR<>;
  requires x::WSTR<>@L & Term[]
  ensures res::WSTR<>;

void assignStr(STR x,int v)
/*
  requires x::STR<n,k>@L & Term[]
  ensures true;
*/
  requires x::WSTR<>@L & Term[]
  ensures emp;

int getChar(STR x)
  requires x::STR<n,k>@L & Term[]
  case { 
    n=k -> ensures res=0;
    n!=k -> ensures true;
  }
  requires x::WSTR<>@L
  ensures emp;
 
void while_fn(ref STR s1, STR s2)
  requires s1::WSTR<>@L * s2::STR<n2,k2>@L & Term[k2-n2]
  ensures s1'=s1;
{
  int c = getChar(s2);
  bool b = (c==0);
  if (!b) {
    assignStr(s1,c);
    STR new_s1=incStr(s1);
    STR new_s2=incStr(s2);
    while_fn(new_s1,new_s2);
  }
}
