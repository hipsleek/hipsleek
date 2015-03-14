
void foo2a(ref int a, int b)
 requires @full[a] & a>0
 ensures @zero[a];

// requires @full[a]*@value[b]
// ensures @zero[a];

