global int stk;

// when just reading, why use ref parameter for global

void subt_foo2(int n) 
  requires stk>=n
  ensures stk'=stk-n; //'

