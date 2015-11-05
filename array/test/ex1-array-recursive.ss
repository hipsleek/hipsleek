//hip_include prelude_aux
//#option --ato
//relation P(int a,int r).

relation P2(int[] a,int[] a_prime,int r).
  relation P1(int[] a).
int foo2(ref int[] a)
  infer[P2,update_array_1d]
  requires true
//ensures P(a[5],res);
  ensures P2(a,a',res);
//ensures (a[5]>=5 & res=a[5]+6) | (a[5]<5 & res=11);
//ensures (a[5]>=5 & res=a[5]+6 & a'[5]=a[5]) | (a[5]<5 & a'[5]=5 & res=11);
{
  if (a[6]<5) {
    //a = update_arr(a,5,0);
    a[6] = a[6]+1;
    return foo2(a);
  }
  else{
    return a[6]+6;
  }
}

/*

Simplified fixcalc input:(with update_array_1d
P2:={[a___6___] -> [PRIa___6___,res] -> []: ((PRIa___6___=a___6___ && PRIa___6___=res-(6) && 11<=res) || ((exists (a_1238___6___: P2(a_1238___6___,PRIa___6___,res)  && a_1238___6___=a___6___+1 )) && a___6___<=4))
};
bottomupgen([P2], [1], SimHeur);


*/
/* int foo3(ref int a) */
/*   infer[P2,P1] */
/*   requires P1(a) */
/*   ensures P2(a,a',res); */
/* { */
/*   if (a<5) { */
/*     //a = update_arr(a,5,0); */
/*     a = a+1; */
/*     return foo3(a); */
/*   } */
/*   else{ */
/*     return a-6; */
/*   } */
/* } */
