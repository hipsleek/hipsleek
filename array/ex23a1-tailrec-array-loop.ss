relation P(int a,int b,int r).
  relation P1(int[] a,int[] b).
  relation P2(int[] a,int[] b,int r).


  void wloop(ref int[] a)
  infer[@arrvar,P1,update_array_1d]
    requires true
      ensures P1(a,a');
{
  if (a[5]>0) {
    a[5]=a[5]-1;
    wloop(a);
  }
}

/*

This one works!!!

P1:={[a___5___,a] -> [PRIa___5___,PRIa] -> []: (a___5___<=0 && a___5___=PRIa___5___||  ((exists (a_1224___5___: P1(a_1224___5___,a_1224,PRIa___5___,PRIa) && a_1224___5___=a___5___-(1) ))      && 1<=a___5___))
};
bottomupgen([P1], [2], SimHeur);

This does not...

P1:={[a___5___,a] -> [PRIa___5___,PRIa] -> []: (PRIa=a && a___5___<=0 ||  (exists (a_1224___5___: (exists (a_1224:P1(a_1224___5___,a_1224,PRIa___5___,PRIa) && a_1224___5___=a___5___-(1))) ))      && 1<=a___5___)
};
bottomupgen([P1], [3], SimHeur);

Var version:

P1:={[a] -> [PRIa] -> []: (PRIa=a && a<=0 ||  (exists (a_1193:a_1193=a-(1) && P1(a_1193,PRIa)))  && 1<=a)
};
bottomupgen([P1], [2], SimHeur);

int loop(ref int[] a)
//infer[@post_n]
  infer[P2]
  requires true
  ensures P2(a,a',res);
{
  while(a[5]>0)
    infer[P1,update_array_1d]
    requires true
      ensures P1(a,a');
  {
    a[5] = a[5]-1;
  }
  return a[5];

}
*/
