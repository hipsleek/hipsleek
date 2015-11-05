relation P(int[] a).
relation Q(int[] a,int[] b,int r,int i,int j).

  int foo(ref int[] a,int k,int j)
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res,k,j);
{
   if(a[k]>0){
      a[k] = a[k]-1;
      return foo(a,j,k);
   }
   else{
     return a[k]+a[j]+5;
   }

}


/*

How to handle the number of disjunctions??


Q:={[a__j,a__k,a,k,j] -> [PRIa__j,PRIa__k,PRIa,res] -> []: ((PRIa__j=a__j && PRIa__k=a__k && PRIa=a && PRIa__k<=0 && ((j<k) || (j>k)) && PRIa__j+5+PRIa__k=res && a__j+5+PRIa__k=res || PRIa__j=a__j && PRIa__k=a__k && PRIa=a && PRIa__k<=0 && PRIa__j=PRIa__k && a__j=PRIa__k && res=PRIa__k+PRIa__k+5) ||  (exists (v_int_8_1250: (exists (a_1274__k: (exists (a_1274__j: (exists (a_1274:Q(a_1274__k,a_1274__j,a_1274,j,k,PRIa__k,PRIa__j,PRIa,res) && a_1274__k=v_int_8_1250 && (j=k || a_1274__j=a__j) && (k=k || a_1274__k=a__k))) )) ))  && v_int_8_1250=a__k-(1)))  && 1<=a__k) && (((j<k) || (j>k)) || PRIa__j=PRIa__k) && (((k<j) || (k>j)) || a__k=a__j)
};
bottomupgen([Q], [20], SimHeur);

(((((PRIa__j >= 0 && a__j >= 1 + PRIa__j) && k >= 1 + j) && a__k >= 1) && 0 = PRIa__k && PRIa__j + 5 = res) || ((((PRIa__j >= 0 && a__j >= 1 + PRIa__j) && j >= 1 + k) && a__k >= 1) && 0 = PRIa__k && PRIa__j + 5 = res) || ((((PRIa__k >= 0 && a__k >= 2 + PRIa__k) && j >= 1 + k) && a__j >= 1) && 0 = PRIa__j && PRIa__k + 5 = res) || ((((PRIa__k >= 0 && a__k >= 2 + PRIa__k) && k >= 1 + j) && a__j >= 1) && 0 = PRIa__j && PRIa__k + 5 = res) || (a__k >= 1 && j = k && 0 = PRIa__j && 0 = PRIa__k && a__k = a__j && 5 = res) || (((j >= 1 + k && 0 >= a__j) && PRIa__k >= 0) && a__j = PRIa__j && PRIa__k + 1 = a__k && a__j + PRIa__k + 5 = res) || (((k >= 1 + j && 0 >= a__j) && PRIa__k >= 0) && a__j = PRIa__j && PRIa__k + 1 = a__k && a__j + PRIa__k + 5 = res) || (0 >= a__k && a__k = PRIa__j && a__k = PRIa__k && a__k = a__j && 2*a__k + 5 = res && a = PRIa) || ((k >= 1 + j && 0 >= a__k) && a__j = PRIa__j && a__k = PRIa__k && a__j + a__k + 5 = res && a = PRIa) || ((j >= 1 + k && 0 >= a__k) && a__j = PRIa__j && a__k = PRIa__k && a__j + a__k + 5 = res && a = PRIa))


( But it is not strong enough...)
// j!=k and a'[j]>=0 and a[j] >= 1+a'[j] and a[k]>=1 and a'[k]=0 and res = a'[j] + 5
   (((((PRIa__j >= 0 && a__j >= 1 + PRIa__j) && k >= 1 + j) && a__k >= 1) && 0 = PRIa__k && PRIa__j + 5 = res)
 || ((((PRIa__j >= 0 && a__j >= 1 + PRIa__j) && j >= 1 + k) && a__k >= 1) && 0 = PRIa__k && PRIa__j + 5 = res)

// j!=k and a'[k]>=0 and a[k] >=2 + a'[k] and a[j]>=1 and a'[j]=0 and a'[k]+5 = res
 || ((((PRIa__k >= 0 && a__k >= 2 + PRIa__k) && j >= 1 + k) && a__j >= 1) && 0 = PRIa__j && PRIa__k + 5 = res)
 || ((((PRIa__k >= 0 && a__k >= 2 + PRIa__k) && k >= 1 + j) && a__j >= 1) && 0 = PRIa__j && PRIa__k + 5 = res)

// j==k and a[k]>0 at the beginning, that a[k] will drop to zero at the end
 || (a__k >= 1 && j = k && 0 = PRIa__j && 0 = PRIa__k && a__k = a__j && 5 = res)

// j!=k and a[j]<0 and a'[k]>=0 and a[j] = a'[j] and a[k] = a'[k]+1 and res = a'[k]+a[j]
 || (((j >= 1 + k && 0 >= a__j) && PRIa__k >= 0) && a__j = PRIa__j && PRIa__k + 1 = a__k && a__j + PRIa__k + 5 = res)
 || (((k >= 1 + j && 0 >= a__j) && PRIa__k >= 0) && a__j = PRIa__j && PRIa__k + 1 = a__k && a__j + PRIa__k + 5 = res)

// a[k]=a[j] & a[k]<0 ... It doesn't matter that whether k=j
 || (0 >= a__k && a__k = PRIa__j && a__k = PRIa__k && a__k = a__j && 2*a__k + 5 = res && a = PRIa)

// j!=k and a[k]<0 at the beginning
 || ((k >= 1 + j && 0 >= a__k) && a__j = PRIa__j && a__k = PRIa__k && a__j + a__k + 5 = res && a = PRIa)
 || ((j >= 1 + k && 0 >= a__k) && a__j = PRIa__j && a__k = PRIa__k && a__j + a__k + 5 = res && a = PRIa))







((j>=(1+k) & (a[k])>=1 & 0=a'[k] & (a[j])+5=res) | (k>=(1+j) & (a[k])>=1 & 0=a'[k] & (a[j])+5=res)
| ((a[j])>=1 & a[j]=a[k] & k=j & 0=a'[j] & 0=a'[k] & 5=res)
| (0>=(a'[k]) & a'[k]=a'[j] & a'[k]=a[j] &
(2*(a'[k]))+5=res & a=a') | (0>=(a'[k]) & k>=(1+j) & (a'[k])+(a[j])+
     5=res & a=a') | (0>=(a'[k]) & j>=(1+k) & (a'[k])+(a[j])+5=res & a=a'))
*/

