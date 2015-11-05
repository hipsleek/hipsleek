relation P(int[] a).
relation Q(int[] a,int[] b,int r,int i,int j).

  int foo(ref int[] arr,int k,int j)
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(arr,arr',res,k,j);
{
   if(arr[k]>0){
      arr[k] = 0;
      return foo(arr,j,k);
   }
   else{
     return arr[k]+arr[j]+5;
   }

}


/*

Q:={[a__j,a__k,a,k,j] -> [PRIa__j,PRIa__k,PRIa,res] -> []: ((PRIa__j=a__j && PRIa__k=a__k && PRIa=a && PRIa__k<=0 && ((j<k) || (j>k)) && PRIa__j+5+PRIa__k=res && a__j+5+PRIa__k=res || PRIa__j=a__j && PRIa__k=a__k && PRIa=a && PRIa__k<=0 && PRIa__j=PRIa__k && a__j=PRIa__k && res=PRIa__k+PRIa__k+5) ||  (exists (fc_1258: (exists (a_1255__k: (exists (a_1255__j: (exists (a_1255:Q(a_1255__k,a_1255__j,a_1255,j,k,PRIa__k,PRIa__j,PRIa,res) && a_1255__k=fc_1258 && (j=k || a_1255__j=a__j) && (k=k || a_1255__k=a__k))) )) ))  && fc_1258=0))  && 1<=a__k) && (((j<k) || (j>k)) || PRIa__j=PRIa__k) && (((k<j) || (k>j)) || a__k=a__j)
};
bottomupgen([Q], [5], SimHeur);

(((a__j >= 1 && a__k >= 1) && 0 = PRIa__j && 0 = PRIa__k && 5 = res) || ((0 >= PRIa__j && a__k >= 1) && PRIa__j = a__j && 0 = PRIa__k && PRIa__j + 5 = res) || (0 >= PRIa__k && PRIa__k = a__k && PRIa__j = a__j && PRIa__k + PRIa__j + 5 = res && a = PRIa))

*/

