//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [@arrvar,Q,update_array_1d] requires true ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  int k=5;
  if (a[5]>0) {
    // a[6] = a[6]+1;
    //    a[k] = a[5]-1;
    a[1] = a[1]+1;
    a[5] = a[5]-1;
    int r = foo(a);
    a[1]=a[1]+1;
    return r; } 
  else {
    return a[1];
  }
}

/*
# ex12.ss 


!!! **trans_arr.ml#4933:new_result [(a,a',[1;5];(a,a',[]]

 requires true
 ensures a[5]>0 & forall(i: i!=1 & i!=5 --> a'[i]=a[i])
      or a[5]<=0 & a'=a //forall(i:a'[i]=a[i]);


Post Inference result:
foo$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
  EAssume ref [a]
           emp&(((a[5])>=1 & a'[1]=res & a'[1]=(a[1])+(a[5]) & 0=a'[5]) 
   | (0>=(a'[5]) & a[1]=res & a=a'))&{FLOW,(4,5)=__norm#E}[]


Post Inference result:
foo$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
  EAssume ref [a]
      emp&(((a[5])>=1 & a'[1]=res & a'[1]=(a[1])+(a[5]) & 0=a'[5]) 
        & forall(i: i!=1 & i!=5 --> a'[i]=a[i])
   | (0>=(a'[5]) & a[1]=res & a=a'))&{FLOW,(4,5)=__norm#E}[]


[RELDEFN Q: ( update_array_1d(a_1252,a_1261,1+(a_1252[4]),4) & v_int_14_1233=(a[5])-1 & 
1<=(a[5]) & Q(a_1261,a',res) & update_array_1d(a,a_1252,v_int_14_1233,5)) -->  Q(a,a',res),
RELDEFN Q: ( a[4]=res & a'[4]=res & a'=a & a[5]=a'[5] & (a'[5])<=0) -->  Q(a,a',res)]
[RELDEFN Q: ( 
   update_array_1d(a_1252,a_1261,1+(a_1252[4]),4) 
  & v_int_14_1233=(a[5])-1 & 
   1<=(a[5]) & Q(a_1261,a',res) 
   & update_array_1d(a,a_1252,v_int_14_1233,5)) 
   -->  Q(a,a',res),
RELDEFN Q: ( a'[4]=res & a'=a & (a'[5])<=0) -->  Q(a,a',res)]
*


[RELDEFN Q: ( a4=a4'-1 & a5'=a5-1 & 1<=a5 & Q(a4',a5',res)) 
   -->  Q(a4,a5,res),
RELDEFN Q: ( a4=res & a5<=0) -->  Q(a4,a5,res)]


Manually modified fixcalc input:
Q:={[a___4___,a___5___,a] -> [PRIa___4___,PRIa___5___,PRIa,res] -> []: (a___4___=res && PRIa___4___=res && a=PRIa  && a___5___=PRIa___5___ && PRIa___5___<=0 ||  

(exists (fc_1267: 

(exists (fc_1266: 

(exists (a_1252___5___: (exists (a_1252___4___:  (exists (a_1252: 

        (exists (fc_a_1265: (exists (a_1261___5___: (exists (a_1261___4___: (exists (a_1261:a_1261___4___=fc_a_1265  && (5=fc_1266 || a_1261___5___=a_1252___5___)  && (5=fc_1266 || a_1261___5___=a_1252___5___) && (5=fc_1266 || a_1261___5___=a_1252___5___) && Q(a_1261___4___,a_1261___5___,a_1261,PRIa___4___,PRIa___5___,PRIa,res))) )) ))  && fc_a_1265=1+a_1252___4___))

        &&  (exists (v_int_14_1233:v_int_14_1233=a___5___-(1) && a_1252___5___=v_int_14_1233 && (a_1252___4___=a___4___)  && (a_1252___4___=a___4___)  && (a_1252___4___=a___4___) )) ))  )) ))

&& fc_1266=4))

&& fc_1267=5))

&& 1<=a___5___)
};
bottomupgen([Q], [2], SimHeur);

output from fixcalc:
((res >= 1 + a___4___ && res = PRIa___4___ && 0 = PRIa___5___ && res = a___5___ + a___4___) || (0 >= a___5___ && res = PRIa___4___ && res = a___4___ && a___5___ = PRIa___5___ && PRIa = a))


I think the 2nd relation assumption contains extra ctr that need not be there.

Q:={[a___4___,a___5___,a] -> [PRIa___4___,PRIa___5___,PRIa,res] -> []: (a___4___=res && PRIa___4___=res && PRIa=a && a___5___=PRIa___5___ && PRIa___5___<=0 ||  (exists (fc_1267: (exists (fc_1266: (exists (a_1252___i___: (exists (a_1252___5___: (exists (a_1252___4___: (exists (a_1252___i___: (exists (a_1252: (exists (fc_a_1265: (exists (a_1261___4___: (exists (a_1261___5___: (exists (a_1261___i___: (exists (a_1261___4___: (exists (a_1261:a_1261___4___=fc_a_1265 && (4=fc_1266 || a_1261___4___=a_1252___4___) && (4=fc_1266 || a_1261___4___=a_1252___4___) && (5=fc_1266 || a_1261___5___=a_1252___5___) && (4=fc_1266 || a_1261___4___=a_1252___4___) && (5=fc_1266 || a_1261___5___=a_1252___5___) && (4=fc_1266 || a_1261___4___=a_1252___4___) && (5=fc_1266 || a_1261___5___=a_1252___5___) && Q(a_1261___4___,a_1261___5___,a_1261,PRIa___4___,PRIa___5___,PRIa,res))) )) )) )) ))  && fc_a_1265=1+a_1252___4___))  &&  (exists (v_int_14_1233:v_int_14_1233=a___5___-(1) && a_1252___5___=v_int_14_1233 && (4=fc_1267 || a_1252___4___=a___4___) && (5=fc_1267 || a_1252___5___=a___5___) && (4=fc_1267 || a_1252___4___=a___4___) && (5=fc_1267 || a_1252___5___=a___5___) && (4=fc_1267 || a_1252___4___=a___4___) && (5=fc_1267 || a_1252___5___=a___5___))) )) )) )) )) ))  && fc_1266=4))  && fc_1267=5))  && 1<=a___5___)
};
bottomupgen([Q], [2], SimHeur);

foo$int[]
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume ref [a]
           emp&((res>=(1+(a[4])) & res=a'[4] & 0=a'[5] & res=(a[5])+
           (a[4])) | (0>=(a[5]) & res=a'[4] & res=a[4] & a[5]=a'[5] & a=a'))&
           {FLOW,(4,5)=__norm#E}[]
((res>=(1+(a[4])) & res=a'[4] & 0=a'[5] & res=(a[5])+(a[4])) | (0>=(a[5]) & res=a'[4] & res=a[4] & a[5]=a'[5] & a=a'))

one branch implies a[5]>=1

*/
