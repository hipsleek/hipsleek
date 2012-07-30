Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Eliminating variable aliasing...
Eliminating pointers...PASSED 

Checking procedure inc$lock~cell... 
dprint: cell4.ss:70: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:l::LOCK(f)<x>@M[Orig][LHSCase]&Anon_full_perm=FLOAT 1. & l'=l & x'=x & MayLoop&{FLOW,(20,21)=__norm}[]

 ]

dprint: cell4.ss:72: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:EXISTS(v_667: x'::cell()<l',v_667>@M[Orig] * l'::LOCK(f_665)<x>@M[Derv]&Anon_full_perm=FLOAT 1. & l'=l & x'=x & f_665=f & l!=null & 0<=v_667&{FLOW,(20,21)=__norm})[]
       es_var_measures: MayLoop

 ]

dprint: cell4.ss:75: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:EXISTS(v_int_73_718: l'::LOCK(f_665)<x>@M[Orig] * x'::cell(f_707)<l',v_int_73_718>@M[Orig]&Anon_full_perm=FLOAT 1. & l'=l & x'=x & f_665=f & l!=null & 0<=v_681 & f_680=Anon_full_perm & f_680>FLOAT 0. & f_680<=FLOAT 1. & f_691=f_680 & f_691>FLOAT 0. & f_691<=FLOAT 1. & v_int_73_718=1+v_681 & f_707=f_691 & f_707=FLOAT 1.&{FLOW,(20,21)=__norm})[]
       es_var_measures: MayLoop

 ]

dprint: cell4.ss:77: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:l'::LOCK(f_721)<x>@M[Orig]&Anon_full_perm=FLOAT 1. & l'=l & x'=x & f_665=f & l!=null & 0<=v_681 & f_680=Anon_full_perm & f_680>FLOAT 0. & f_680<=FLOAT 1. & f_691=f_680 & f_691>FLOAT 0. & f_691<=FLOAT 1. & v_int_73_723=1+v_681 & f_707=f_691 & f_707=FLOAT 1. & f_721=f_665 & v_722=v_int_73_723 & x'!=null & l'!=null&{FLOW,(20,21)=__norm}[]
       es_var_measures: MayLoop

 ]

Procedure inc$lock~cell SUCCESS

Checking procedure main$... 
dprint: cell4.ss:47: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:l_24'::LOCK(f_765)<x_25>@M[Orig]&Anon_full_perm=FLOAT 1. & v_int_40_755=0 & f_765=Anon_full_perm & v_766=v_int_40_755 & x_25'!=null & l_24'!=null&{FLOW,(20,21)=__norm}[]
       es_var_measures: MayLoop

 ]

dprint: cell4.ss:49: ctx:  List of Failesc Context: [FEC(0, 0, 1  ) FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:true&x_25'=x_801 & l_24'=l_800 & Anon_full_perm=FLOAT 1. & v_int_40_755=0 & f_765=Anon_full_perm & v_766=v_int_40_755 & x_801!=null & l_800!=null & x_801=x_25 & f=f_765 & id_26'=tid_778&{FLOW,(20,21)=__norm}
AND  <thread=tid_778>  <ref:> l_800::LOCK(f)<x_801>@M[Orig][LHSCase]&l_800!=null
       es_var_measures: MayLoop

 ],

Successful States:
[
 Label: 
 State:l_802::LOCK(f2_790)<x_25>@M[Derv]&x_25'=x_803 & l_24'=l_802 & FLOAT 0.<f_765 & f_765<=FLOAT 1. & Anon_full_perm=FLOAT 1. & v_int_40_755=0 & f_765=Anon_full_perm & v_766=v_int_40_755 & x_803!=null & l_802!=null & x_803=x_25 & FLOAT 0.<f2_790 & FLOAT 0.<(f_765-f2_790) & f_765=f2_790+f & FLOAT 0.<f & FLOAT 0.<f2_790 & id_26'=tid_778&{FLOW,(20,21)=__norm}
AND  <thread=tid_778>  <ref:> l_802::LOCK(f)<x_803>@M[Orig][LHSCase]&l_802!=null
       es_var_measures: MayLoop

 ]

dprint: cell4.ss:53: ctx:  List of Failesc Context: [FEC(0, 0, 1  )]

Successful States:
[
 Label: 
 State:EXISTS(v_int_52_861: l_24'::LOCK(f_808)<x_25>@M[Orig] * x_25'::cell(f_850)<l_24',v_int_52_861>@M[Orig]&x_25'=x_803 & l_24'=l_802 & FLOAT 0.<f_765 & f_765<=FLOAT 1. & Anon_full_perm=FLOAT 1. & v_int_40_755=0 & f_765=Anon_full_perm & v_766=v_int_40_755 & x_803!=null & x_803=x_25 & FLOAT 0.<(f_765-f2_790) & f_765=f2_790+f & FLOAT 0.<f & FLOAT 0.<f2_790 & id_26'=tid_778 & f_808=f2_790 & l_802!=null & 0<=v_824 & f_823=Anon_full_perm & f_823>FLOAT 0. & f_823<=FLOAT 1. & f_834=f_823 & f_834>FLOAT 0. & f_834<=FLOAT 1. & v_int_52_861=1+v_824 & f_850=f_834 & f_850=FLOAT 1.&{FLOW,(20,21)=__norm})
AND  <thread=tid_778>  <ref:> l_802::LOCK(f)<x_803>@M[Orig][LHSCase]&l_802!=null
       es_var_measures: MayLoop

 ]

Procedure main$ SUCCESS
Halting Reduce... 
Stop Omega... 34 invocations 
0 false contexts at: ()

Total verification time: 0.9 second(s)
	Time spent in main process: 0.47 second(s)
	Time spent in child processes: 0.43 second(s)
