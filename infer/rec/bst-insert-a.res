
Processing file "bst-insert-a.ss"
Parsing bst-insert-a.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node2~int... 
!!! REL :  C(mi,sm,ma,lg,a)
!!! POST:  sm>=mi & lg>=sm & ma>=lg & a>=mi & ma>=a
!!! PRE :  sm<=lg
!!! NEW RELS:[ (lg=ma & mi=a & a<=sm & sm<=ma | ma=a & sm=mi & mi<=lg & (1+lg)<=a | 
  lg=ma & sm=mi & (1+mi)<=a & a<=ma) --> C(mi,sm,ma,lg,a),
 (C(mi_649,sm_621,ma_650,lg_622,a) & ma=lg & mi=mi_649 & sm_621=sm & 
  mi_649<=ma_650 & sm<=lg_622 & exists(v_606:exists(qs_605:a<=v_606 & 
  qs_605<=lg & lg_622<=v_606 & v_606<=qs_605))) --> C(mi,sm,ma,lg,a),
 (C(mi_684,sm_656,ma_685,lg_657,a) & ma=ma_685 & mi=sm & lg_657=lg & 
  mi_684<=ma_685 & sm_656<=lg & exists(v_606:exists(pl_604:sm<=pl_604 & (1+
  v_606)<=a & pl_604<=v_606 & v_606<=sm_656))) --> C(mi,sm,ma,lg,a)]
!!! NEW ASSUME:[ RELASS [C]: ( C(mi_649,sm_621,ma_650,lg_622,a)) -->  lg_622<sm_621 | sm_621<=lg_622 & ma_650<=lg_622 | sm_621<=lg_622 & 
lg_622<ma_650 & ma_650<mi_649 | sm_621<=lg_622 & lg_622<ma_650 & ma_650<=a & 
mi_649<=ma_650,
 RELASS [C]: ( C(mi_684,sm_656,ma_685,lg_657,a)) -->  sm_656<=mi_684 | ma_685<mi_684 & mi_684<sm_656 | mi_684<=(sm_656-1) & 
mi_684<=ma_685 & lg_657<sm_656 | (a-1)<=mi_684 & mi_684<sm_656 & 
sm_656<=lg_657 & mi_684<=ma_685]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 236 invocations 
0 false contexts at: ()

Total verification time: 1.344083 second(s)
	Time spent in main process: 0.100006 second(s)
	Time spent in child processes: 1.244077 second(s)
