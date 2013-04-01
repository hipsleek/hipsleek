Starting z3... 

Entail (1) : Valid. 

 <1>EXISTS(bperm_9_113,bperm_9_112,bperm_9_111,Anon_138,bperm_3_137,bperm_3_136: x::cell( (c2_121,bperm_9_112,bperm_3_136))<Anon_138>[Orig]&bperm_3_137=0 & bperm_3_136=0 & 0<bperm_9_113 & bperm_9_113<=bperm_9_112 & bperm_9_113=2 & bperm_9_112=2 & bperm_9_111=0 & Anon_12=Anon_13 & c2_121<bperm_9_112 & 0<c2_121 & bperm_9_112=2 & bperm_9_113=c2_121+1 & 0<1 & 1<bperm_9_112&{FLOW,(19,20)=__norm})[]


Entail (2) : Valid. 

 <1>EXISTS(bperm_13_179,bperm_13_178,bperm_13_177,bperm_3_206,bperm_3_205: emp&bperm_3_206=0 & bperm_3_205=0 & 0<bperm_13_179 & bperm_13_179<=bperm_13_178 & bperm_13_179=2 & bperm_13_178=2 & bperm_13_177=0 & Anon_14=Anon_15&{FLOW,(19,20)=__norm})[]


Entail (3) : Fail.


Entail (4) : Valid. 

 <1>EXISTS(c2_378,bperm_21_367,bperm_21_366,bperm_21_365,bperm_3_394,bperm_3_393,Anon_420,bperm_3_419,bperm_3_418: x::cell( (c2_403,bperm_21_366,bperm_3_418))<Anon_420>[Orig]&bperm_3_419=0 & bperm_3_418=0 & 0<c2_378 & c2_378<=bperm_21_366 & bperm_3_394=0 & bperm_3_393=0 & 0<bperm_21_367 & bperm_21_367<=bperm_21_366 & bperm_21_367=3 & bperm_21_366=3 & bperm_21_365=0 & Anon_20=Anon_21 & c2_403<bperm_21_366 & 0<c2_403 & bperm_21_366=3 & bperm_21_366=3 & 1<bperm_21_366 & 0<1 & 1<bperm_21_366 & 0<(c2_403+1) & (c2_403+1)<bperm_21_366 & bperm_21_367=c2_403+1+1&{FLOW,(19,20)=__norm})[]


Entail (5) : Valid. 

 <1>EXISTS(c2_486,bperm_25_472,bperm_25_471,bperm_25_470,bperm_3_502,bperm_3_501,bperm_3_527,bperm_3_526: emp&bperm_3_527=0 & bperm_3_526=0 & 0<c2_486 & c2_486<=bperm_25_471 & bperm_3_502=0 & bperm_3_501=0 & 0<bperm_25_472 & bperm_25_472<=bperm_25_471 & bperm_25_472=3 & bperm_25_471=3 & bperm_25_470=0 & Anon_23=Anon_24&{FLOW,(19,20)=__norm})[]


Entail (6) : Fail.


Entail (7) : Valid. 

 <1>EXISTS(bperm_33_727,bperm_33_726,bperm_33_725,bperm_3_754,bperm_3_753: emp&bperm_3_754=0 & bperm_3_753=0 & 0<bperm_33_727 & bperm_33_727<=bperm_33_726 & bperm_33_727=2 & bperm_33_726=3 & bperm_33_725=0 & Anon_31=Anon_32&{FLOW,(19,20)=__norm})[]

Stop z3... 32 invocations 
SAT Count   : 7
SAT % Hit   : 57.14%
IMPLY Count : 63
IMPLY % Hit : 53.96%
Time(cache overhead) : 0.01 (seconds)

Total verification time: 0.17 second(s)
	Time spent in main process: 0.16 second(s)
	Time spent in child processes: 0.01 second(s)

