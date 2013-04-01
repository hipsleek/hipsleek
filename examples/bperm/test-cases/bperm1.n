Starting z3... 

Entail (1) : Valid. 

 <1>EXISTS(bperm_4_58,bperm_4_57,bperm_4_56: emp&bperm_4_58=3 & bperm_4_57=2 & bperm_4_56=1 & b=null & Anon_11=Anon_12&{FLOW,(19,20)=__norm})[]


Entail (2) : Fail.


Entail (3) : Valid. 

 <1>EXISTS(bperm_14_130,bperm_14_129,bperm_14_128: emp&bperm_14_130=1 & bperm_14_129=2 & bperm_14_128=1 & b=null & Anon_15=Anon_16&{FLOW,(19,20)=__norm})[]


Entail (4) : Valid. 

 <1>emp&c=1 & t=2 & a=1 & b=null & Anon_17=Anon_18&{FLOW,(19,20)=__norm}[]


Entail (5) : Valid. 

 <1>EXISTS(flted_25_173: x::node( (c,t,a))<Anon_19,flted_25_173>[Orig]&flted_25_173=null&{FLOW,(19,20)=__norm})[]


Entail (6) : Valid. 

 <1>emp&c=1 & t=2 & a=1 & b=null & Anon_20=Anon_21&{FLOW,(19,20)=__norm}[]


Entail (7) : Valid. 

 <1>EXISTS(bperm_35_222: emp&bperm_35_222=1 & t=2 & a=1 & b=null & Anon_22=Anon_23&{FLOW,(19,20)=__norm})[]


Entail (8) : Fail.

Stop z3... 15 invocations 
SAT Count   : 8
SAT % Hit   : 62.5%
IMPLY Count : 15
IMPLY % Hit : 20.%
Time(cache overhead) : 0. (seconds)

Total verification time: 0.07 second(s)
	Time spent in main process: 0.06 second(s)
	Time spent in child processes: 0.01 second(s)

