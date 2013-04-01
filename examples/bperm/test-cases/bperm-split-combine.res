Starting z3... 

Entail (1) : Valid. 

 <1>emp&true&{FLOW,(19,20)=__norm}[]


Entail (2) : Valid. 

 <1>EXISTS(bperm_12_220,bperm_12_219,bperm_12_218: emp&bperm_12_220=1 & bperm_12_219=2 & bperm_12_218=1&{FLOW,(19,20)=__norm})[]


Entail (3) : Valid. 

 <1>EXISTS(bperm_16_282: emp&bperm_16_282=0 & c1=c2&{FLOW,(19,20)=__norm})[]


Entail (4) : Valid. 

 <1>EXISTS(bperm_20_379,bperm_5_404,bperm_5_403: x::cell( (c2_387,bperm_20_379,bperm_5_403))<v1>[Orig]&bperm_5_404=0 & bperm_5_403=0 & 0<bperm_3_364 & bperm_3_364<=bperm_20_379 & bperm_3_364=c2_349+2 & bperm_3_363=0 & bperm_20_379=5 & c2_349=3 & t_15=5 & bperm_3_13=0 & v1=v_16 & v1=v2 & c2_387<bperm_20_379 & 0<c2_387 & bperm_20_379=5 & bperm_3_364=c2_387+1 & 0<1 & 1<bperm_20_379&{FLOW,(19,20)=__norm})[]


Entail (5) : Valid. 

 <1>EXISTS(bperm_24_475,bperm_5_500,bperm_5_499: x::cell( (c2_483,bperm_24_475,bperm_5_499))<v1>[Orig]&bperm_5_500=0 & bperm_5_499=0 & 0<bperm_3_460 & bperm_3_460<=bperm_24_475 & bperm_3_460=c2_445+2 & bperm_3_459=0 & bperm_24_475=5 & c2_445=3 & t_15=5 & bperm_3_13=0 & v1=v_16 & v1=v2 & c2_483<bperm_24_475 & 0<c2_483 & bperm_24_475=5 & bperm_3_460=c2_483+4 & 0<4 & 4<bperm_24_475&{FLOW,(19,20)=__norm})[]


Entail (6) : Valid. 

 <1>EXISTS(bperm_28_586,bperm_5_617,bperm_5_616: emp&bperm_5_617=0 & bperm_5_616=0 & 0<bperm_3_571 & bperm_3_571<=bperm_28_586 & bperm_3_571=c2_556+2 & bperm_3_570=0 & bperm_28_586=5 & c2_556=3 & t_15=5 & bperm_3_13=0 & v1=v_16&{FLOW,(19,20)=__norm})[]

Stop z3... 42 invocations 
SAT Count   : 12
SAT % Hit   : 58.33%
IMPLY Count : 62
IMPLY % Hit : 40.32%
Time(cache overhead) : 0. (seconds)

Total verification time: 0.14 second(s)
	Time spent in main process: 0.13 second(s)
	Time spent in child processes: 0.01 second(s)

