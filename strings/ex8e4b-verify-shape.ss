
data str {
  int val;
  str next;
}

DDD<> == self::EEE<> inv true;

EEE<> == self::str<_,_> inv true;

/*
# ex8e4.slk -dre "incr_fixpt_view"

# bug with proc below..

(==iast.ml#2186==)
syn_data_name@2@1
syn_data_name inp1 :[WAITS:@,WAIT:@,memLoc:@,EEE:@,DDD:@]
syn_data_name@2 EXIT:[(WAITS:@,[],[]),(WAIT:@,[],[]),(memLoc:@,[],[]),(EEE:@,[str],[]),(DDD:@,[],[EEE])]

(==iast.ml#2187==)
fixpt_data_name@3@1
fixpt_data_name inp1 :[(WAITS:@,[],[]),(WAIT:@,[],[]),(memLoc:@,[],[]),(EEE:@,[str],[]),(DDD:@,[],[EEE])]
fixpt_data_name@3 EXIT:[(WAITS:@,[],[]),(WAIT:@,[],[]),(memLoc:@,[],[]),(EEE:@,[str],[]),(DDD:@,[str],[EEE])]

(==iast.ml#2190==)
update_fixpt@4@1
update_fixpt inp1 :[(WAITS:@,[],[]),(WAIT:@,[],[]),(memLoc:@,[],[]),(EEE:@,[str],[]),(DDD:@,[str],[EEE])]
update_fixpt res1 :[(WAITS:WAITS@,[],[]),(WAIT:WAIT@,[],[]),(memLoc:memLoc@,[],[]),(EEE:str@,[str],[]),(DDD:str@,[str],[EEE])]
update_fixpt@4 EXIT:()

(==astsimp.ml#9550==)
set_check_fixpt@1
set_check_fixpt inp1 :?
set_check_fixpt inp2 :[WAITS:@,WAIT:@,memLoc:@,EEE:@,DDD:@]
set_check_fixpt res2 :[WAITS:WAITS@,WAIT:WAIT@,memLoc:memLoc@,EEE:str@,DDD:str@]
set_check_fixpt@1 EXIT:()

*/


