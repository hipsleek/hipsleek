
function tmp_cp
{
 cp ref/slk/$1.out ref/tmp/$1.out
}

function keep_tmp
{
tmp_cp cll-1b.slk
tmp_cp dll-append2.slk
tmp_cp dll-pap-1.slk
tmp_cp dll-pap-2.slk
tmp_cp pre-2a.slk
tmp_cp tll-if.slk
tmp_cp tree-1.slk
tmp_cp zip1b1.slk
tmp_cp zip1b2.slk
tmp_cp zip1b3.slk
tmp_cp zip1b4.slk
tmp_cp zip1b5.slk
tmp_cp zip1b.slk
tmp_cp zip1c1.slk
tmp_cp zip1c2.slk
tmp_cp zip1c.slk
tmp_cp zip1d.slk
tmp_cp zip1e.slk
tmp_cp zip1f.slk
tmp_cp zip1.slk
tmp_cp zip1z.slk
tmp_cp zip-bug1a.slk
tmp_cp zip-bug1b.slk
tmp_cp zip-bug1c.slk
tmp_cp zip-bug1.slk
tmp_cp zip-bug2.slk
tmp_cp zip-bug3.slk
tmp_cp zip-bug4.slk
tmp_cp zip-bug5a.slk
tmp_cp zip-bug5b.slk
tmp_cp zip-bug5c.slk
tmp_cp zip-bug5.slk
tmp_cp zip.slk
}

rm ref/tmp/*.out
keep_tmp
./override_slk.sh
cp ref/tmp/*.out ref/slk