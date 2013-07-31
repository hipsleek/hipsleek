function two 
{
 cp tests/slk/$1.out ref/slk/$1.out
}
mkdir -p ref/slk
two lab1.slk --dump-proof
two lab2.slk --dump-proof
two lab3.slk --dump-proof
two lab4.slk --dump-proof
two test-3a.slk --dump-proof
two test-3b.slk --dump-proof
two test-3c.slk --dump-proof
two test-3d.slk --dump-proof
two test-3e.slk --dump-proof
two test-3f.slk --dump-proof
two test-3g.slk --dump-proof
two test-3h.slk --dump-proof
two test-3i.slk --dump-proof


