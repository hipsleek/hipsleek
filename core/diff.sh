# compare expected outcomes (*.res) with new outcomes
echo "======= ptr-byptr.ss ======"
diff test/ptr-byptr.res test/ptr-byptr.n
echo "======= ptr-byval.ss ======"
diff test/ptr-byval.res test/ptr-byval.n
echo "======= ptr-byref.ss ======"
diff test/ptr-byref.res test/ptr-byref.n
echo "======= ptr-globalptr.ss ======"
diff test/ptr-globalptr.res test/ptr-globalptr.n
echo "======= ptr-global.ss ======"
diff test/ptr-global.res test/ptr-global.n
echo "======= ptr-local.ss ======"
diff test/ptr-local.res test/ptr-local.n
echo "======= ptr-ifthenelse.ss ======"
diff test/ptr-ifthenelse.res test/ptr-ifthenelse.n
echo "======= ptr-while.ss ======"
diff test/ptr-while.res test/ptr-while.n
echo "======= address-of-var.ss ======"
diff test/address-of-var.res test/address-of-var.n
echo "======= ptr-of-ptr.ss ======"
diff test/ptr-of-ptr.res test/ptr-of-ptr.n
echo "======= ptr-proc.ss ======"
diff test/ptr-proc.res test/ptr-proc.n
echo "======= ptr-proc-fork.ss ======"
diff test/ptr-proc-fork.res test/ptr-proc-fork.n
echo "======= while-w-heap.ss ======"
diff test/while-w-heap.res test/while-w-heap.n
echo "======= ptr-while-addr.ss ======"
diff test/ptr-while-addr.res test/ptr-while-addr.n
echo "======= ptr-ref1.ss ======"
diff test/ptr-ref1.res test/ptr-ref1.n
echo "======= ptr-ref2.ss ======"
diff test/ptr-ref2.res test/ptr-ref2.n
echo "======= ptr-ref3.ss ======"
diff test/ptr-ref3.res test/ptr-ref3.n
echo "======= ptr-ref4.ss ======"
diff test/ptr-ref4.res test/ptr-ref4.n
echo "======= ptr-ref5.ss ======"
diff test/ptr-ref5.res test/ptr-ref5.n
