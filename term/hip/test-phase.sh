../../hip infer-1.ss > p1.inf
../../hip infer-2.ss > p2.inf
../../hip infer-3.ss > p3.inf
../../hip infer-4.ss > p4.inf
../../hip infer-6a.ss > p6a.inf
../../hip infer-6b.ss > p6b.inf
../../hip infer-gcd-1.ss > p-gcd-1.inf
../../hip infer-gcd-2.ss > p-gcd-2.inf
../../hip infer-mutual-1.ss > p-mutual-1.inf
../../hip infer-no-1.ss > p1.no
../../hip infer-no-2.ss > p2.no
../../hip infer-no-3.ss > p3.no
../../hip infer-no-4.ss > p4.no
../../hip infer-no-6a.ss > p6a.no
../../hip infer-no-6b.ss > p6b.no
../../hip infer-no-gcd-1.ss > p-gcd-1.no
../../hip infer-no-gcd-2.ss > p-gcd-2.no
../../hip infer-no-mutual-1.ss > p-mutual-1.no
echo "======= infer-1.ss infer-no-1.ss ======"
diff p1.inf p1.no
echo "======= infer-2.ss infer-no-2.ss ======"
diff p2.inf p2.no
echo "======= infer-3.ss infer-no-3.ss ======"
diff p3.inf p3.no
echo "======= infer-4.ss infer-no-4.ss ======"
diff p4.inf p4.no
echo "======= infer-6a.ss infer-no-6a.ss ======"
diff p6a.inf p6a.no
echo "======= infer-6b.ss infer-no-6b.ss ======"
diff p6b.inf p6b.no
echo "======= infer-gcd-1.ss infer-no-gcd-1.ss ======"
diff p-gcd-1.inf p-gcd-1.no
echo "======= infer-gcd-2.ss infer-no-gcd-2.ss ======"
diff p-gcd-2.inf p-gcd-2.no
echo "======= infer-mutual-1.ss infer-no-mutual-1.ss ======"
diff p-mutual-1.inf p-mutual-1.no






