H  : forall A, length A [] = 0
H1 : forall A x xs,
       length A (x::xs) = length A xs + 1
-----------------------------
length nat [1; 2; 3] = 3
